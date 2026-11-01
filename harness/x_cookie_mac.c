// SPDX-License-Identifier: GPL-2.0
// Law `cookie_mac`: mac1/mac2 creation (wg_cookie_add_mac_to_packet) and validation (wg_cookie_validate_packet)
// against the model, on ANY message and ANY cookie state.
//
// Responder device B with ANY static key (its cookie checker keys precomputed; its cookie secret and the secret's
// birthdate ANY); a peer P of another device whose public key is B's (honest) or ANY; P's cookie state ANY
// (valid or not, any birthdate, any cookie, any last mac1) or, in one mode, the cookie B would make for the
// packet's source; a message of ANY length >= 32 (its last 32 bytes are mac1 || mac2; exact-size buffer) with ANY
// content; ANY boot clock; the packet's protocol IPv4, IPv6 or other, ANY source address and port; the rate
// limiter's answer ANY; check_cookie ANY.
// Claims:
//  - the checker's keys are HASH("mac1----" || S_pub) and HASH("cookie--" || S_pub) (zero without identity);
//    the peer's are the same for its public key; wg_cookie_checker_init gives the checker a fresh
//    random secret (the shim's draw) born now;
//  - add_mac writes mac1 = MAC(mac1 key, m[0..len-32)), and mac2 = MAC(cookie, m[0..len-16)) if the cookie is
//    valid and younger than 115 s (COOKIE_SECRET_MAX_AGE - COOKIE_SECRET_LATENCY: birthdate + 115 s > now,
//    signed), else 16 zero bytes; nothing else of the message; the peer remembers mac1 (last_mac1_sent,
//    have_sent_mac1) and nothing else of its cookie state changes;
//  - validate returns exactly the model's verdict: INVALID_MAC if mac1 is not MAC(checker mac1 key, ...);
//    VALID_MAC_BUT_NO_COOKIE if !check_cookie or mac2 does not match the cookie of the packet's source;
//    VALID_MAC_WITH_COOKIE_BUT_RATELIMITED if the rate limiter refuses; else VALID_MAC_WITH_COOKIE.  The cookie
//    is MAC32(secret, source address (4 bytes for IPv4, 16 for IPv6, none otherwise) || source port), and the
//    secret is replaced by fresh random bytes (birthdate now) when it is 120 s old, exactly as cookie.c decides it
//    (wg_birthdate_has_expired: (s64)(birthdate + 120 s) <= (s64)now): at EXACTLY 120 s the secret is new, so a
//    mac2 made with the old one fails (wireguard-go rotates only after 120 s); the harness draws the clock at
//    120 s +- 2 ns and 115 s +- 2 ns on purpose;
//  - validate modifies neither the message nor the packet; the checker only by that rotation;
//  - (whole-state frame; P has ANY handshake state, dead flag, last sent handshake, reference count
//    below INT_MAX, its handshake entry in A's index table or not, and ANY keypairs - whole objects of any content -
//    in that table and possibly in its slots) add_mac changes nothing of the peer but those two cookie fields
//    (handshake, reference count, keypair slots and every byte of the keypairs, ... unchanged), neither device and
//    not A's index table; validate changes nothing of either device but that rotation (identity, both checker keys,
//    the checker's device, tables) nor the peer (its keypairs and A's index table included), and leaves every field
//    of the packet as it was (data, length, protocol, source address and port); neither allocates nor makes a
//    reference count warn;
//  - round trips: a message with macs added by a peer that has B's public key has a valid mac1 at B; if the peer
//    also holds B's current cookie for the packet's source (fresh), mac2 is valid too.
#include "common.h"

// B's cookie for the packet's source with secret `secret` (make_cookie)
static void m_cookie(u8 out[16], const u8 secret[32], const struct sk_buff *skb)
{
	u8 buf[18];
	size_t n = 0;
	if (skb->protocol == htons(ETH_P_IP)) {
		bytes_copy(buf, skb->ip4.saddr.s_addr, 4);
		n = 4;
	} else if (skb->protocol == htons(ETH_P_IPV6)) {
		bytes_copy(buf, skb->ip6.saddr.s6_addr, 16);
		n = 16;
	}
	bytes_copy(buf + n, skb->udp.source, 2);
	m_mac(out, secret, 32, buf, n + 2);
}

// wg_birthdate_has_expired(birthdate, seconds), as the model states it
static int m_expired(u64 birthdate, u64 seconds, u64 now)
{
	return (s64)(birthdate + seconds * 1000000000ULL) <= (s64)now;
}

int main(void)
{
	struct wg_device wa, wb;
	struct index_hashtable ita, itb;
	struct pubkey_hashtable pta, ptb;
	struct wg_peer p;
	struct m_identity ib;
	struct ck_snap cs;
	struct hs_snap hs0;
	struct pr_snap ps0;
	struct dev_snap da, db;
	struct skb_snap sks;
	struct shim_snap ss;
	struct kent *kes;
	struct index_hashtable_entry *head0;
	unsigned int refs0;
	struct sk_buff skb;
	u8 raw_a[32], raw_b[32], pub[32], k[32], mac1[16], mac2[16], cookie[16], secret[32];
	u8 *msg, *copy;
	size_t len;
	u64 now, secret_birth;
	int honest_peer, check_cookie, verdict, cookie_mode, corrupted = 0;
	enum cookie_mac_state r;

	wg_shim_boottime_ns = draw_boottime();
	wg_noise_init();
	nondet_bytes(raw_a, 32);
	nondet_bytes(raw_b, 32);
	setup_device(&wa, &ita, &pta, raw_a);
	setup_device(&wb, &itb, &ptb, raw_b);
	// wg_cookie_checker_init: a fresh random secret (the last draw), born now
	CHECK(bytes_eq(wb.cookie_checker.secret, wg_shim_random_log, 32) &&
	      wb.cookie_checker.secret_birthdate == wg_shim_boottime_ns);
	m_identity_of(&ib, raw_b);
	// the checker's keys
	if (ib.ok) {
		m_label_key(k, M_LABEL_MAC1, wb.static_identity.static_public);
		CHECK(bytes_eq(wb.cookie_checker.message_mac1_key, k, 32));
		m_label_key(k, M_LABEL_COOKIE, wb.static_identity.static_public);
		CHECK(bytes_eq(wb.cookie_checker.cookie_encryption_key, k, 32));
	} else {
		CHECK(bytes_zero(wb.cookie_checker.message_mac1_key, 32) &&
		      bytes_zero(wb.cookie_checker.cookie_encryption_key, 32));
	}
	CHECK(wb.cookie_checker.device == &wb);
	// B's cookie secret: any value and age
	nondet_bytes(wb.cookie_checker.secret, 32);
	wb.cookie_checker.secret_birthdate = draw_boottime();

	honest_peer = nondet_u8() % 4 != 0;
	if (honest_peer)
		bytes_copy(pub, wb.static_identity.static_public, 32);
	else
		nondet_bytes(pub, 32);
	setup_peer(&p, &wa, pub, NULL, 1);
	m_label_key(k, M_LABEL_MAC1, pub);
	CHECK(bytes_eq(p.latest_cookie.message_mac1_key, k, 32));
	m_label_key(k, M_LABEL_COOKIE, pub);
	CHECK(bytes_eq(p.latest_cookie.cookie_decryption_key, k, 32));
	// ANY other state of P (handshake, dead flag, last sent handshake, reference count below INT_MAX), its
	// handshake entry in A's index table or not, and ANY keypairs of P (in A's table, possibly in P's slots)
	hs_randomize(&p.handshake);
	p.is_dead = nondet_u8() & 1;
	p.last_sent_handshake.counter = (s64)draw_u64();
	p.refcount.refcount = draw_peer_refs();
	if (nondet_u8() & 1)
		wg_index_hashtable_insert(&ita, &p.handshake.entry);
	kes = kents_add(&ita, NULL, &p, 1);
	kents_snap(kes);
	head0 = ita.head;

	// the packet
	len = draw_size();
	if (len > SIZE_MAX - 32 || len + 32 > 0xffffffffu)
		return 0;   // skb->len is an unsigned int
	len += 32;
	msg = malloc(len);
	copy = malloc(len);
	if (msg == NULL || copy == NULL) {
		free(msg);
		free(copy);
		return 0;
	}
	nondet_bytes(msg, len);
	skb.data = msg;
	skb.len = (unsigned int)len;
	switch (nondet_u8() % 3) {
	case 0: skb.protocol = htons(ETH_P_IP); break;
	case 1: skb.protocol = htons(ETH_P_IPV6); break;
	default: skb.protocol = (__be16)nondet_u32(); break;
	}
	nondet_bytes(skb.ip4.saddr.s_addr, 4);
	nondet_bytes(skb.ip6.saddr.s6_addr, 16);
	nondet_bytes(skb.udp.source, 2);
	now = draw_boottime();
	if (nondet_u8() % 4 == 0) {
		// the edges of the secret's lifetime (120 s) and of a cookie's (115 s)
		u64 edge = wb.cookie_checker.secret_birthdate + (nondet_u8() & 1 ? 120 : 115) * 1000000000ULL - 2 +
			   nondet_u8() % 5;
		if (edge < (1ULL << 62))
			now = edge;
	}
	wg_shim_boottime_ns = now;

	// P's cookie state: any, or B's current cookie for this source (fresh)
	p.latest_cookie.is_valid = nondet_u8() & 1;
	p.latest_cookie.birthdate = draw_boottime();
	if (nondet_u8() % 4 == 0 && now >= 115000000002ULL)
		p.latest_cookie.birthdate = now - 115000000000ULL - 2 + nondet_u8() % 5;   // the cookie's 115 s edge
	nondet_bytes(p.latest_cookie.cookie, 16);
	p.latest_cookie.have_sent_mac1 = nondet_u8() & 1;
	nondet_bytes(p.latest_cookie.last_mac1_sent, 16);
	cookie_mode = nondet_u8() & 1;
	if (cookie_mode) {
		if (m_expired(wb.cookie_checker.secret_birthdate, 120, now))
			wb.cookie_checker.secret_birthdate = now;
		m_cookie(p.latest_cookie.cookie, wb.cookie_checker.secret, &skb);
		p.latest_cookie.is_valid = true;
		p.latest_cookie.birthdate = now;
	}

	// ---- add_mac ----
	ck_take(&cs, &p.latest_cookie);
	hs_take(&hs0, &p.handshake);
	pr_take(&ps0, &p);
	refs0 = p.refcount.refcount;
	dev_take(&da, &wa);
	dev_take(&db, &wb);
	shim_take(&ss);
	bytes_copy(copy, msg, len);
	wg_cookie_add_mac_to_packet(msg, len, &p);
	m_mac(mac1, p.latest_cookie.message_mac1_key, 32, copy, len - 32);
	bytes_copy(copy + len - 32, mac1, 16);
	if (cs.is_valid && !m_expired(cs.birthdate, 115, now))
		m_mac(mac2, cs.cookie, 16, copy, len - 16);
	else
		bytes_set(mac2, 0, 16);
	bytes_copy(copy + len - 16, mac2, 16);
	CHECK(bytes_eq(msg, copy, len));
	CHECK(p.latest_cookie.have_sent_mac1 && bytes_eq(p.latest_cookie.last_mac1_sent, mac1, 16));
	CHECK(p.latest_cookie.birthdate == cs.birthdate && p.latest_cookie.is_valid == cs.is_valid &&
	      bytes_eq(p.latest_cookie.cookie, cs.cookie, 16) &&
	      bytes_eq(p.latest_cookie.cookie_decryption_key, cs.cookie_decryption_key, 32) &&
	      bytes_eq(p.latest_cookie.message_mac1_key, cs.message_mac1_key, 32));
	// nothing else of the peer, neither device, no allocation
	CHECK(hs_same(&hs0, &p.handshake) && pr_same_but_cookie(&ps0, &p) && p.refcount.refcount == refs0 &&
	      dev_same(&da, &wa) && dev_same(&db, &wb) && shim_same(&ss) && ita.head == head0 && kents_same(kes));

	// ---- validate (the message as sent, or with any change) ----
	if (nondet_u8() % 4 == 0) {
		size_t i = nondet_size();
		if (i < len) {
			msg[i] ^= (u8)(1 + nondet_u8() % 255);
			corrupted = 1;
		}
	}
	bytes_copy(copy, msg, len);
	check_cookie = nondet_u8() & 1;
	wg_shim_ratelimit_allow = nondet_u8() & 1;
	secret_birth = wb.cookie_checker.secret_birthdate;
	bytes_copy(secret, wb.cookie_checker.secret, 32);
	hs_take(&hs0, &p.handshake);
	pr_take(&ps0, &p);
	dev_take(&da, &wa);
	dev_take(&db, &wb);
	skb_take(&sks, &skb);
	shim_take(&ss);
	r = wg_cookie_validate_packet(&wb.cookie_checker, &skb, check_cookie);

	m_mac(mac1, wb.cookie_checker.message_mac1_key, 32, copy, len - 32);
	if (!bytes_eq(mac1, copy + len - 32, 16)) {
		verdict = INVALID_MAC;
	} else if (!check_cookie) {
		verdict = VALID_MAC_BUT_NO_COOKIE;
	} else {
		if (m_expired(secret_birth, 120, now)) {
			bytes_copy(secret, wg_shim_random_log, 32);
			secret_birth = now;
		}
		m_cookie(cookie, secret, &skb);
		m_mac(mac2, cookie, 16, copy, len - 16);
		if (!bytes_eq(mac2, copy + len - 16, 16))
			verdict = VALID_MAC_BUT_NO_COOKIE;
		else if (!wg_shim_ratelimit_allow)
			verdict = VALID_MAC_WITH_COOKIE_BUT_RATELIMITED;
		else
			verdict = VALID_MAC_WITH_COOKIE;
	}
	CHECK((int)r == verdict);
	CHECK(wb.cookie_checker.secret_birthdate == secret_birth && bytes_eq(wb.cookie_checker.secret, secret, 32));
	CHECK(bytes_eq(msg, copy, len) && skb.data == msg && skb.len == len);
	// B's checker changes only by the rotation (the model's secret and birthdate, written into the
	// snapshot), nothing else of either device, the peer or the packet; no allocation
	bytes_copy(db.secret, secret, 32);
	db.secret_birthdate = secret_birth;
	CHECK(dev_same(&db, &wb) && dev_same(&da, &wa) && skb_same(&sks, &skb) && hs_same(&hs0, &p.handshake) &&
	      pr_same(&ps0, &p) && p.refcount.refcount == refs0 && shim_same(&ss) && ita.head == head0 &&
	      kents_same(kes));

	// round trips
	if (!corrupted && honest_peer && ib.ok) {
		CHECK(r != INVALID_MAC);
		if (cookie_mode && check_cookie)
			CHECK(r == (wg_shim_ratelimit_allow ? VALID_MAC_WITH_COOKIE : VALID_MAC_WITH_COOKIE_BUT_RATELIMITED));
	}
	free(msg);
	free(copy);
	kents_free(kes);
	return 0;
}
