// SPDX-License-Identifier: GPL-2.0
// Law `cookie_reply`: the cookie reply message (wg_cookie_message_create) and its consumption
// (wg_cookie_message_consume) against the model: exact bytes, the round trip, and ANY reply bytes.
//
// Responder device B with ANY static key, ANY cookie secret and secret age; a packet with ANY message of length >=
// 32 (its mac1 at len-32), IPv4/IPv6/other source, ANY source address and port; ANY receiver index; ANY boot clock.
// Initiator device A with ANY static key and ANY number of peers (unique public keys, ANY cookie states and other
// mutable peer state (common.h peer_randomize_rest), any reference count below INT_MAX), whose handshake entries are
// in A's index table or not, plus ANY number of keypairs (whole objects of ANY content, common.h kents_add) of ANY
// peers in the table, possibly in their peers' slots; one peer P has B's public key.  The reply A consumes is B's
// reply (honest: P's handshake index, P remembers the packet's mac1 and has sent it), or B's
// reply with one byte changed, or ANY 64 bytes (receiver index drawn or taken from the table).
// Claims:
//  - create writes exactly: type 3, the receiver index, the nonce = 24 random bytes (the shim's draw), the
//    cookie encrypted = XChaCha20-Poly1305(key HASH("cookie--" || S_pub_B), nonce, cookie, ad = the packet's
//    mac1), where the cookie is MAC32(secret, source address || port) after the secret's rotation at age >= 120 s
//    ((s64)(birthdate + 120 s) <= (s64)now: at exactly 120 s the secret is new; as in law cookie_mac); B's
//    checker changes only by that rotation (B as a whole - identity, both checker keys, the checker's
//    device, tables - but that rotation); the packet is not modified (no field of it: data, length,
//    protocol, source address and port);
//  - consume accepts exactly when: the table entry with the receiver index exists (handshake or keypair entry),
//    its peer has sent a mac1, and the encrypted cookie decrypts under that peer's cookie key
//    HASH("cookie--" || its remote static) with its last mac1 as associated data.  Then that peer's cookie
//    state is exactly: cookie = the plaintext, birthdate = now, valid, mac1 no longer pending; else nothing
//    changes.  Other peers never change; references are balanced; the reply is not modified;
//  - (whole-state frame) consume changes nothing but that cookie state: every other peer as a whole, the
//    rest of that peer (handshake, reference count, keypair slots, ...), device A (identity, cookie checker,
//    public-key table), the index table (first entry, every entry's peer, type, index, membership, list link), every
//    keypair (byte for byte) stay as they were, and nothing is allocated or freed, no peer is released and no
//    reference count warns;
//  - round trip: if B has an identity, B's unmodified reply to a packet whose mac1 P sent is accepted, and P then
//    holds exactly B's cookie for that source.
#include "common.h"

struct cnode {
	struct hnode *n;
	struct ck_snap cs;
	struct cnode *next;
};

static int m_expired(u64 birthdate, u64 seconds, u64 now)
{
	return (s64)(birthdate + seconds * 1000000000ULL) <= (s64)now;
}

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

int main(void)
{
	struct wg_device wa, wb;
	struct index_hashtable ita, itb;
	struct pubkey_hashtable pta, ptb;
	struct m_identity ib;
	struct sk_buff skb;
	u8 raw_a[32], raw_b[32], pub[32], secret[32], cookie[16], k[32], enc[32];
	u8 img[COOKIE_MSG_LEN], img2[COOKIE_MSG_LEN];
	u8 *msg, *copy;
	size_t len, n, i;
	u64 now, secret_birth;
	__le32 index;
	struct message_handshake_cookie *reply;
	struct hnode *peers = NULL, *np, *it;
	struct kent *kes;
	struct cnode *cns = NULL, *cn, *target;
	struct dev_snap da, db;
	struct skb_snap sks;
	struct shim_snap ss;
	struct index_hashtable_entry *head0;
	struct index_hashtable_entry *e;
	int mode, honest;

	wg_shim_boottime_ns = draw_boottime();
	wg_noise_init();
	nondet_bytes(raw_a, 32);
	nondet_bytes(raw_b, 32);
	setup_device(&wa, &ita, &pta, raw_a);
	setup_device(&wb, &itb, &ptb, raw_b);
	m_identity_of(&ib, raw_b);
	nondet_bytes(wb.cookie_checker.secret, 32);
	wb.cookie_checker.secret_birthdate = draw_boottime();

	// the packet B answers
	len = draw_size();
	if (len > SIZE_MAX - 32 || len + 32 > 0xffffffffu)
		return 0;
	len += 32;
	msg = malloc(len);
	copy = malloc(len);
	reply = malloc(sizeof(*reply));
	if (msg == NULL || copy == NULL || reply == NULL) {
		free(msg);
		free(copy);
		free(reply);
		return 0;
	}
	nondet_bytes(msg, len);
	bytes_copy(copy, msg, len);
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
	index = nondet_u32();

	// ---- B: create ----
	fill_cookie_msg(reply);
	secret_birth = wb.cookie_checker.secret_birthdate;
	bytes_copy(secret, wb.cookie_checker.secret, 32);
	dev_take(&db, &wb);
	skb_take(&sks, &skb);
	wg_cookie_message_create(reply, &skb, index, &wb.cookie_checker);
	// random draws: the nonce, then (if the secret is 120 s old) the new secret
	if (m_expired(secret_birth, 120, now)) {
		bytes_copy(secret, wg_shim_random_log, 32);
		secret_birth = now;
		CHECK(bytes_eq(reply->nonce, wg_shim_random_log_prev, 24));
	} else {
		CHECK(bytes_eq(reply->nonce, wg_shim_random_log, 24));
	}
	CHECK(wb.cookie_checker.secret_birthdate == secret_birth && bytes_eq(wb.cookie_checker.secret, secret, 32));
	m_cookie(cookie, secret, &skb);
	if (ib.ok)
		m_label_key(k, M_LABEL_COOKIE, wb.static_identity.static_public);
	else
		bytes_set(k, 0, 32);
	CHECK(bytes_eq(wb.cookie_checker.cookie_encryption_key, k, 32));
	CHECK(reply->header.type == MESSAGE_HANDSHAKE_COOKIE && reply->receiver_index == index);
	xchacha20poly1305_encrypt(enc, cookie, 16, msg + len - 32, 16, reply->nonce, k);
	CHECK(bytes_eq(reply->encrypted_cookie, enc, 32));
	CHECK(bytes_eq(msg, copy, len));
	// B changes only by the rotation (the model's secret, birthdate), the packet not at all
	bytes_copy(db.secret, secret, 32);
	db.secret_birthdate = secret_birth;
	CHECK(dev_same(&db, &wb) && skb_same(&sks, &skb));

	// ---- A's peers ----
	np = hnodes_add(&peers, &wa, wb.static_identity.static_public, 0);
	n = draw_steps();
	for (i = 0; i < n; i++) {
		nondet_bytes(pub, 32);
		hnodes_add(&peers, &wa, pub, 1 + i);
	}
	for (it = peers; it; it = it->next) {
		peer_randomize_rest(it->p);   // ANY cookie state (and dead flag, last sent handshake)
		if (nondet_u8() % 4 != 0)
			wg_index_hashtable_insert(&ita, &it->p->handshake.entry);
		cn = malloc(sizeof(*cn));
		if (cn == NULL)
			return 0;   /* end the run cleanly (the model must track every peer) */
		cn->n = it;
		cn->next = cns;
		cns = cn;
	}
	kes = kents_add(&ita, peers, NULL, 1);   // keypairs of any peers, possibly in their slots

	// ---- the reply A consumes ----
	mode = nondet_u8() % 3;
	honest = 0;
	if (mode != 2 && np != NULL) {
		// B's reply to P: P's handshake index, and P has sent the packet's mac1
		struct noise_handshake *h = &np->p->handshake;
		if (!h->entry.hashed)
			wg_index_hashtable_insert(&ita, &h->entry);
		reply->receiver_index = h->entry.index;
		np->p->latest_cookie.have_sent_mac1 = true;
		bytes_copy(np->p->latest_cookie.last_mac1_sent, msg + len - 32, 16);
		honest = mode == 0;
		if (mode == 1) {
			size_t kk = nondet_size() % COOKIE_MSG_LEN;
			u8 d = (u8)(1 + nondet_u8() % 255);
			if (kk < 4)
				reply->header.type ^= d;       // not read by consume
			else if (kk < 8)
				reply->receiver_index ^= d;
			else if (kk < 32)
				reply->nonce[kk - 8] ^= d;
			else
				reply->encrypted_cookie[kk - 32] ^= d;
		}
	} else if (mode == 2) {
		fill_cookie_msg(reply);
		if (ita.head != NULL && (nondet_u8() & 1)) {
			size_t kk = nondet_size();
			for (e = ita.head; e->next != NULL && kk > 0; e = e->next)
				kk--;
			reply->receiver_index = e->index;
		}
	}
	cookie_img(img, reply);
	hnodes_snap(peers);
	for (cn = cns; cn; cn = cn->next)
		ck_take(&cn->cs, &cn->n->p->latest_cookie);
	kents_snap(kes);
	dev_take(&da, &wa);
	head0 = ita.head;
	now = draw_boottime();
	wg_shim_boottime_ns = now;
	shim_take(&ss);
	wg_cookie_message_consume(reply, &wa);

	// the model
	target = NULL;
	for (e = ita.head; e != NULL && e->index != reply->receiver_index; e = e->next)
		;
	if (e != NULL && (e->type & (INDEX_HASHTABLE_HANDSHAKE | INDEX_HASHTABLE_KEYPAIR))) {
		for (cn = cns; cn; cn = cn->next)
			if (cn->n->p == e->peer && target == NULL)
				target = cn;
	}
	if (target != NULL) {
		u8 pt[16];
		if (!target->cs.have_sent_mac1 ||
		    !xchacha20poly1305_decrypt(pt, reply->encrypted_cookie, 32, target->cs.last_mac1_sent, 16, reply->nonce,
					       target->cs.cookie_decryption_key)) {
			target = NULL;
		} else {
			struct cookie *c = &target->n->p->latest_cookie;
			CHECK(bytes_eq(c->cookie, pt, 16) && c->birthdate == now && c->is_valid && !c->have_sent_mac1 &&
			      bytes_eq(c->last_mac1_sent, target->cs.last_mac1_sent, 16) &&
			      bytes_eq(c->cookie_decryption_key, target->cs.cookie_decryption_key, 32) &&
			      bytes_eq(c->message_mac1_key, target->cs.message_mac1_key, 32));
		}
	}
	for (cn = cns; cn; cn = cn->next)
		if (cn != target)
			CHECK(ck_same(&cn->cs, &cn->n->p->latest_cookie));
	// every other peer as a whole; of the target, everything but its cookie state; device A, the
	// index table and the shim's counters
	if (target == NULL) {
		CHECK(hnodes_same_except(peers, NULL));
	} else {
		struct hnode *tn = target->n;
		CHECK(hnodes_same_except(peers, tn->p));
		CHECK(hs_same(&tn->snap, &tn->p->handshake) && tn->p->refcount.refcount == tn->refs &&
		      pr_same_but_cookie(&tn->rest, tn->p));
	}
	CHECK(dev_same(&da, &wa) && ita.head == head0 && kents_same(kes) && shim_same(&ss));
	cookie_img(img2, reply);
	CHECK(bytes_eq(img, img2, COOKIE_MSG_LEN));
	if (honest && np != NULL && ib.ok) {
		CHECK(target != NULL && target->n == np);
		CHECK(bytes_eq(np->p->latest_cookie.cookie, cookie, 16));
	}

	while (cns) {
		cn = cns->next;
		free(cns);
		cns = cn;
	}
	kents_free(kes);
	hnodes_free(peers);
	free(msg);
	free(copy);
	free(reply);
	return 0;
}
