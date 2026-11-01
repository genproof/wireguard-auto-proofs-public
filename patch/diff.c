// SPDX-License-Identifier: GPL-2.0
// patch/diff.c: the differential test of the patch (DEVIATIONS.md P01..P23, S18).  Not a law.
//
// patch/diff.sh builds this driver twice, against the unmodified upstream units (patch/tree.sh --orig) and against
// this repository's units (patch/tree.sh), with the same shim, under ASan/UBSan, and runs both with the same seeds.  The
// driver calls every patched function through the public API on pseudo-random inputs (degenerate keys, zero
// points, arbitrary handshake states, corrupted messages, all verdict paths) and folds EVERY output byte and
// return value into one output hash per section.  Identical outputs = identical behaviour on these
// inputs.  The environment (nondet_*: keys, random bytes, indices) is this driver's seeded PRNG, so the two
// builds see the same draws as long as they make the same calls.
// P22 and P23 are patches 4/5 and 5/5 of the lib/crypto series: they change results only for
// chunks / lengths of about 2^32 bytes, which this driver never draws, so here too the outputs must be
// identical; the sections poly_split and aead_lens cover every short chunking and length exhaustively, diff.sh's
// small-limit builds (small1, small2) run the series' loops with several iterations, and patch/tests/big.sh runs
// the failing range (>= 4 GiB) itself.
#include "../harness/common.h"
#include <crypto/chacha.h>
#include <crypto/poly1305.h>
#include <stdio.h>
#include <stdlib.h>
extern bool wg_shim_fail_next_alloc;

static uint64_t rs;
static uint64_t rnd64(void)
{
	rs ^= rs << 13;
	rs ^= rs >> 7;
	rs ^= rs << 17;
	return rs;
}

uint8_t nondet_u8(void) { return (uint8_t)rnd64(); }
uint32_t nondet_u32(void)
{
	switch (rnd64() % 6) {
	case 0: return (uint32_t)(rnd64() % 8);
	case 1: return 0xffffffffu - (uint32_t)(rnd64() % 3);
	default: return (uint32_t)rnd64();
	}
}
size_t nondet_size(void)
{
	switch (rnd64() % 4) {
	case 0: return rnd64() % 4;
	case 1: return 16 * (1 + rnd64() % 5) - 1 + rnd64() % 3;
	default: return rnd64() % 200;
	}
}
void nondet_bytes(uint8_t *buf, size_t n)
{
	unsigned kind = rnd64() % 16;
	for (size_t i = 0; i < n; i++)
		buf[i] = kind == 0 ? 0 : kind == 1 ? 0xff : (uint8_t)rnd64();
}

// ---- the output hash ----
#define NRAND 10	// sections drawn at random in the main loop; the last two run once, exhaustively (P22, P23)
#define NSEC 12
static const char *secname[NSEC] = { "blake2s", "chacha", "aead", "poly1305", "curve25519", "handshake",
				     "noise_any", "keypairs", "cookie", "counter", "poly_split", "aead_lens" };
static uint64_t th[NSEC], tcount[NSEC];
static int sec;

static void t_bytes(const void *p, size_t n)
{
	const u8 *b = p;
	for (size_t i = 0; i < n; i++) {
		th[sec] ^= b[i];
		th[sec] *= 0x100000001b3ULL;
	}
	tcount[sec] += n;
}
static void t_u64(u64 v) { u8 b[8]; le64_store(b, v); t_bytes(b, 8); }

static void t_hs(const struct noise_handshake *h)
{
	t_u64(h->state);
	t_u64(h->last_initiation_consumption);
	t_bytes(h->ephemeral_private, 32);
	t_bytes(h->remote_static, 32);
	t_bytes(h->remote_ephemeral, 32);
	t_bytes(h->precomputed_static_static, 32);
	t_bytes(h->preshared_key, 32);
	t_bytes(h->hash, 32);
	t_bytes(h->chaining_key, 32);
	t_bytes(h->latest_timestamp, 12);
	t_u64(h->remote_index);
	t_u64(h->entry.index);
	t_u64(h->entry.hashed);
}

static void t_kp(const struct noise_keypair *k)
{
	if (k == NULL) {
		t_u64(0xdead);
		return;
	}
	t_bytes(k->sending.key, 32);
	t_bytes(k->receiving.key, 32);
	t_u64(k->sending.birthdate);
	t_u64(k->sending.is_valid);
	t_u64(k->receiving.is_valid);
	t_u64(k->remote_index);
	t_u64(k->i_am_the_initiator);
	t_u64(k->refcount.refcount);
	t_u64(k->entry.index);
	t_u64(k->entry.hashed);
}

static void t_cookie(const struct cookie *c)
{
	t_u64(c->birthdate);
	t_u64(c->is_valid);
	t_bytes(c->cookie, 16);
	t_u64(c->have_sent_mac1);
	t_bytes(c->last_mac1_sent, 16);
	t_bytes(c->cookie_decryption_key, 32);
	t_bytes(c->message_mac1_key, 32);
}

// ---- sections ----
static void s_blake2s(void)
{
	struct blake2s_ctx ctx;
	u8 key[32], out[32], msg[300];
	size_t keylen = rnd64() % 33, outlen = 1 + rnd64() % 32, n = rnd64() % 300, pos = 0;
	nondet_bytes(key, 32);
	nondet_bytes(msg, n);
	if (keylen)
		blake2s_init_key(&ctx, outlen, key, keylen);
	else
		blake2s_init(&ctx, outlen);
	while (pos < n) {
		size_t c = rnd64() % (n - pos + 1);
		blake2s_update(&ctx, msg + pos, c);
		pos += c;
	}
	blake2s_final(&ctx, out);
	t_bytes(out, outlen);
	t_bytes(&ctx, sizeof(ctx));
	blake2s(keylen ? key : NULL, keylen, msg, n, out, outlen);
	t_bytes(out, outlen);
}

static void s_chacha(void)
{
	struct chacha_state st;
	u32 out[8];
	u8 blk[64], buf[200], dst[200];
	int i;
	unsigned n = rnd64() % 200;
	for (i = 0; i < 16; i++)
		st.x[i] = (u32)rnd64();
	hchacha_block(&st, out, rnd64() % 2 ? 20 : 12);
	t_bytes(out, 32);
	chacha_block_generic(&st, blk, 20);
	t_bytes(blk, 64);
	t_bytes(st.x, 64);
	nondet_bytes(buf, n);
	chacha_crypt(&st, dst, buf, n, 20);
	t_bytes(dst, n);
	t_bytes(st.x, 64);
}

static void s_aead(void)
{
	u8 key[32], xn[24], ad[100], pt[200], ct[216], dec[200];
	size_t adlen = rnd64() % 100, n = rnd64() % 200;
	u64 nonce = rnd64();
	int x = rnd64() & 1, ok;
	nondet_bytes(key, 32);
	nondet_bytes(xn, 24);
	nondet_bytes(ad, adlen);
	nondet_bytes(pt, n);
	if (x)
		xchacha20poly1305_encrypt(ct, pt, n, ad, adlen, xn, key);
	else
		chacha20poly1305_encrypt(ct, pt, n, ad, adlen, nonce, key);
	t_bytes(ct, n + 16);
	if (rnd64() % 3 == 0)
		ct[rnd64() % (n + 16)] ^= 1;
	memset(dec, 0x5a, sizeof(dec));
	ok = x ? xchacha20poly1305_decrypt(dec, ct, n + 16 - (rnd64() % 4 == 0 ? rnd64() % (n + 17) : 0), ad, adlen, xn, key)
	       : chacha20poly1305_decrypt(dec, ct, n + 16 - (rnd64() % 4 == 0 ? rnd64() % (n + 17) : 0), ad, adlen, nonce, key);
	t_u64(ok);
	t_bytes(dec, sizeof(dec));
}

static void s_poly1305(void)
{
	struct poly1305_desc_ctx d;
	u8 key[32], msg[300], mac[16];
	size_t n = rnd64() % 300, pos = 0;
	nondet_bytes(key, 32);
	nondet_bytes(msg, n);
	poly1305_init(&d, key);
	while (pos < n) {
		size_t c = rnd64() % (n - pos + 1);
		poly1305_update(&d, msg + pos, (unsigned int)c);
		pos += c;
	}
	poly1305_final(&d, mac);
	t_bytes(mac, 16);
	t_bytes(d.buf, 16);           // the context is zeroed by final (named fields: padding is unspecified)
	t_u64(d.buflen);
	t_bytes(d.s, 16);
	t_bytes(d.state.h.h, 20);
	t_bytes(d.state.core_r.key.r, 20);
	t_bytes(d.state.core_r.precomputed_s.r, 20);
}

// P22: poly1305_update's block-path test.  Every buffered state (a first chunk of p = 0..47 bytes, so buflen = 0..15
// with 0..2 blocks done), then every chunk c = 0..299, then a rest of 0, 1 or 17 bytes; tag and zeroed context.
static void s_poly1305_split(void)
{
	struct poly1305_desc_ctx d;
	u8 key[32], msg[400], mac[16];
	unsigned int p, c, r;
	static const unsigned int rest[3] = { 0, 1, 17 };
	for (p = 0; p < 48; p++)
		for (c = 0; c < 300; c++)
			for (r = 0; r < 3; r++) {
				nondet_bytes(key, 32);
				nondet_bytes(msg, p + c + rest[r]);
				poly1305_init(&d, key);
				poly1305_update(&d, msg, p);
				poly1305_update(&d, msg + p, c);
				poly1305_update(&d, msg + p + c, rest[r]);
				poly1305_final(&d, mac);
				t_bytes(mac, 16);
				t_bytes(d.buf, 16);
				t_u64(d.buflen);
				t_bytes(d.s, 16);
				t_bytes(d.state.h.h, 20);
			}
}

// P23: every associated-data length 0..64 and message length 0..130, both constructions: ciphertext and tag,
// decryption of it, and decryption with one byte changed (also the output buffer on rejection)
static void s_aead_lens(void)
{
	u8 key[32], xn[24], ad[64], pt[130], ct[146], dec[130];
	size_t adlen, n;
	u64 nonce;
	int x, ok;
	for (x = 0; x < 2; x++)
		for (adlen = 0; adlen <= 64; adlen++)
			for (n = 0; n <= 130; n++) {
				nondet_bytes(key, 32);
				nondet_bytes(xn, 24);
				nondet_bytes(ad, adlen);
				nondet_bytes(pt, n);
				nonce = rnd64();
				if (x)
					xchacha20poly1305_encrypt(ct, pt, n, ad, adlen, xn, key);
				else
					chacha20poly1305_encrypt(ct, pt, n, ad, adlen, nonce, key);
				t_bytes(ct, n + 16);
				memset(dec, 0x5a, sizeof(dec));
				ok = x ? xchacha20poly1305_decrypt(dec, ct, n + 16, ad, adlen, xn, key)
				       : chacha20poly1305_decrypt(dec, ct, n + 16, ad, adlen, nonce, key);
				t_u64(ok);
				t_bytes(dec, sizeof(dec));
				ct[rnd64() % (n + 16)] ^= 1;
				memset(dec, 0x5a, sizeof(dec));
				ok = x ? xchacha20poly1305_decrypt(dec, ct, n + 16, ad, adlen, xn, key)
				       : chacha20poly1305_decrypt(dec, ct, n + 16, ad, adlen, nonce, key);
				t_u64(ok);
				t_bytes(dec, sizeof(dec));
			}
}

static void s_curve25519(void)
{
	u8 s[32], p[32], out[32];
	nondet_bytes(s, 32);
	nondet_bytes(p, 32);
	curve25519_generic(out, s, p);
	t_bytes(out, 32);
	t_u64(curve25519(out, s, p));
	t_bytes(out, 32);
	memset(out, 0x77, 32);
	t_u64(curve25519_generate_public(out, s));
	t_bytes(out, 32);
}

// a full handshake between two devices, with degenerate keys now and then, and every step's outputs
static void s_handshake(void)
{
	struct wg_device wa, wb;
	struct index_hashtable ita, itb;
	struct pubkey_hashtable pta, ptb;
	struct wg_peer pa, pb, *r;
	u8 ra[32], rb[32], psk[32];
	struct message_handshake_initiation m1;
	struct message_handshake_response m2;
	u8 img[INIT_LEN], rimg[RESP_LEN];
	int use_psk = rnd64() & 1;

	wg_shim_boottime_ns = rnd64() & ((1ULL << 62) - 1);
	nondet_bytes(ra, 32);
	nondet_bytes(rb, 32);
	nondet_bytes(psk, 32);
	setup_device(&wa, &ita, &pta, ra);
	setup_device(&wb, &itb, &ptb, rb);
	t_bytes(wa.static_identity.static_public, 32);
	t_u64(wa.static_identity.has_identity);
	t_bytes(wb.cookie_checker.message_mac1_key, 32);
	t_bytes(wb.cookie_checker.cookie_encryption_key, 32);
	setup_peer(&pb, &wa, wb.static_identity.static_public, use_psk ? psk : NULL, 1);
	setup_peer(&pa, &wb, rnd64() % 8 ? wa.static_identity.static_public : psk, use_psk ? psk : NULL, 2);
	t_hs(&pb.handshake);
	t_cookie(&pb.latest_cookie);
	fill_init(&m1);
	fill_resp(&m2);
	draw_real_clock();
	t_u64(wg_noise_handshake_create_initiation(&m1, &pb.handshake));
	wg_cookie_add_mac_to_packet(&m1, sizeof(m1), &pb);
	init_img(img, &m1);
	t_bytes(img, INIT_LEN);
	t_hs(&pb.handshake);
	wg_shim_boottime_ns = rnd64() & ((1ULL << 62) - 1);
	r = wg_noise_handshake_consume_initiation(&m1, &wb);
	t_u64(r == &pa);
	t_u64(r == NULL);
	if (r)
		wg_peer_put(r);
	t_hs(&pa.handshake);
	t_u64(wg_noise_handshake_create_response(&m2, &pa.handshake));
	wg_cookie_add_mac_to_packet(&m2, sizeof(m2), &pa);
	resp_img(rimg, &m2);
	t_bytes(rimg, RESP_LEN);
	t_hs(&pa.handshake);
	r = wg_noise_handshake_consume_response(&m2, &wa);
	t_u64(r == &pb);
	t_u64(r == NULL);
	if (r)
		wg_peer_put(r);
	t_hs(&pb.handshake);
	pb.is_dead = rnd64() % 8 == 0;
	t_u64(wg_noise_handshake_begin_session(&pb.handshake, &pb.keypairs));
	t_u64(wg_noise_handshake_begin_session(&pa.handshake, &pa.keypairs));
	t_kp(pb.keypairs.current_keypair);
	t_kp(pa.keypairs.next_keypair);
	t_hs(&pb.handshake);
	t_hs(&pa.handshake);
	t_u64(pa.refcount.refcount);
	t_u64(pb.refcount.refcount);
	wg_noise_keypairs_clear(&pb.keypairs);
	wg_noise_keypairs_clear(&pa.keypairs);
	t_u64(table_len(&ita));
	t_u64(table_len(&itb));
}

// the handshake functions on arbitrary state and arbitrary messages
static void s_noise_any(void)
{
	struct wg_device w;
	struct index_hashtable it;
	struct pubkey_hashtable pt;
	struct wg_peer p, q, *r;
	u8 raw[32], pub[32];
	struct message_handshake_initiation m1;
	struct message_handshake_response m2;
	u8 img[INIT_LEN], rimg[RESP_LEN];

	wg_shim_boottime_ns = rnd64() & ((1ULL << 62) - 1);
	nondet_bytes(raw, 32);
	setup_device(&w, &it, &pt, raw);
	nondet_bytes(pub, 32);
	setup_peer(&p, &w, pub, NULL, 1);
	nondet_bytes(pub, 32);
	setup_peer(&q, &w, pub, pub, 2);
	hs_randomize(&p.handshake);
	hs_randomize(&q.handshake);
	if (rnd64() % 4 == 0)
		memset(p.handshake.precomputed_static_static, 0, 32);   // the "ss" failure paths
	if (rnd64() & 1)
		wg_index_hashtable_insert(&it, &p.handshake.entry);
	if (rnd64() & 1)
		wg_index_hashtable_insert(&it, &q.handshake.entry);
	fill_init(&m1);
	fill_resp(&m2);
	if (rnd64() & 1)
		m2.receiver_index = p.handshake.entry.index;
	draw_real_clock();
	switch (rnd64() % 4) {
	case 0: t_u64(wg_noise_handshake_create_initiation(&m1, &p.handshake)); break;
	case 1: t_u64(wg_noise_handshake_create_response(&m2, &p.handshake)); break;
	case 2:
		if (rnd64() & 1) {
			// an initiation to this device from a peer whose key it knows: w's own peer p has w's public key
			memcpy(p.handshake.remote_static, w.static_identity.static_public, 32);
			wg_noise_precompute_static_static(&p);
			if (rnd64() % 4 == 0)
				memset(p.handshake.precomputed_static_static, 0, 32);
			wg_noise_handshake_create_initiation(&m1, &p.handshake);
			if (rnd64() % 3 == 0)
				m1.encrypted_timestamp[rnd64() % 28] ^= 1;
		}
		r = wg_noise_handshake_consume_initiation(&m1, &w);
		t_u64(r == &p);
		t_u64(r == &q);
		if (r)
			wg_peer_put(r);
		break;
	default:
		r = wg_noise_handshake_consume_response(&m2, &w);
		t_u64(r == &p);
		t_u64(r == &q);
		if (r)
			wg_peer_put(r);
		break;
	}
	init_img(img, &m1);
	resp_img(rimg, &m2);
	t_bytes(img, INIT_LEN);
	t_bytes(rimg, RESP_LEN);
	t_hs(&p.handshake);
	t_hs(&q.handshake);
	t_u64(p.refcount.refcount);
}

static void s_keypairs(void)
{
	struct wg_device w;
	struct index_hashtable it;
	struct pubkey_hashtable pt;
	struct wg_peer p;
	struct noise_keypair *held[8];
	int nh = 0, i, steps = rnd64() % 40;
	u8 raw[32], pub[32];

	nondet_bytes(raw, 32);
	nondet_bytes(pub, 32);
	setup_device(&w, &it, &pt, raw);
	setup_peer(&p, &w, pub, NULL, 1);
	for (i = 0; i < steps; i++) {
		struct noise_keypair *k;
		wg_shim_boottime_ns += rnd64() % 1000000000ULL;
		switch (rnd64() % 6) {
		case 0:
			p.handshake.state = draw_hs_state();
			nondet_bytes(p.handshake.chaining_key, 32);
			p.handshake.remote_index = nondet_u32();
			if (rnd64() & 1)
				wg_index_hashtable_insert(&it, &p.handshake.entry);
			p.is_dead = rnd64() % 8 == 0;
			wg_shim_fail_next_alloc = rnd64() % 8 == 0;
			t_u64(wg_noise_handshake_begin_session(&p.handshake, &p.keypairs));
			wg_shim_fail_next_alloc = false;
			break;
		case 1: {
			int c = rnd64() % 3;
			k = c == 0 ? p.keypairs.current_keypair : c == 1 ? p.keypairs.previous_keypair : p.keypairs.next_keypair;
			if (k)
				t_u64(wg_noise_received_with_keypair(&p.keypairs, k));
			break;
		}
		case 2: wg_noise_expire_current_peer_keypairs(&p); t_u64(p.last_sent_handshake.counter); break;
		case 3: wg_noise_keypairs_clear(&p.keypairs); break;
		case 4:
			if (nh < 8) {
				k = wg_noise_keypair_get(p.keypairs.current_keypair);
				if (k)
					held[nh++] = k;
			}
			break;
		default:
			if (nh > 0)
				wg_noise_keypair_put(held[--nh], rnd64() & 1);
			break;
		}
		t_kp(p.keypairs.previous_keypair);
		t_kp(p.keypairs.current_keypair);
		t_kp(p.keypairs.next_keypair);
		t_hs(&p.handshake);
		t_u64(table_len(&it));
	}
	wg_noise_keypairs_clear(&p.keypairs);
	while (nh > 0)
		wg_noise_keypair_put(held[--nh], false);
}

static void s_cookie(void)
{
	struct wg_device wa, wb;
	struct index_hashtable ita, itb;
	struct pubkey_hashtable pta, ptb;
	struct wg_peer p;
	struct sk_buff skb;
	struct message_handshake_cookie reply;
	u8 raw[32], msg[200], img[COOKIE_MSG_LEN];
	size_t len = 32 + rnd64() % 150;

	nondet_bytes(raw, 32);
	setup_device(&wb, &itb, &ptb, raw);
	nondet_bytes(raw, 32);
	setup_device(&wa, &ita, &pta, raw);
	setup_peer(&p, &wa, rnd64() % 4 ? wb.static_identity.static_public : raw, NULL, 1);
	nondet_bytes(wb.cookie_checker.secret, 32);
	wb.cookie_checker.secret_birthdate = rnd64() & ((1ULL << 62) - 1);
	wg_shim_boottime_ns = rnd64() & ((1ULL << 62) - 1);
	p.latest_cookie.is_valid = rnd64() & 1;
	p.latest_cookie.birthdate = rnd64() & ((1ULL << 62) - 1);
	nondet_bytes(p.latest_cookie.cookie, 16);
	nondet_bytes(msg, len);
	skb.data = msg;
	skb.len = (unsigned int)len;
	skb.protocol = rnd64() % 3 == 0 ? htons(ETH_P_IP) : rnd64() % 2 ? htons(ETH_P_IPV6) : (u16)rnd64();
	nondet_bytes(skb.ip4.saddr.s_addr, 4);
	nondet_bytes(skb.ip6.saddr.s6_addr, 16);
	nondet_bytes(skb.udp.source, 2);
	wg_cookie_add_mac_to_packet(msg, len, &p);
	t_bytes(msg, len);
	t_cookie(&p.latest_cookie);
	if (rnd64() % 4 == 0)
		msg[rnd64() % len] ^= 1;
	wg_shim_ratelimit_allow = rnd64() & 1;
	t_u64(wg_cookie_validate_packet(&wb.cookie_checker, &skb, rnd64() & 1));
	t_bytes(wb.cookie_checker.secret, 32);
	t_u64(wb.cookie_checker.secret_birthdate);
	fill_cookie_msg(&reply);
	wg_cookie_message_create(&reply, &skb, nondet_u32(), &wb.cookie_checker);
	cookie_img(img, &reply);
	t_bytes(img, COOKIE_MSG_LEN);
	if (rnd64() % 4 != 0)
		wg_index_hashtable_insert(&ita, &p.handshake.entry);
	if (rnd64() % 4 != 0)
		reply.receiver_index = p.handshake.entry.index;
	if (rnd64() % 4 == 0)
		reply.encrypted_cookie[rnd64() % 32] ^= 1;
	p.latest_cookie.have_sent_mac1 = rnd64() % 4 != 0;
	wg_cookie_message_consume(&reply, &wa);
	t_cookie(&p.latest_cookie);
	t_u64(p.refcount.refcount);
	// with the cookie (if accepted): mac2 again, and the validation paths behind a valid mac2
	wg_cookie_add_mac_to_packet(msg, len, &p);
	t_bytes(msg, len);
	wg_shim_ratelimit_allow = rnd64() & 1;
	t_u64(wg_cookie_validate_packet(&wb.cookie_checker, &skb, true));
}

bool wg_counter_validate(struct noise_replay_counter *counter, u64 their_counter);

static void s_counter(void)
{
	struct noise_replay_counter c;
	u64 top = 0;
	int i, steps = rnd64() % 300;
	memset(&c, 0, sizeof(c));
	for (i = 0; i < steps; i++) {
		u64 n;
		switch (rnd64() % 4) {
		case 0: n = top + rnd64() % 200 - 100; break;
		case 1: n = top - rnd64() % 9000; break;
		case 2: n = 0xffffffffffffffffULL - 8129 + rnd64() % 8 - 4; break;
		default: n = rnd64(); break;
		}
		t_u64(wg_counter_validate(&c, n));
		t_u64(c.counter);
		top = c.counter;
	}
	t_bytes(c.backtrack, sizeof(c.backtrack));
}

int main(int argc, char **argv)
{
	long iters = argc > 1 ? atol(argv[1]) : 20000;
	uint64_t seed = argc > 2 ? strtoull(argv[2], NULL, 0) : 1;
	long i;

	rs = 0x9E3779B97F4A7C15ULL ^ (seed * 0x2545F4914F6CDD1DULL);
	wg_noise_init();
	for (i = 0; i < iters; i++) {
		sec = (int)(rnd64() % NRAND);
		switch (sec) {
		case 0: s_blake2s(); break;
		case 1: s_chacha(); break;
		case 2: s_aead(); break;
		case 3: s_poly1305(); break;
		case 4: s_curve25519(); break;
		case 5: s_handshake(); break;
		case 6: s_noise_any(); break;
		case 7: s_keypairs(); break;
		case 8: s_cookie(); break;
		default: s_counter(); break;
		}
	}
	sec = 10;
	s_poly1305_split();
	sec = 11;
	s_aead_lens();
	for (i = 0; i < NSEC; i++)
		printf("%-10s bytes %12llu  hash %016llx\n", secname[i], (unsigned long long)tcount[i],
		       (unsigned long long)th[i]);
	return 0;
}
