// SPDX-License-Identifier: GPL-2.0
// Law `transport_order`: on the receive data path the replay counter is validated only AFTER the
// AEAD tag verifies, and a packet with a bad tag is dropped with NO change to the replay counter and NO
// plaintext consumed.
//
// One receiving keypair (one receiving key, a fresh RFC 6479 replay counter) and a sequence of ANY length of
// received MESSAGE_DATA packets: authentic ones (the real chacha20poly1305_encrypt under the key at a drawn
// nonce), authentic ones with one byte of the ciphertext flipped, replays of an authentic nonce, and fully
// random bytes.  The harness runs receive.c's two stages in order on each packet, composing the REAL functions
// the pipeline composes (see transport.h):
//   stage 1 (decrypt_packet): ok = chacha20poly1305_decrypt(...);   the counter is untouched here;
//   stage 2 (rx_poll):        only if ok, r = wg_counter_validate(&receiving_counter, nonce);  deliver iff r.
// Shadow model: ref_aead_decrypt (common.h) for whether the tag verifies and the plaintext; a window model
// (transport.h) for the counter verdict.
// CHECKs after every packet:
//   - ok == (the reference tag verifies);
//   - BAD TAG  => the whole replay counter is byte-for-byte unchanged (no counter advance, no bit set) and
//                 nothing is delivered  [the ordering invariant: no state change / no consume on a bad tag];
//   - GOOD TAG => wg_counter_validate is reached, its verdict == the window model, the counter advances to the
//                 model's top, and delivered iff accepted; a delivered packet's plaintext == the reference.
#include "transport.h"

#define MD_HDR 16                        // sizeof(struct message_data): header(4) + key_idx(4) + counter(8)

static u64 draw_nonce(u64 top)
{
	switch (nondet_u8() % 5) {
	case 0: return top + (u64)(nondet_u32() % 200) - 100;        // around the top
	case 1: return top - (u64)(nondet_u32() % 9000);             // inside / just outside the window
	case 2: return M_R + (u64)(nondet_u32() % 8) - 4;            // around the reject limit
	case 3: return top - M_W - 1 + (u64)(nondet_u32() % 5) - 2;  // the window's edge
	default: return draw_u64();
	}
}

int main(void)
{
	struct noise_replay_counter rc;
	struct wmodel wm;
	struct rc_snap snap;
	u8 key[32];
	u64 last_nonce = 0;
	int have_auth = 0;
	size_t steps, i;

	rc_init(&rc);
	wm_init(&wm);
	nondet_bytes(key, 32);

	steps = draw_steps();
	for (i = 0; i < steps; i++) {
		u8 *pkt, *pt_out, *ref_pt;
		size_t L, enc_len, tot, j;
		u64 nonce;
		int kind, ok, ref_ok;

		kind = nondet_u8() % 4;
		L = draw_size();
		if (L > PTRDIFF_MAX - 32)             // no C object that large (DEVIATIONS.md L13, prim_aead.h)
			break;
		if (kind == 3 && L < 16)              // a "random bytes" packet of < 16 bytes has no room for a tag
			enc_len = L;                  // keep enc_len = L (the AEAD rejects it; exact buffer)
		else
			enc_len = L + 16;
		tot = MD_HDR + enc_len;

		pkt = malloc(tot);
		pt_out = malloc(enc_len >= 16 ? enc_len - 16 : 0);
		ref_pt = malloc(enc_len >= 16 ? enc_len - 16 : 0);
		if (pkt == NULL || pt_out == NULL || ref_pt == NULL) {
			free(pkt); free(pt_out); free(ref_pt);
			break;
		}

		nonce = (kind == 2 && have_auth) ? last_nonce : draw_nonce(wm.top);
		// message_data header: type, key_idx, counter (the only field the data path reads here)
		le32_store(pkt, MESSAGE_DATA);
		le32_store(pkt + 4, nondet_u32());
		le64_store(pkt + 8, nonce);

		if (kind == 0 || kind == 1 || kind == 2) {
			// an authentic packet: real AEAD-encrypt L plaintext bytes under the key at this nonce
			u8 *pt = malloc(L);
			if (pt == NULL) {
				free(pkt); free(pt_out); free(ref_pt);
				break;
			}
			nondet_bytes(pt, L);
			chacha20poly1305_encrypt(pkt + MD_HDR, pt, L, NULL, 0, nonce, key);
			free(pt);
			if (kind == 1) {
				// flip one byte of the ciphertext||tag -> the tag no longer verifies
				j = nondet_size();
				if (j < enc_len)
					pkt[MD_HDR + j] ^= (u8)(1 + nondet_u8() % 255);
			}
		} else {
			nondet_bytes(pkt + MD_HDR, enc_len);
		}

		// ===== the receive pipeline, in order =====
		rc_take(&snap, &rc);
		// stage 1 (decrypt_packet): AEAD verify; the replay counter is not touched here
		ok = chacha20poly1305_decrypt(pt_out, pkt + MD_HDR, enc_len, NULL, 0, nonce, key);
		ref_ok = ref_aead_decrypt(ref_pt, pkt + MD_HDR, enc_len, NULL, 0, nonce, key);
		CHECK(ok == ref_ok);

		if (!ok) {
			// BAD TAG: dropped before stage 2.  The ordering invariant:
			CHECK(rc_same(&snap, &rc));       // the replay counter is byte-for-byte unchanged
			// (no plaintext is consumed: stage 2 / consume_data_done is never reached)
		} else {
			// only an authenticated packet reaches the counter (stage 2: rx_poll)
			int pred = wm_accepts(&wm, nonce);
			int r = wg_counter_validate(&rc, nonce);
			CHECK(r == pred);
			if (r) {
				CHECK(bytes_eq(pt_out, ref_pt, enc_len - 16));  // delivered plaintext == reference
				if (!wm_commit(&wm, nonce)) {
					free(pkt); free(pt_out); free(ref_pt);
					break;
				}
			}
			CHECK(rc.counter == wm.top);        // the counter advanced exactly to the model's top
			have_auth = 1;
			last_nonce = nonce;
		}
		free(pkt); free(pt_out); free(ref_pt);
	}
	wm_free(&wm);
	return 0;
}
