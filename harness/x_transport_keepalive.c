// SPDX-License-Identifier: GPL-2.0
// Law `transport_keepalive`: a keepalive is a data packet with a ZERO-length payload; it obeys the same
// auth + counter rules as a normal data packet (authenticated, counter-validated), it delivers no plaintext, and
// a truly empty / tag-less packet is handled without over-reading.
//
// One receiving keypair and a sequence of ANY length of keepalive-shaped packets:
//   - an authentic keepalive: the real chacha20poly1305_encrypt of the EMPTY plaintext under the key at a drawn
//     nonce -> encrypted_data is exactly the 16-byte Poly1305 tag (total length = MESSAGE_MINIMUM_LENGTH);
//   - that keepalive with its tag corrupted (bad tag);
//   - a replay of an authentic keepalive's nonce;
//   - a tag-less packet: encrypted_data of 0..15 bytes, with no room for a tag.
// The harness runs receive.c's two stages (as transport_order), on an EXACT-size encrypted_data buffer.
// Shadow model: ref_aead_decrypt over the empty payload for the tag; the window model for the counter.
// CHECKs after every packet:
//   - ok == (the reference tag verifies);  a tag-less packet (enc_len < 16) is rejected, ok == 0, never over-read;
//   - BAD TAG / tag-less => the replay counter is byte-for-byte unchanged, nothing delivered;
//   - authentic keepalive => reaches wg_counter_validate, verdict == the window model, counter advances to top,
//     and on acceptance the delivered plaintext length is 0 (a keepalive carries no data);
//   - an authentic keepalive follows exactly the same accept/replay rule as a full data packet (same window).
#include "transport.h"

#define MD_HDR 16

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
		size_t enc_len, tot, pt_len, j;
		u64 nonce;
		int kind, ok, ref_ok;

		kind = nondet_u8() % 4;
		if (kind == 3)
			enc_len = nondet_u8() % 16;    // 0..15: a tag-less / truncated packet
		else
			enc_len = 16;                 // a keepalive: the tag only, empty ciphertext
		tot = MD_HDR + enc_len;
		pt_len = enc_len >= 16 ? enc_len - 16 : 0;

		pkt = malloc(tot);                    // EXACT size
		pt_out = malloc(pt_len);
		ref_pt = malloc(pt_len);
		if (pkt == NULL || (pt_len && (pt_out == NULL || ref_pt == NULL))) {
			free(pkt); free(pt_out); free(ref_pt);
			break;
		}

		nonce = (kind == 2 && have_auth) ? last_nonce : (wm.top + (u64)(nondet_u32() % 64) - 16);
		le32_store(pkt, MESSAGE_DATA);
		le32_store(pkt + 4, nondet_u32());
		le64_store(pkt + 8, nonce);

		if (kind == 0 || kind == 1 || kind == 2) {
			// authentic keepalive: AEAD-encrypt the EMPTY plaintext -> 16-byte tag in encrypted_data
			chacha20poly1305_encrypt(pkt + MD_HDR, NULL, 0, NULL, 0, nonce, key);
			if (kind == 1) {
				j = nondet_u8() % 16;
				pkt[MD_HDR + j] ^= (u8)(1 + nondet_u8() % 255);
			}
		} else {
			nondet_bytes(pkt + MD_HDR, enc_len);
		}

		// ===== the receive pipeline, in order =====
		rc_take(&snap, &rc);
		ok = chacha20poly1305_decrypt(pt_out, pkt + MD_HDR, enc_len, NULL, 0, nonce, key);
		ref_ok = ref_aead_decrypt(ref_pt, pkt + MD_HDR, enc_len, NULL, 0, nonce, key);
		CHECK(ok == ref_ok);

		if (!ok) {
			CHECK(rc_same(&snap, &rc));            // bad tag / tag-less: counter untouched, nothing consumed
		} else {
			int pred = wm_accepts(&wm, nonce);
			int r = wg_counter_validate(&rc, nonce);
			CHECK(r == pred);
			if (r) {
				CHECK(pt_len == 0);           // a keepalive delivers no plaintext
				if (!wm_commit(&wm, nonce)) {
					free(pkt); free(pt_out); free(ref_pt);
					break;
				}
			}
			CHECK(rc.counter == wm.top);
			have_auth = 1;
			last_nonce = nonce;
		}
		free(pkt); free(pt_out); free(ref_pt);
	}
	wm_free(&wm);
	return 0;
}
