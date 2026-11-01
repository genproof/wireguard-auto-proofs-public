// SPDX-License-Identifier: GPL-2.0
// Law `transport_len`: data-packet length / padding is validated before the payload is accessed; a
// too-short or malformed-length data packet is rejected, not over-read.
//
// A received packet of ANY total length `tot` (drawn around the 4-byte header and the 32-byte minimum, up to a few
// hundred, and of any size; the run ends above PTRDIFF_MAX - 32, DEVIATIONS.md L13) and ANY type word, held in a
// buffer of EXACTLY `tot` bytes (the quickproof convention: a one-byte overread is then caught by ASan / the
// CompCert interpreter).  The harness runs the receive.c length
// gate (validate_header_len, extracted in patch/data_header.c) and, when it admits a MESSAGE_DATA packet, the
// payload read that decrypt_packet performs (the real chacha20poly1305_decrypt over exactly the encrypted_data
// region [sizeof(message_data), tot)).
// Shadow model: a MESSAGE_DATA packet is admitted exactly when tot >= MESSAGE_MINIMUM_LENGTH (= message_data_len(0)
//   = sizeof(message_data) + 16); the encrypted_data region is then tot - sizeof(message_data) bytes (>= 16, room
//   for the Poly1305 tag) and the plaintext is tot - sizeof(message_data) - 16 bytes.
// CHECKs:
//   - wg_validate_header_len == the model's header length (sizeof(message_data) for an admitted data packet, 0 for
//     a short or non-data packet)  [the length gate];
//   - an admitted data packet: the AEAD reads exactly [sizeof(message_data), tot) of the exact-size buffer and
//     never past it (the exact buffer + ASan/interp are the overread oracle); its verdict and plaintext == the
//     reference over the same region; the plaintext length is tot - sizeof(message_data) - 16;
//   - a rejected packet (tot < MESSAGE_MINIMUM_LENGTH, or a non-data type): the payload is never accessed.
#include "transport.h"

size_t wg_validate_header_len(u32 type, size_t len);

#define MD_HDR 16                        // sizeof(struct message_data)

int main(void)
{
	u8 key[32];
	u8 *pkt, *pt_out, *ref_pt;
	size_t tot, hl, enc_len, pt_len, expect;
	u64 nonce;
	u32 type;
	int ok, ref_ok, authentic;

	nondet_bytes(key, 32);
	nonce = draw_u64();

	// draw a total length: small, around the header (4) and the minimum (32), and up to a few hundred
	switch (nondet_u8() % 4) {
	case 0: tot = nondet_u8() % 40; break;                 // 0..39: straddles 4 and 32
	case 1: tot = 32 + nondet_u8() % 8; break;             // at / just above the minimum
	case 2: tot = nondet_u8() % 300; break;
	default: tot = draw_size(); break;
	}
	if (tot > PTRDIFF_MAX - 32)
		return 0;

	// mostly MESSAGE_DATA, sometimes another type / garbage word (the gate must still reject on length)
	switch (nondet_u8() % 4) {
	case 0: type = MESSAGE_HANDSHAKE_INITIATION; break;
	case 1: type = MESSAGE_HANDSHAKE_COOKIE; break;
	case 2: type = nondet_u32(); break;
	default: type = MESSAGE_DATA; break;
	}

	pkt = malloc(tot);                   // EXACT size: an overread of pkt is caught
	if (pkt == NULL)
		return 0;
	nondet_bytes(pkt, tot);
	if (tot >= 4)
		le32_store(pkt, type);       // set the type word when there is room for it

	// the length gate (validate_header_len), checked against an independent model of its length rules
	hl = wg_validate_header_len(type, tot);
	if (tot < sizeof(struct message_header))
		expect = 0;
	else if (type == MESSAGE_DATA && tot >= MESSAGE_MINIMUM_LENGTH)
		expect = sizeof(struct message_data);
	else if (type == MESSAGE_HANDSHAKE_INITIATION && tot == sizeof(struct message_handshake_initiation))
		expect = sizeof(struct message_handshake_initiation);
	else if (type == MESSAGE_HANDSHAKE_RESPONSE && tot == sizeof(struct message_handshake_response))
		expect = sizeof(struct message_handshake_response);
	else if (type == MESSAGE_HANDSHAKE_COOKIE && tot == sizeof(struct message_handshake_cookie))
		expect = sizeof(struct message_handshake_cookie);
	else
		expect = 0;
	CHECK(hl == expect);

	if (type != MESSAGE_DATA || hl == 0) {
		// rejected: decrypt_packet is never reached, the payload is never accessed
		free(pkt);
		return 0;
	}

	// an admitted data packet: decrypt_packet reads exactly the encrypted_data region [MD_HDR, tot)
	enc_len = tot - MD_HDR;              // >= 16 because tot >= MESSAGE_MINIMUM_LENGTH = 32
	CHECK(enc_len >= 16);
	pt_len = enc_len - 16;

	// half the time make the payload a real ciphertext of exactly pt_len bytes, so the AEAD reads all of it
	authentic = nondet_u8() & 1;
	if (authentic) {
		u8 *pt = malloc(pt_len);
		if (pt == NULL) { free(pkt); return 0; }
		nondet_bytes(pt, pt_len);
		chacha20poly1305_encrypt(pkt + MD_HDR, pt, pt_len, NULL, 0, nonce, key);
		free(pt);
	}

	pt_out = malloc(pt_len);
	ref_pt = malloc(pt_len);
	if (pt_out == NULL || ref_pt == NULL) { free(pkt); free(pt_out); free(ref_pt); return 0; }

	ok = chacha20poly1305_decrypt(pt_out, pkt + MD_HDR, enc_len, NULL, 0, nonce, key);
	ref_ok = ref_aead_decrypt(ref_pt, pkt + MD_HDR, enc_len, NULL, 0, nonce, key);
	CHECK(ok == ref_ok);
	if (ok)
		CHECK(bytes_eq(pt_out, ref_pt, pt_len));   // plaintext == reference, exactly pt_len bytes
	if (authentic)
		CHECK(ok);                                 // an authentic packet of this exact length decrypts
	free(pkt); free(pt_out); free(ref_pt);
	return 0;
}
