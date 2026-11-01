// Law ae_roundtrip: For any message (up to PTRDIFF_MAX - 16 bytes), any associated data (up to PTRDIFF_MAX bytes),
// any 64-bit nonce and any 32-byte key, chacha20poly1305_encrypt writes the message's length + 16 bytes, and
// chacha20poly1305_decrypt of exactly those bytes with the same associated data, nonce and key returns true and
// gives back exactly the message (each buffer an object of its own; a failed malloc ends the run).
#include "wg_laws.h"

int main(void) {
	// Choose the inputs: any message, associated data, nonce and key
	size_t len = upto(PTRDIFF_MAX - CHACHA20POLY1305_AUTHTAG_SIZE);
	size_t ad_len = upto(PTRDIFF_MAX);
	u8 *message = any_bytes(len);
	u8 *ad = any_bytes(ad_len);
	u8 *sealed = malloc(len + CHACHA20POLY1305_AUTHTAG_SIZE);
	u8 *opened = any_bytes(len);
	if (message == NULL || ad == NULL || sealed == NULL || opened == NULL)
		return 0;
	u8 key[CHACHA20POLY1305_KEY_SIZE];
	nondet_bytes(key, sizeof key);
	u64 nonce = any_u64();
	// Encrypt, then decrypt. lib/crypto/chacha20poly1305.c: "This is an implementation of the ChaCha20Poly1305
	// AEAD construction. Information: https://tools.ietf.org/html/rfc8439"; RFC 8439, 2.8: "The calculated tag is
	// bitwise compared to the received tag. The message is authenticated if and only if the tags match."
	chacha20poly1305_encrypt(sealed, message, len, ad, ad_len, nonce, key);
	bool ok = chacha20poly1305_decrypt(opened, sealed, len + CHACHA20POLY1305_AUTHTAG_SIZE, ad, ad_len, nonce, key);
	// Check
	gp_assert(ok != 0);
	gp_assert(bytes_eq(opened, message, len));
	return 0;
}
