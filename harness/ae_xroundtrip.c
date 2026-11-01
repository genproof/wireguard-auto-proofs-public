// Law ae_xroundtrip: For any message (up to PTRDIFF_MAX - 16 bytes), any associated data (up to PTRDIFF_MAX bytes),
// any 24-byte nonce and any 32-byte key, xchacha20poly1305_encrypt writes the message's length + 16 bytes, and
// xchacha20poly1305_decrypt of exactly those bytes with the same associated data, nonce and key returns true and
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
	u8 key[CHACHA20POLY1305_KEY_SIZE], nonce[XCHACHA20POLY1305_NONCE_SIZE];
	nondet_bytes(key, sizeof key);
	nondet_bytes(nonce, sizeof nonce);
	// Encrypt, then decrypt. draft-irtf-cfrg-xchacha-03, 2: "Calculate a subkey from the first 16 bytes of the
	// nonce and the key, using HChaCha20", then "Use the subkey and remaining 8 bytes of the nonce ... with
	// AEAD_CHACHA20_POLY1305 from [RFC8439] as normal"; RFC 8439, 2.8: "The message is authenticated if and only
	// if the tags match."
	xchacha20poly1305_encrypt(sealed, message, len, ad, ad_len, nonce, key);
	bool ok = xchacha20poly1305_decrypt(opened, sealed, len + CHACHA20POLY1305_AUTHTAG_SIZE, ad, ad_len, nonce, key);
	// Check
	gp_assert(ok != 0);
	gp_assert(bytes_eq(opened, message, len));
	return 0;
}
