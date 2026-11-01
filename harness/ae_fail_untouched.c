// Law ae_fail_untouched: For any bytes as ciphertext (any length up to PTRDIFF_MAX), any associated data (up to
// PTRDIFF_MAX bytes), any nonce and any 32-byte key, a chacha20poly1305_decrypt or xchacha20poly1305_decrypt that
// returns false leaves every byte of its output buffer (an object of max(length - 16, 0) bytes) as it was.  The
// ciphertext is built as the encryption of any message under that associated data, nonce and key, then any bytes
// changed and any prefix kept: this reaches every byte string, and lets runs reach the tag check (a failed malloc
// ends the run).
#include "wg_laws.h"

int main(void) {
	// Choose the inputs: either AEAD, any message, associated data, nonce, key
	int extended = nondet_u8() & 1;
	size_t len = upto(PTRDIFF_MAX - CHACHA20POLY1305_AUTHTAG_SIZE);
	size_t ad_len = upto(PTRDIFF_MAX);
	u8 *message = any_bytes(len);
	u8 *ad = any_bytes(ad_len);
	u8 *sealed = malloc(len + CHACHA20POLY1305_AUTHTAG_SIZE);
	if (message == NULL || ad == NULL || sealed == NULL)
		return 0;
	u8 key[CHACHA20POLY1305_KEY_SIZE], xnonce[XCHACHA20POLY1305_NONCE_SIZE];
	nondet_bytes(key, sizeof key);
	nondet_bytes(xnonce, sizeof xnonce);
	u64 nonce = any_u64();
	if (extended)
		xchacha20poly1305_encrypt(sealed, message, len, ad, ad_len, xnonce, key);
	else
		chacha20poly1305_encrypt(sealed, message, len, ad, ad_len, nonce, key);
	// Any bytes changed to any values, then any prefix of it, as an object of its own
	while (nondet_u8() != 0)
		sealed[upto(len + CHACHA20POLY1305_AUTHTAG_SIZE - 1)] = nondet_u8();
	size_t given = upto(len + CHACHA20POLY1305_AUTHTAG_SIZE);
	size_t out_len = given < CHACHA20POLY1305_AUTHTAG_SIZE ? 0 : given - CHACHA20POLY1305_AUTHTAG_SIZE;
	u8 *ciphertext = copy_of(sealed, given);
	u8 *out = any_bytes(out_len);
	if (ciphertext == NULL || out == NULL)
		return 0;
	u8 *before = copy_of(out, out_len);
	if (before == NULL)
		return 0;
	// Decrypt. RFC 8439, 2.8: "The message is authenticated if and only if the tags match."; lib/crypto/
	// chacha20poly1305.c: "ret = crypto_memneq(b.block0, src + dst_len, POLY1305_DIGEST_SIZE); if (likely(!ret))
	// chacha20_crypt(chacha_state, dst, src, dst_len);"
	bool ok;
	if (extended)
		ok = xchacha20poly1305_decrypt(out, ciphertext, given, ad, ad_len, xnonce, key);
	else
		ok = chacha20poly1305_decrypt(out, ciphertext, given, ad, ad_len, nonce, key);
	// Check
	if (ok == 0)
		gp_assert(bytes_eq(out, before, out_len));
	return 0;
}
