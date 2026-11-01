// Law ae_split_blake2s: For any output length 1..32, any key of 0..32 bytes and any message (up to PTRDIFF_MAX
// bytes), the one-call blake2s() gives the same hash as blake2s_init (no key) or blake2s_init_key, blake2s_update
// over the message in any pieces of any lengths (empty pieces too), and blake2s_final.
#include "wg_laws.h"

int main(void) {
	// Choose the inputs: any output length and key length in the documented ranges, any key, any message
	size_t out_len = 1 + upto(BLAKE2S_HASH_SIZE - 1);
	size_t key_len = upto(BLAKE2S_KEY_SIZE);
	u8 key[BLAKE2S_KEY_SIZE];
	nondet_bytes(key, sizeof key);
	size_t len = upto(PTRDIFF_MAX);
	u8 *message = any_bytes(len);
	if (message == NULL)
		return 0;
	// In one call. include/crypto/blake2s.h: "@outlen: length of output hash value in bytes, at most
	// BLAKE2S_HASH_SIZE"; "@keylen: the key length in bytes (at most BLAKE2S_KEY_SIZE), or 0 for an unkeyed hash"
	u8 whole[BLAKE2S_HASH_SIZE], pieces[BLAKE2S_HASH_SIZE];
	blake2s(key_len == 0 ? NULL : key, key_len, message, len, whole, out_len);
	// In any pieces. include/crypto/blake2s.h, blake2s_update: "This can be called any number of times."; RFC 7693,
	// 3.3: "Key and data input are split and padded into "dd" message blocks".
	struct blake2s_ctx ctx;
	if (key_len == 0)
		blake2s_init(&ctx, out_len);
	else
		blake2s_init_key(&ctx, out_len, key, key_len);
	size_t done = 0;
	while (done < len || nondet_u8() != 0) {
		size_t take = upto(len - done);
		blake2s_update(&ctx, message + done, take);
		done += take;
	}
	blake2s_final(&ctx, pieces);
	// Check
	gp_assert(bytes_eq(whole, pieces, out_len));
	return 0;
}
