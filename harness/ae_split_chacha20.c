// Law ae_split_chacha20: For any 32-byte key, any 16-byte block counter and nonce and any message (up to PTRDIFF_MAX
// bytes), chacha20_crypt over the whole message writes the same bytes as chacha20_crypt over it in any pieces, all
// but the last a multiple of 64 bytes long (empty pieces too), each piece continuing the state of the one before.
#include "wg_laws.h"

int main(void) {
	// Choose the inputs: any key, counter and nonce, any message
	u32 key[CHACHA_KEY_WORDS];
	for (size_t i = 0; i < CHACHA_KEY_WORDS; i++)
		key[i] = nondet_u32();
	u8 iv[CHACHA_IV_SIZE];
	nondet_bytes(iv, sizeof iv);
	size_t len = upto(PTRDIFF_MAX);
	u8 *message = any_bytes(len);
	u8 *whole = malloc(len);
	u8 *pieces = malloc(len);
	if (message == NULL || whole == NULL || pieces == NULL)
		return 0;
	// In one call
	struct chacha_state one, many;
	chacha_init(&one, key, iv);
	chacha20_crypt(&one, whole, message, len);
	// In pieces: each the rest, or any multiple of 64 bytes no longer than the rest. RFC 8439, 2.4: "ChaCha20
	// successively calls the ChaCha20 block function, with the same key and nonce, and with successively increasing
	// block counter parameters"; lib/crypto/chacha.c: "Process longer messages in chunks that are a multiple of
	// CHACHA_BLOCK_SIZE, so that the keystream continues correctly from one chunk to the next."
	chacha_init(&many, key, iv);
	size_t done = 0;
	while (done < len) {
		size_t take = len - done;
		if (nondet_u8() != 0)
			take = CHACHA_BLOCK_SIZE * upto(take / CHACHA_BLOCK_SIZE);
		chacha20_crypt(&many, pieces + done, message + done, take);
		done += take;
	}
	// Check
	gp_assert(bytes_eq(whole, pieces, len));
	return 0;
}
