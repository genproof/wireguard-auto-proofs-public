#!/usr/bin/env python3
"""wgpatch.py: the patch of the code under test, run at the root of a tree that holds the unmodified upstream files
(patch/check.sh shows that it turns them into this repository's files).

First the two patches of patch/series/ (rows P22, P23 of DEVIATIONS.md): patches 4/5 "lib/crypto: poly1305: Take a
size_t length in poly1305_update()" and 5/5 "lib/crypto: chacha: Take a size_t length in chacha_crypt()" of the
lib/crypto series "lib/crypto: Handle large lengths in poly1305 and chacha20poly1305" (the four files they touch are
byte-identical between the series' base and the pin; patches 1-3 of the series change only the arm64, MIPS and
RISC-V poly1305 glue code, which is not built here).  They are applied VERBATIM: every hunk must match at exactly its
stated line with its exact context (no offset, no fuzz), and every patched file must hash to the git blob of the
patch's `index` line before and after (apply_series).  Their lines carry no QUICKPROOF marker, because they are the
series' text itself.  They change results only where upstream is wrong (patch/tests/big.sh, patch/diff.sh).

Then the idiom hunks P01-P21; each is marked QUICKPROOF Pnn in the patched source and changes no result:
patch/diff.sh runs the unmodified and the patched code on the same inputs (ASan/UBSan) and compares every output
byte and return value; patch/diff.sh --coverage shows that every hunk is executed.

Kinds of hunks:
  - goto: VST has no rule for goto.  A function whose gotos all jump forward to one label before the common exit
    code becomes `do { ... } while (0)` with `break` for `goto` (no goto is inside a loop or switch; checked);
    consume_response has two labels (fail, out) and gets two nested blocks and a flag.
  - type punning: VST reasons about typed memory; stores of u64/u32 into byte arrays, byte copies between u8 and
    u32 arrays, and a union read through another member are written element by element with the kernel's own
    byte-order helpers (little endian, as x86_64).
  - struct copies and compound literals: VST has no struct assignment; CompCert rejects the empty compound
    literal `(struct T){}` (C23).  Written as element loops / memset.
  - the scatterlist AEAD functions (data path, not called by the handshake) are compiled out.
Also checked here: patch/counter_validate.c still holds upstream's counter_validate byte for byte (S19),
patch/data_header.c holds upstream's validate_header_len with exactly the three substitutions of its reduction
(S24), and patch/wg_shim.c holds upstream's wg_birthdate_has_expired (S18), so that the patch fails if the pin
and the extracted text diverge.
"""
import re
import sys


def read(p):
    return open(p).read()


def write(p, s):
    open(p, 'w').write(s)


def sub1(s, old, new, what):
    n = s.count(old)
    if n != 1:
        sys.exit('wgpatch: %s: expected 1 occurrence, found %d' % (what, n))
    return s.replace(old, new)


def function(s, sig):
    """(start, end) of the function whose definition starts with `sig` (end: after the closing '\\n}\\n')."""
    a = s.find(sig)
    if a < 0 or s.count(sig) != 1:
        sys.exit('wgpatch: function %r not found exactly once' % sig)
    b = s.index('\n}\n', a) + 3
    return a, b


def git_blob(data):
    """the git blob id (sha1) of `data` (bytes)"""
    import hashlib
    return hashlib.sha1(b'blob %d\0' % len(data) + data).hexdigest()


def apply_series(series_dir='patch/series'):
    """P22, P23: apply the series' patches 4/5 and 5/5 verbatim (git format-patch files, in name order).  Strict:
    each hunk's old lines (context and removed) must be exactly the file's lines at the hunk's stated position (no
    offset, no fuzz), and each file's git blob before and after must match the abbreviated ids of the patch's
    `index` line, so the result is byte for byte the series' post-image."""
    import glob
    import os
    files = sorted(glob.glob(os.path.join(series_dir, '*.patch')))
    if len(files) != 2:
        sys.exit('wgpatch: series: expected 2 patches in %s, found %d' % (series_dir, len(files)))
    for pf in files:
        text = open(pf).read()
        body = text[text.index('\ndiff --git ') + 1:]
        body = body[:body.index('\n-- \n') + 1] if '\n-- \n' in body else body
        for sec in re.split(r'(?m)^(?=diff --git )', body):
            if not sec.startswith('diff --git '):
                continue
            m = re.search(r'(?m)^index ([0-9a-f]+)\.\.([0-9a-f]+)', sec)
            f = re.search(r'(?m)^\+\+\+ b/(\S+)$', sec).group(1)
            if re.search(r'(?m)^--- a/(\S+)$', sec).group(1) != f:
                sys.exit('wgpatch: series: %s: renames are not expected' % pf)
            raw = open(f, 'rb').read()
            if not git_blob(raw).startswith(m.group(1)):
                sys.exit('wgpatch: series: %s: %s is not the pre-image %s' % (pf, f, m.group(1)))
            lines = raw.decode().split('\n')
            out, pos = [], 0
            for h in re.finditer(r'(?ms)^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@[^\n]*\n(.*?)(?=^@@ |\Z)', sec):
                start, cnt = int(h.group(1)), int(h.group(2) or 1)
                hl = h.group(5).split('\n')
                if hl and hl[-1] == '':
                    hl = hl[:-1]
                old = [x[1:] for x in hl if x[:1] in (' ', '-')]
                new = [x[1:] for x in hl if x[:1] in (' ', '+')]
                if any(x[:1] not in (' ', '-', '+') for x in hl) or len(old) != cnt:
                    sys.exit('wgpatch: series: %s: %s: malformed hunk at -%d' % (pf, f, start))
                a = start - 1
                if a < pos or lines[a:a + cnt] != old:
                    sys.exit('wgpatch: series: %s: %s: hunk at -%d does not match exactly' % (pf, f, start))
                out += lines[pos:a] + new
                pos = a + cnt
            out += lines[pos:]
            res = '\n'.join(out).encode()
            if not git_blob(res).startswith(m.group(2)):
                sys.exit('wgpatch: series: %s: %s is not the post-image %s' % (pf, f, m.group(2)))
            open(f, 'wb').write(res)


def goto_to_break(s, sig, after, label, pid, why):
    """In the function `sig`: open `do {` after the line `after`, turn every `goto <label>;` into `break;`, and
    close the block at `<label>:`.  Checks that no goto sits inside a loop or switch of the block."""
    a, b = function(s, sig)
    f = s[a:b]
    i = f.index(after) + len(after)
    j = f.index('\n%s:\n' % label)
    body = f[i:j]
    # every loop/switch in the block must be free of gotos: find each loop header and its braced body
    for m in re.finditer(r'\b(for|while|switch)\s*\(', body):
        k = body.index('{', m.end()) if '{' in body[m.end():m.end() + 200] else None
        seg = body[m.start():]
        if k is not None:
            depth, t = 0, k
            while True:
                if body[t] == '{':
                    depth += 1
                elif body[t] == '}':
                    depth -= 1
                    if depth == 0:
                        break
                t += 1
            seg = body[m.start():t + 1]
        else:
            seg = body[m.start():body.index(';', m.end()) + 1]
        if re.search(r'\bgoto\s+\w+\s*;', seg):
            sys.exit('wgpatch: %s: goto inside a loop or switch' % pid)
    n = body.count('goto %s;' % label)
    if n == 0 or len(re.findall(r'\bgoto\s+\w+\s*;', body)) != n:
        sys.exit('wgpatch: %s: unexpected gotos' % pid)
    body = body.replace('goto %s;' % label, 'break;')
    if not body.startswith('\n'):
        body = '\n' + body
    f = (f[:i] + '\n\t/* QUICKPROOF %s: %s */\n\tdo {' % (pid, why) + body +
         '\n\t} while (0); /* QUICKPROOF %s: was the label `%s:` */\n' % (pid, label) + f[j + len('\n%s:\n' % label):])
    return s[:a] + f + s[b:]


GOTO_WHY = '`goto out` is `break` out of this block (VST has no goto); same statements in the same order'


def patch_noise(p):
    s = read(p)
    # P01 kdf: the three early exits are nested ifs
    old = '''	hmac(secret, data, chaining_key, data_len, NOISE_HASH_LEN);

	if (!first_dst || !first_len)
		goto out;

	/* Expand first key: key = secret, data = 0x1 */
	output[0] = 1;
	hmac(output, output, secret, 1, BLAKE2S_HASH_SIZE);
	memcpy(first_dst, output, first_len);

	if (!second_dst || !second_len)
		goto out;

	/* Expand second key: key = secret, data = first-key || 0x2 */
	output[BLAKE2S_HASH_SIZE] = 2;
	hmac(output, output, secret, BLAKE2S_HASH_SIZE + 1, BLAKE2S_HASH_SIZE);
	memcpy(second_dst, output, second_len);

	if (!third_dst || !third_len)
		goto out;

	/* Expand third key: key = secret, data = second-key || 0x3 */
	output[BLAKE2S_HASH_SIZE] = 3;
	hmac(output, output, secret, BLAKE2S_HASH_SIZE + 1, BLAKE2S_HASH_SIZE);
	memcpy(third_dst, output, third_len);

out:
'''
    new = '''	hmac(secret, data, chaining_key, data_len, NOISE_HASH_LEN);

	/* QUICKPROOF P01: the three `goto out` are nested ifs (VST has no goto); same statements in the same order */
	if (first_dst && first_len) {
	/* Expand first key: key = secret, data = 0x1 */
	output[0] = 1;
	hmac(output, output, secret, 1, BLAKE2S_HASH_SIZE);
	memcpy(first_dst, output, first_len);

	if (second_dst && second_len) {
	/* Expand second key: key = secret, data = first-key || 0x2 */
	output[BLAKE2S_HASH_SIZE] = 2;
	hmac(output, output, secret, BLAKE2S_HASH_SIZE + 1, BLAKE2S_HASH_SIZE);
	memcpy(second_dst, output, second_len);

	if (third_dst && third_len) {
	/* Expand third key: key = secret, data = second-key || 0x3 */
	output[BLAKE2S_HASH_SIZE] = 3;
	hmac(output, output, secret, BLAKE2S_HASH_SIZE + 1, BLAKE2S_HASH_SIZE);
	memcpy(third_dst, output, third_len);
	}
	}
	} /* QUICKPROOF P01: was the label `out:` */

'''
    s = sub1(s, old, new, 'P01 kdf')
    # P02 tai64n_now: u64/u32 stores into the byte array -> byte stores, big endian (what cpu_to_be* + the store do)
    old = '''	*(__be64 *)output = cpu_to_be64(0x400000000000000aULL + now.tv_sec);
	*(__be32 *)(output + sizeof(__be64)) = cpu_to_be32(now.tv_nsec);
'''
    new = '''	/* QUICKPROOF P02: the u64/u32 stores through casts of the byte array are big-endian byte stores (VST: typed memory) */
	put_unaligned_be64(0x400000000000000aULL + now.tv_sec, output);
	put_unaligned_be32(now.tv_nsec, output + sizeof(__be64));
'''
    s = sub1(s, old, new, 'P02 tai64n_now')
    # P03..P05, P07: goto out -> break
    s = goto_to_break(s, 'wg_noise_handshake_create_initiation(struct message_handshake_initiation *dst,\n\t\t\t\t     struct noise_handshake *handshake)\n{',
                      '\tdown_write(&handshake->lock);\n', 'out', 'P03', GOTO_WHY)
    s = goto_to_break(s, 'wg_noise_handshake_consume_initiation(struct message_handshake_initiation *src,\n\t\t\t\t      struct wg_device *wg)\n{',
                      '\tdown_read(&wg->static_identity.lock);\n', 'out', 'P04', GOTO_WHY)
    s = goto_to_break(s, 'bool wg_noise_handshake_create_response(struct message_handshake_response *dst,',
                      '\tdown_write(&handshake->lock);\n', 'out', 'P05', GOTO_WHY)
    s = goto_to_break(s, 'bool wg_noise_handshake_begin_session(struct noise_handshake *handshake,',
                      '\tdown_write(&handshake->lock);\n', 'out', 'P07', GOTO_WHY)
    # P06 consume_response: `goto out` (before the lookup succeeded) leaves the outer block, `goto fail` the inner
    # block; the fail path (wg_peer_put) runs exactly when the inner block did not reach its end (flag)
    a, b = function(s, 'wg_noise_handshake_consume_response(struct message_handshake_response *src,\n\t\t\t\t    struct wg_device *wg)\n{')
    f = s[a:b]
    f = sub1(f, '\tu8 preshared_key[NOISE_SYMMETRIC_KEY_LEN];\n',
             '\tu8 preshared_key[NOISE_SYMMETRIC_KEY_LEN];\n\tbool quickproof_success = false; /* QUICKPROOF P06 */\n', 'P06 decl')
    f = sub1(f, '\tdown_read(&wg->static_identity.lock);\n\n\tif (unlikely(!wg->static_identity.has_identity))\n\t\tgoto out;\n',
             '\tdown_read(&wg->static_identity.lock);\n\n'
             '\t/* QUICKPROOF P06: `goto out` is `break` out of the outer block, `goto fail` `break` out of the inner block,\n'
             '\t * and the fail path runs when the inner block did not reach its end (VST has no goto); same statements\n'
             '\t * in the same order */\n'
             '\tdo {\n\tif (unlikely(!wg->static_identity.has_identity))\n\t\tbreak;\n', 'P06 open outer')
    f = sub1(f, '\tif (unlikely(!handshake))\n\t\tgoto out;\n', '\tif (unlikely(!handshake))\n\t\tbreak;\n', 'P06 lookup')
    f = sub1(f, '\tup_read(&handshake->lock);\n\n\tif (state != HANDSHAKE_CREATED_INITIATION)\n\t\tgoto fail;\n',
             '\tup_read(&handshake->lock);\n\n\tdo {\n\tif (state != HANDSHAKE_CREATED_INITIATION)\n\t\tbreak;\n', 'P06 open inner')
    f = sub1(f, '''	ret_peer = peer;
	goto out;

fail:
	wg_peer_put(peer);
out:
''', '''	ret_peer = peer;
	quickproof_success = true;
	} while (0); /* QUICKPROOF P06: was the jump to out, then the label `fail:` */
	if (!quickproof_success)
		wg_peer_put(peer);
	} while (0); /* QUICKPROOF P06: was the label `out:` */
''', 'P06 close')
    if f.count('goto fail;') != 4:
        sys.exit('wgpatch: P06: expected 4 goto fail')
    f = f.replace('goto fail;', 'break;')
    if re.search(r'\bgoto\s+\w+\s*;', f):
        sys.exit('wgpatch: P06: goto left')
    s = s[:a] + f + s[b:]
    if re.search(r'\bgoto\s+\w+\s*;', s):
        sys.exit('wgpatch: noise.c: goto left')
    write(p, s)


def patch_cookie(p):
    s = read(p)
    s = goto_to_break(s, 'enum cookie_mac_state wg_cookie_validate_packet(struct cookie_checker *checker,',
                      '\tu8 cookie[COOKIE_LEN];\n', 'out', 'P08', GOTO_WHY)
    s = goto_to_break(s, 'void wg_cookie_message_consume(struct message_handshake_cookie *src,',
                      '\t\treturn;\n', 'out', 'P09', GOTO_WHY)
    if re.search(r'\bgoto\s+\w+\s*;', s):
        sys.exit('wgpatch: cookie.c: goto left')
    write(p, s)


def check_counter(tree_receive, unit):
    """S19: patch/counter_validate.c holds upstream's counter_validate byte for byte."""
    src = read(tree_receive)
    a = src.index('/* This is RFC6479, a replay detection bitmap algorithm that avoids bitshifts */')
    b = src.index('#include "selftest/counter.c"')
    up = src[a:b].rstrip('\n') + '\n'
    u = read(unit)
    x = u.index('/* ---- BEGIN UPSTREAM receive.c ---- */\n') + len('/* ---- BEGIN UPSTREAM receive.c ---- */\n')
    y = u.index('/* ---- END UPSTREAM receive.c ---- */')
    if u[x:y] != up:
        sys.exit('wgpatch: patch/counter_validate.c differs from counter_validate in receive.c at the pin')


def check_data_header(tree_receive, unit):
    """S24: patch/data_header.c holds upstream's validate_header_len with exactly three substitutions: the
    signature (non-static, the two skb accessors as parameters), SKB_TYPE_LE32(skb) -> type, skb->len -> len."""
    a, b = function(read(tree_receive), 'static size_t validate_header_len(struct sk_buff *skb)\n')
    up = read(tree_receive)[a:b]
    up = sub1(up, 'static size_t validate_header_len(struct sk_buff *skb)\n',
              'size_t wg_validate_header_len(u32 type, size_t len)\n', 'S24 signature')
    if up.count('SKB_TYPE_LE32(skb)') != 4 or up.count('skb->len') != 5:
        sys.exit('wgpatch: S24: validate_header_len in receive.c no longer reads SKB_TYPE_LE32(skb) 4x, skb->len 5x')
    up = up.replace('SKB_TYPE_LE32(skb)', 'type').replace('skb->len', 'len')
    if 'skb' in up:
        sys.exit('wgpatch: S24: validate_header_len in receive.c reads the skb beyond the two reduced accessors')
    u = read(unit)
    x = u.index('/* ---- BEGIN REDUCED receive.c ---- */\n') + len('/* ---- BEGIN REDUCED receive.c ---- */\n')
    y = u.index('/* ---- END REDUCED receive.c ---- */')
    if u[x:y] != up:
        sys.exit('wgpatch: patch/data_header.c differs from the reduction of validate_header_len in receive.c at the pin')


def patch_counter(p):
    s = read(p)
    s = goto_to_break(s, 'static bool counter_validate(struct noise_replay_counter *counter, u64 their_counter)',
                      '\tspin_lock_bh(&counter->lock);\n', 'out', 'P10', GOTO_WHY)
    write(p, s)


def check_timers(unit):
    """S18: wg_birthdate_has_expired in patch/wg_shim.c is upstream's body (drivers/net/wireguard/timers.c)."""
    upstream = '''bool wg_birthdate_has_expired(u64 birthday_nanoseconds, u64 expiration_seconds)
{
	return (s64)(birthday_nanoseconds + expiration_seconds * NSEC_PER_SEC)
		<= (s64)ktime_get_coarse_boottime_ns();
}
'''
    if upstream not in read(unit):
        sys.exit('wgpatch: wg_birthdate_has_expired in patch/wg_shim.c is not upstream\'s text')


def patch_blake2s(p):
    s = read(p)
    s = sub1(s, '''		memcpy(m, data, BLAKE2S_BLOCK_SIZE);
		le32_to_cpu_array(m, ARRAY_SIZE(m));
		memcpy(v, ctx->h, 32);
''', '''		/* QUICKPROOF P11: memcpy of the block into u32 m[16] + le32_to_cpu_array = 16 little-endian loads (VST: typed memory) */
		for (i = 0; i < 16; ++i)
			m[i] = get_unaligned_le32(data + 4 * i);
		/* QUICKPROOF P12: memcpy(v, ctx->h, 32) = 8 word copies (VST: typed memory) */
		for (i = 0; i < 8; ++i)
			v[i] = ctx->h[i];
''', 'P11/P12 blake2s_compress')
    s = sub1(s, '''	cpu_to_le32_array(ctx->h, ARRAY_SIZE(ctx->h));
	memcpy(out, ctx->h, ctx->outlen);
''', '''	/* QUICKPROOF P13: cpu_to_le32_array + memcpy(out, ctx->h, outlen) = the first outlen bytes of the words in
	 * little-endian order (VST: typed memory); ctx->h is zeroed below either way */
	for (i = 0; i < ctx->outlen; ++i)
		out[i] = (u8)(ctx->h[i / 4] >> (8 * (i % 4)));
''', 'P13 blake2s_final')
    s = sub1(s, '''void blake2s_final(struct blake2s_ctx *ctx, u8 *out)
{
''', '''void blake2s_final(struct blake2s_ctx *ctx, u8 *out)
{
	unsigned int i; /* QUICKPROOF P13 */

''', 'P13 decl')
    write(p, s)


def patch_chacha_block(p):
    s = read(p)
    s = sub1(s, '''	struct chacha_state permuted_state = *state;
	int i;

	chacha_permute(&permuted_state, nrounds);
''', '''	struct chacha_state permuted_state;
	int i;

	/* QUICKPROOF P14: the struct copy `permuted_state = *state` word by word (VST has no struct assignment) */
	for (i = 0; i < CHACHA_STATE_WORDS; i++)
		permuted_state.x[i] = state->x[i];

	chacha_permute(&permuted_state, nrounds);
''', 'P14 chacha_block_generic')
    s = sub1(s, '''	struct chacha_state permuted_state = *state;

	chacha_permute(&permuted_state, nrounds);

	memcpy(&out[0], &permuted_state.x[0], 16);
	memcpy(&out[4], &permuted_state.x[12], 16);
''', '''	struct chacha_state permuted_state;
	int i; /* QUICKPROOF P15 */

	/* QUICKPROOF P15: the struct copy word by word (VST has no struct assignment) */
	for (i = 0; i < CHACHA_STATE_WORDS; i++)
		permuted_state.x[i] = state->x[i];

	chacha_permute(&permuted_state, nrounds);

	/* QUICKPROOF P15: the two 16-byte memcpy between u32 arrays word by word (VST: typed memory) */
	for (i = 0; i < 4; i++) {
		out[i] = permuted_state.x[i];
		out[4 + i] = permuted_state.x[12 + i];
	}
''', 'P15 hchacha_block_generic')
    write(p, s)


def patch_aead(p):
    whole = read(p)
    cut = whole.index('static\nbool chacha20poly1305_crypt_sg_inplace(')
    s, tail = whole[:cut], whole[cut:]   # P16/P17 apply to the functions before the scatterlist code
    # P16: the nonce block `__le64 iv[2]` read through (u8 *) -> a byte array with little-endian stores (twice)
    old = '''	struct chacha_state chacha_state;
	u32 k[CHACHA_KEY_WORDS];
	__le64 iv[2];
'''
    new = '''	struct chacha_state chacha_state;
	u32 k[CHACHA_KEY_WORDS];
	u8 iv[16]; /* QUICKPROOF P16: was __le64 iv[2], read through (u8 *)iv (VST: typed memory) */
'''
    if s.count(old) != 2:
        sys.exit('wgpatch: P16: expected 2 declarations')
    s = s.replace(old, new)
    old = '''	iv[0] = 0;
	iv[1] = cpu_to_le64(nonce);

	chacha_init(&chacha_state, k, (u8 *)iv);
'''
    new = '''	/* QUICKPROOF P16: iv[0] = 0; iv[1] = cpu_to_le64(nonce) as bytes */
	put_unaligned_le64(0, iv);
	put_unaligned_le64(nonce, iv + 8);

	chacha_init(&chacha_state, k, iv);
'''
    if s.count(old) != 2:
        sys.exit('wgpatch: P16: expected 2 initialisations')
    s = s.replace(old, new)
    # P17: the union b (block0 / mac / lens) -> a byte array; the lengths stored little endian into it
    s = sub1(s, '''	union {
		u8 block0[POLY1305_KEY_SIZE];
		__le64 lens[2];
	} b;
''', '''	struct { /* QUICKPROOF P17: was a union with __le64 lens[2] (VST: typed memory) */
		u8 block0[POLY1305_KEY_SIZE];
	} b;
''', 'P17 encrypt union')
    s = sub1(s, '''	union {
		u8 block0[POLY1305_KEY_SIZE];
		u8 mac[POLY1305_DIGEST_SIZE];
		__le64 lens[2];
	} b;
''', '''	struct { /* QUICKPROOF P17: was a union of block0, mac (= block0[0..15]) and __le64 lens[2] (VST: typed memory) */
		u8 block0[POLY1305_KEY_SIZE];
	} b;
''', 'P17 decrypt union')
    for n, ln in (('src_len', 'encrypt'), ('dst_len', 'decrypt')):
        s = sub1(s, '''	b.lens[0] = cpu_to_le64(ad_len);
	b.lens[1] = cpu_to_le64(%s);
	poly1305_update(&poly1305_state, (u8 *)b.lens, sizeof(b.lens));
''' % n, '''	/* QUICKPROOF P17: the two lengths as 16 little-endian bytes (were b.lens[0..1]) */
	put_unaligned_le64(ad_len, b.block0);
	put_unaligned_le64(%s, b.block0 + 8);
	poly1305_update(&poly1305_state, b.block0, 16);
''' % n, 'P17 lens ' + ln)
    s = sub1(s, '''	poly1305_final(&poly1305_state, b.mac);

	ret = crypto_memneq(b.mac, src + dst_len, POLY1305_DIGEST_SIZE);
''', '''	poly1305_final(&poly1305_state, b.block0); /* QUICKPROOF P17: b.mac was block0[0..15] */

	ret = crypto_memneq(b.block0, src + dst_len, POLY1305_DIGEST_SIZE);
''', 'P17 mac')
    # P18: the scatterlist functions (data path) compiled out
    s = s + tail
    a = s.index('static\nbool chacha20poly1305_crypt_sg_inplace(')
    b = s.index('EXPORT_SYMBOL(chacha20poly1305_decrypt_sg_inplace);\n') + len('EXPORT_SYMBOL(chacha20poly1305_decrypt_sg_inplace);\n')
    s = (s[:a] + '/* QUICKPROOF P18: the scatterlist functions (data path, never called by the handshake) are compiled out */\n'
         '#if 0\n' + s[a:b] + '#endif /* QUICKPROOF P18 */\n' + s[b:])
    write(p, s)


def patch_poly1305(p, internal):
    s = read(p)
    s = sub1(s, '\t*desc = (struct poly1305_desc_ctx){};\n',
             '\tmemset(desc, 0, sizeof(*desc)); /* QUICKPROOF P19: was *desc = (struct poly1305_desc_ctx){}; (C23 empty literal, struct assignment) */\n',
             'P19 poly1305_final')
    write(p, s)
    s = read(internal)
    s = sub1(s, '\t*state = (struct poly1305_state){};\n',
             '\tmemset(state, 0, sizeof(*state)); /* QUICKPROOF P20: was *state = (struct poly1305_state){}; (C23 empty literal, struct assignment) */\n',
             'P20 poly1305_core_init')
    write(internal, s)


def patch_fiat32(p):
    s = read(p)
    for name, t in (('fe_copy', 'fe'), ('fe_copy_lt', 'fe_loose')):
        s = sub1(s, '''static __always_inline void %s(%s *h, const fe *f)
{
	memmove(h, f, sizeof(u32) * 10);
}''' % (name, t), '''static __always_inline void %s(%s *h, const fe *f)
{
	int i; /* QUICKPROOF P21: memmove of the 10 limbs, limb by limb (VST: typed memory) */

	for (i = 0; i < 10; i++)
		h->v[i] = f->v[i];
}''' % (name, t), 'P21 ' + name)
    s = sub1(s, '''static __always_inline void fe_0(fe *h)
{
	memset(h, 0, sizeof(u32) * 10);
}''', '''static __always_inline void fe_0(fe *h)
{
	int i; /* QUICKPROOF P21: memset of the 10 limbs, limb by limb (VST: typed memory) */

	for (i = 0; i < 10; i++)
		h->v[i] = 0;
}''', 'P21 fe_0')
    s = sub1(s, '''static __always_inline void fe_1(fe *h)
{
	memset(h, 0, sizeof(u32) * 10);
	h->v[0] = 1;
}''', '''static __always_inline void fe_1(fe *h)
{
	int i; /* QUICKPROOF P21: memset of the 10 limbs, limb by limb (VST: typed memory) */

	for (i = 0; i < 10; i++)
		h->v[i] = 0;
	h->v[0] = 1;
}''', 'P21 fe_1')
    write(p, s)


def main():
    apply_series()
    check_counter('drivers/net/wireguard/receive.c', 'patch/counter_validate.c')
    check_data_header('drivers/net/wireguard/receive.c', 'patch/data_header.c')
    check_timers('patch/wg_shim.c')
    patch_noise('drivers/net/wireguard/noise.c')
    patch_cookie('drivers/net/wireguard/cookie.c')
    patch_counter('patch/counter_validate.c')
    patch_blake2s('lib/crypto/blake2s.c')
    patch_chacha_block('lib/crypto/chacha-block-generic.c')
    patch_aead('lib/crypto/chacha20poly1305.c')
    patch_poly1305('lib/crypto/poly1305.c', 'include/crypto/internal/poly1305.h')
    patch_fiat32('lib/crypto/curve25519-fiat32.c')


if __name__ == '__main__':
    main()
