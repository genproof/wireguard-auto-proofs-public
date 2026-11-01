#!/usr/bin/env python3
"""extract_check.py [TREE]: QUICKPROOF S22 - patch/receive_handshake.c holds upstream's text byte for byte.

The blocks between `/* ---- BEGIN UPSTREAM receive.c (n) ---- */` and `/* ---- END UPSTREAM receive.c (n) ---- */`
must be exactly (1) receive.c from `#define SKB_TYPE_LE32(skb)` up to `static int prepare_skb_header(` and (2) from
`static void wg_receive_handshake_packet(` up to `void wg_packet_handshake_receive_worker(` (both untouched by
patch/wgpatch.py, so the check holds in the unmodified and in the patched tree)."""
import os
import sys

t = sys.argv[1] if len(sys.argv) > 1 else '.'
r = open(os.path.join(t, 'drivers/net/wireguard/receive.c')).read()
u = open(os.path.join(t, 'patch/receive_handshake.c')).read()


def between(s, a, b):
    i = s.index(a) + len(a)
    return s[i:s.index(b, i)]


want = [r[r.index('#define SKB_TYPE_LE32(skb)'):r.index('static int prepare_skb_header(')],
        r[r.index('static void wg_receive_handshake_packet('):r.index('void wg_packet_handshake_receive_worker(')]]
for n, w in enumerate(want, 1):
    got = between(u, '/* ---- BEGIN UPSTREAM receive.c (%d) ---- */\n' % n, '/* ---- END UPSTREAM receive.c (%d) ---- */' % n)
    if got != w:
        sys.exit('extract_check: block %d of patch/receive_handshake.c differs from receive.c' % n)
print('extract_check: patch/receive_handshake.c = receive.c (2 blocks, %d + %d bytes)' % tuple(len(w) for w in want))
