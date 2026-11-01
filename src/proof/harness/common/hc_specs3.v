(* ONE specification per function of harness/common.h, shared by the protocol laws.

   common.h is compiled into every harness unit (static functions: the same identifier $"name" in every law;
   the static CONSTANTS are renamed per unit, <law>__M_BASEPOINT etc., so the specifications that read them
   take the constant's identifier as an argument: `bp`, `cons`, `iden`).

   Compspecs: the harness structs are stated at the compspecs of law handshake's unit (`HCS`, it has
   m_state, m_identity, m_initiation, m_consumed_initiation, m_response, hs_snap); ck_snap at cookie_mac's
   (`CKS`).  The protocol's objects (peer_rep, device_rep, itable, shim_state, ... of prot_repr3.v) are at
   Noise.CS as everywhere.  Byte arrays are the same in every compspecs.  A body proof (in the unit's
   compspecs of each law) and a caller (main, at the world W_<law>) convert with data_at_change_composite /
   prot_cs.v's data_at_cs_eq (the composites agree).

   Parameters: the primitive models x25519, aead_enc, aead_dec (prim_api.v), the world compspecs CSw. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import QuickProof.Env.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_dec3.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_specs3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require WgNoise.contracts.x_handshake WgNoise.contracts.x_cookie_mac.
Require WgNoise.harness.x_handshake.code WgNoise.harness.x_cookie_reply.code
        WgNoise.harness.x_consume_response_any.code.
Local Open Scope logic.

Module HH := WgNoise.harness.x_handshake.code.
Module HK := WgNoise.harness.x_cookie_reply.code.
Module HR := WgNoise.harness.x_consume_response_any.code.

Definition HCS : compspecs := WgNoise.contracts.x_handshake.Harness.CS.
Definition CKS : compspecs := WgNoise.contracts.x_cookie_mac.Harness.CS.

Definition t_mstate := Tstruct HH._m_state noattr.
Definition t_mident := Tstruct HH._m_identity noattr.
Definition t_minit := Tstruct HH._m_initiation noattr.
Definition t_mcinit := Tstruct HH._m_consumed_initiation noattr.
Definition t_mresp := Tstruct HH._m_response noattr.
Definition t_hsnap := Tstruct HH._hs_snap noattr.
Definition t_cksnap := Tstruct HK._ck_snap noattr.

(* ------------------------------------------------------------------------------------------------ *)
(* values of the harness structs                                                                    *)
(* ------------------------------------------------------------------------------------------------ *)

Section HCSvals.
#[local] Existing Instance HCS.

Definition mstate_val (ck h: list byte) : reptype t_mstate := (bytes ck, bytes h).
Definition mident_val (I: mident) : reptype t_mident :=
  (bytes (mi_priv I), (bytes (mi_pub I), Vint (if mi_ok I then Int.one else Int.zero))).
Definition minit_val (E encs enct ep ck h: list byte) : reptype t_minit :=
  (bytes E, (bytes encs, (bytes enct, (bytes ep, (bytes ck, bytes h))))).
Definition mcinit_val (ck h: list byte) (key spub ts: list val) : reptype t_mcinit :=
  ((bytes ck, bytes h), (key, (spub, ts))).
Definition mresp_val (E encn ep ck h: list byte) : reptype t_mresp :=
  (bytes E, (bytes encn, (bytes ep, (bytes ck, bytes h)))).
Definition hsnap_val (s: hsnap) : reptype t_hsnap :=
  let E := sn_entry s in let H := sn_hs s in
  (e_peer E, (sn_next s, (Val.of_bool (sn_hashed s), (Vint (e_type E), (Vint (e_index E),
  (Vint (hs_state H), (Vlong (hs_lic H), (hs_sid H, (bytes (hs_eph H), (bytes (hs_rstatic H),
  (bytes (hs_reph H), (bytes (hs_ss H), (bytes (hs_psk H), (bytes (hs_hash H), (bytes (hs_ck H),
  (bytes (hs_ts H), Vint (hs_rindex H))))))))))))))))).

(* byte buffers at HCS *)
Definition hbytes (sh: share) (bs: list byte) (p: val) : mpred :=
  data_at sh (tarray tuchar (Zlength bs)) (bytes bs) p.
(* an input buffer that may be empty (then any pointer, NULL included) *)
Definition hin (sh: share) (bs: list byte) (p: val) : mpred :=
  if Z.eq_dec (Zlength bs) 0 then emp else hbytes sh bs p.
(* an output buffer of n bytes, any prior contents *)
Definition hout (sh: share) (n: Z) (p: val) : mpred := data_at_ sh (tarray tuchar n) p.

(* the constants of common.h (renamed per law: their identifiers are arguments) *)
Definition hc_const (gv: globals) (i: ident) (bs: list byte) : mpred :=
  data_at Ers (tarray tuchar (Zlength bs)) (bytes bs) (gv i).
End HCSvals.

Section CKSvals.
#[local] Existing Instance CKS.
Definition cksnap_val (C: cookie) : reptype t_cksnap :=
  (Vlong (ck_birth C), (Val.of_bool (ck_valid C), (bytes (ck_cookie C), (Val.of_bool (ck_sent C),
  (bytes (ck_last_mac1 C), (bytes (ck_dkey C), bytes (ck_mkey C))))))).
End CKSvals.

Definition construction_bytes : list byte := handshake_name.  (* M_CONSTRUCTION[37] *)
Definition identifier_bytes : list byte := identifier_name.  (* M_IDENTIFIER[34] *)

Section Specs.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
#[local] Existing Instance HCS.

(* ------------------------------------------------------------------------------------------------ *)
(* checks and byte helpers                                                                          *)
(* ------------------------------------------------------------------------------------------------ *)

(* check_failed: a NULL store: never called in a safe run *)
Definition check_failed_spec :=
  DECLARE HH._check_failed
  WITH u: unit
  PRE [ ] PROP (False) PARAMS () SEP ()
  POST [ tvoid ] PROP () RETURN () SEP ().

Definition bytes_eq_spec :=
  DECLARE HH._bytes_eq
  WITH sha: share, a: val, A: list byte, shb: share, b: val, B: list byte
  PRE [ tptr tuchar, tptr tuchar, tulong ]
    PROP (readable_share sha; readable_share shb; Zlength A = Zlength B; Zlength A <= Int64.max_unsigned)
    PARAMS (a; b; Vlong (Int64.repr (Zlength A)))
    SEP (hbytes sha A a; hbytes shb B b)
  POST [ tint ]
    PROP () RETURN (Vint (if bytes_eqb A B then Int.one else Int.zero))
    SEP (hbytes sha A a; hbytes shb B b).

Definition bytes_zero_spec :=
  DECLARE HH._bytes_zero
  WITH sha: share, a: val, A: list byte
  PRE [ tptr tuchar, tulong ]
    PROP (readable_share sha; Zlength A <= Int64.max_unsigned)
    PARAMS (a; Vlong (Int64.repr (Zlength A)))
    SEP (hbytes sha A a)
  POST [ tint ]
    PROP () RETURN (Vint (if is_zero A then Int.one else Int.zero))
    SEP (hbytes sha A a).

Definition bytes_copy_spec :=
  DECLARE HH._bytes_copy
  WITH shd: share, d: val, shs: share, s: val, A: list byte
  PRE [ tptr tuchar, tptr tuchar, tulong ]
    PROP (writable_share shd; readable_share shs; Zlength A <= Int64.max_unsigned)
    PARAMS (d; s; Vlong (Int64.repr (Zlength A)))
    SEP (hout shd (Zlength A) d; hbytes shs A s)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (hbytes shd A d; hbytes shs A s).

Definition bytes_set_spec :=
  DECLARE HH._bytes_set
  WITH shd: share, d: val, v: byte, n: Z
  PRE [ tptr tuchar, tuchar, tulong ]
    PROP (writable_share shd; 0 <= n <= Int64.max_unsigned)
    PARAMS (d; Vubyte v; Vlong (Int64.repr n))
    SEP (hout shd n d)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (hbytes shd (Zrepeat v n) d).

(* draw_size / draw_steps: any size (N_MAX = STEPS_MAX = SIZE_MAX for the contracts) *)
Definition draw_size_spec :=
  DECLARE HK._draw_size
  WITH u: unit
  PRE [ ] PROP () PARAMS () SEP ()
  POST [ tulong ] EX n: Z,
    PROP (0 <= n <= Int64.max_unsigned) RETURN (Vlong (Int64.repr n)) SEP ().

Definition draw_steps_spec :=
  DECLARE HR._draw_steps
  WITH u: unit
  PRE [ ] PROP () PARAMS () SEP ()
  POST [ tulong ] EX n: Z,
    PROP (0 <= n <= Int64.max_unsigned) RETURN (Vlong (Int64.repr n)) SEP ().

Definition draw_u64_spec :=
  DECLARE HH._draw_u64
  WITH u: unit
  PRE [ ] PROP () PARAMS () SEP ()
  POST [ tulong ] EX v: int64,
    PROP () RETURN (Vlong v) SEP ().

(* draw_boottime: any value below 2^62 *)
Definition draw_boottime_spec :=
  DECLARE HH._draw_boottime
  WITH u: unit
  PRE [ ] PROP () PARAMS () SEP ()
  POST [ tulong ] EX v: int64,
    PROP (0 <= Int64.unsigned v < 2 ^ 62) RETURN (Vlong v) SEP ().

Definition le32_store_spec :=
  DECLARE HH._le32_store
  WITH sh: share, p: val, v: int
  PRE [ tptr tuchar, tuint ]
    PROP (writable_share sh) PARAMS (p; Vint v)
    SEP (hout sh 4 p)
  POST [ tvoid ]
    PROP () RETURN () SEP (hbytes sh (le32 v) p).

(* ------------------------------------------------------------------------------------------------ *)
(* the symmetric model                                                                              *)
(* ------------------------------------------------------------------------------------------------ *)

(* m_hash2(out, a, |A|, b, |B|): out = HASH(A || B) *)
Definition m_hash2_spec :=
  DECLARE HH._m_hash2
  WITH gv: globals, sho: share, o: val, sha: share, a: val, A: list byte, shb: share, b: val, B: list byte
  PRE [ tptr tuchar, tptr tuchar, tulong, tptr tuchar, tulong ]
    PROP (writable_share sho; readable_share sha; readable_share shb;
          Zlength A <= Int64.max_signed; Zlength B <= Int64.max_signed)
    PARAMS (o; a; Vlong (Int64.repr (Zlength A)); b; Vlong (Int64.repr (Zlength B))) GLOBALS (gv)
    SEP (hout sho 32 o; hin sha A a; hin shb B b; blake2s_globals gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (hbytes sho (HASH (A ++ B)) o; hin sha A a; hin shb B b; blake2s_globals gv).

(* m_hmac(out, key[32], in, |IN|): out = hmac K IN (prot_model3's HMAC-BLAKE2s) *)
Definition m_hmac_spec :=
  DECLARE HH._m_hmac
  WITH gv: globals, sho: share, o: val, shk: share, k: val, K: list byte, shi: share, i: val, IN: list byte
  PRE [ tptr tuchar, tptr tuchar, tptr tuchar, tulong ]
    PROP (writable_share sho; readable_share shk; readable_share shi; Zlength K = 32;
          Zlength IN <= Int64.max_signed)
    PARAMS (o; k; i; Vlong (Int64.repr (Zlength IN))) GLOBALS (gv)
    SEP (hout sho 32 o; hbytes shk K k; hin shi IN i; blake2s_globals gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (hbytes sho (hmac K IN) o; hbytes shk K k; hin shi IN i; blake2s_globals gv).

(* m_kdf(t1, t2, t3, ck, in, |IN|): KDF3 *)
Definition m_kdf_spec :=
  DECLARE HH._m_kdf
  WITH gv: globals, sh1: share, t1: val, sh2: share, t2: val, sh3: share, t3: val, shc: share, c: val,
       CK: list byte, shi: share, i: val, IN: list byte
  PRE [ tptr tuchar, tptr tuchar, tptr tuchar, tptr tuchar, tptr tuchar, tulong ]
    PROP (writable_share sh1; writable_share sh2; writable_share sh3; readable_share shc; readable_share shi;
          Zlength CK = 32; Zlength IN <= Int64.max_signed)
    PARAMS (t1; t2; t3; c; i; Vlong (Int64.repr (Zlength IN))) GLOBALS (gv)
    SEP (hout sh1 32 t1; hout sh2 32 t2; hout sh3 32 t3; hbytes shc CK c; hin shi IN i; blake2s_globals gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (hbytes sh1 (kdf1 CK IN) t1; hbytes sh2 (kdf2 CK IN) t2; hbytes sh3 (kdf3 CK IN) t3;
         hbytes shc CK c; hin shi IN i; blake2s_globals gv).

(* m_dh(out, priv, pub): out = X25519(priv, pub) (the kernel's curve25519_generic); 1 iff not all zero *)
Definition m_dh_spec :=
  DECLARE HH._m_dh
  WITH sho: share, o: val, shv: share, v: val, PRIV: list byte, shp: share, p: val, PUB: list byte
  PRE [ tptr tuchar, tptr tuchar, tptr tuchar ]
    PROP (writable_share sho; readable_share shv; readable_share shp; Zlength PRIV = 32; Zlength PUB = 32)
    PARAMS (o; v; p)
    SEP (hout sho 32 o; hbytes shv PRIV v; hbytes shp PUB p)
  POST [ tint ]
    PROP () RETURN (Vint (if dh_ok x25519 PRIV PUB then Int.one else Int.zero))
    SEP (hbytes sho (x25519 PRIV PUB) o; hbytes shv PRIV v; hbytes shp PUB p).

Definition m_clamp_spec :=
  DECLARE HH._m_clamp
  WITH sh: share, k: val, K: list byte
  PRE [ tptr tuchar ]
    PROP (writable_share sh; Zlength K = 32) PARAMS (k) SEP (hbytes sh K k)
  POST [ tvoid ]
    PROP () RETURN () SEP (hbytes sh (clamp K) k).

(* m_identity_of(id, raw); bp = the law's M_BASEPOINT *)
Definition m_identity_of_spec (bp: ident) :=
  DECLARE HH._m_identity_of
  WITH gv: globals, sh: share, d: val, shr: share, r: val, RAW: list byte
  PRE [ tptr t_mident, tptr tuchar ]
    PROP (writable_share sh; readable_share shr; Zlength RAW = 32) PARAMS (d; r) GLOBALS (gv)
    SEP (data_at_ sh t_mident d; hbytes shr RAW r; hc_const gv bp basepoint9)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh t_mident (mident_val (mident_of x25519 RAW)) d; hbytes shr RAW r;
         hc_const gv bp basepoint9).

(* m_start(s, rpub): (ck, h) = (HASH(CONSTRUCTION), HASH(HASH(Ci || IDENTIFIER) || rpub)) *)
Definition m_start_spec (cons iden: ident) :=
  DECLARE HH._m_start
  WITH gv: globals, sh: share, s: val, shp: share, p: val, PUB: list byte
  PRE [ tptr t_mstate, tptr tuchar ]
    PROP (writable_share sh; readable_share shp; Zlength PUB = 32) PARAMS (s; p) GLOBALS (gv)
    SEP (data_at_ sh t_mstate s; hbytes shp PUB p; hc_const gv cons construction_bytes;
         hc_const gv iden identifier_bytes; blake2s_globals gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh t_mstate (mstate_val init_ck (mix_hash init_hash PUB)) s; hbytes shp PUB p;
         hc_const gv cons construction_bytes; hc_const gv iden identifier_bytes; blake2s_globals gv).

Definition m_mix_hash_spec :=
  DECLARE HH._m_mix_hash
  WITH gv: globals, sh: share, s: val, CK: list byte, H: list byte, shd: share, d: val, D: list byte
  PRE [ tptr t_mstate, tptr tuchar, tulong ]
    PROP (writable_share sh; readable_share shd; Zlength CK = 32; Zlength H = 32;
          Zlength D <= Int64.max_signed)
    PARAMS (s; d; Vlong (Int64.repr (Zlength D))) GLOBALS (gv)
    SEP (data_at sh t_mstate (mstate_val CK H) s; hin shd D d; blake2s_globals gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh t_mstate (mstate_val CK (mix_hash H D)) s; hin shd D d; blake2s_globals gv).

Definition m_mix_ck_spec :=
  DECLARE HH._m_mix_ck
  WITH gv: globals, sh: share, s: val, CK: list byte, H: list byte, shd: share, d: val, D: list byte
  PRE [ tptr t_mstate, tptr tuchar, tulong ]
    PROP (writable_share sh; readable_share shd; Zlength CK = 32; Zlength H = 32;
          Zlength D <= Int64.max_signed)
    PARAMS (s; d; Vlong (Int64.repr (Zlength D))) GLOBALS (gv)
    SEP (data_at sh t_mstate (mstate_val CK H) s; hin shd D d; blake2s_globals gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh t_mstate (mstate_val (kdf1 CK D) H) s; hin shd D d; blake2s_globals gv).

Definition m_mix_key_spec :=
  DECLARE HH._m_mix_key
  WITH gv: globals, sh: share, s: val, CK: list byte, H: list byte, shk: share, k: val,
       shd: share, d: val, D: list byte
  PRE [ tptr t_mstate, tptr tuchar, tptr tuchar, tulong ]
    PROP (writable_share sh; writable_share shk; readable_share shd; Zlength CK = 32; Zlength H = 32;
          Zlength D <= Int64.max_signed)
    PARAMS (s; k; d; Vlong (Int64.repr (Zlength D))) GLOBALS (gv)
    SEP (data_at sh t_mstate (mstate_val CK H) s; hout shk 32 k; hin shd D d; blake2s_globals gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh t_mstate (mstate_val (kdf1 CK D) H) s; hbytes shk (kdf2 CK D) k; hin shd D d;
         blake2s_globals gv).

Definition m_mix_psk_spec :=
  DECLARE HH._m_mix_psk
  WITH gv: globals, sh: share, s: val, CK: list byte, H: list byte, shk: share, k: val,
       shp: share, p: val, PSK: list byte
  PRE [ tptr t_mstate, tptr tuchar, tptr tuchar ]
    PROP (writable_share sh; writable_share shk; readable_share shp; Zlength CK = 32; Zlength H = 32;
          Zlength PSK = 32)
    PARAMS (s; k; p) GLOBALS (gv)
    SEP (data_at sh t_mstate (mstate_val CK H) s; hout shk 32 k; hbytes shp PSK p; blake2s_globals gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh t_mstate (mstate_val (kdf1 CK PSK) (mix_hash H (kdf2 CK PSK))) s;
         hbytes shk (kdf3 CK PSK) k; hbytes shp PSK p; blake2s_globals gv).

(* m_encrypt_and_hash(s, c, p, |P|, key): c = AEAD(key, 0, P, H); H = HASH(H || c) *)
Definition m_encrypt_and_hash_spec :=
  DECLARE HH._m_encrypt_and_hash
  WITH gv: globals, sh: share, s: val, CK: list byte, H: list byte, shc: share, c: val,
       shp: share, p: val, P: list byte, shk: share, k: val, KEY: list byte
  PRE [ tptr t_mstate, tptr tuchar, tptr tuchar, tulong, tptr tuchar ]
    PROP (writable_share sh; writable_share shc; readable_share shp; readable_share shk;
          Zlength CK = 32; Zlength H = 32; Zlength KEY = 32; Zlength P <= Int.max_unsigned - 16)
    PARAMS (s; c; p; Vlong (Int64.repr (Zlength P)); k) GLOBALS (gv)
    SEP (data_at sh t_mstate (mstate_val CK H) s; hout shc (Zlength P + 16) c; hin shp P p;
         hbytes shk KEY k; blake2s_globals gv; @zero_page Noise.CS gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh t_mstate (mstate_val CK (mix_hash H (aead_enc KEY 0 H P))) s;
         hbytes shc (aead_enc KEY 0 H P) c; hin shp P p;
         hbytes shk KEY k; blake2s_globals gv; @zero_page Noise.CS gv).

(* m_decrypt_and_hash(s, p, c, |C|, key): 1, p = plaintext and H = HASH(H || C) if the tag verifies; else 0
   and nothing changes.  p has max(|C| - 16, 0) bytes (any prior contents; nothing when empty) *)
Definition m_decrypt_and_hash_spec :=
  DECLARE HH._m_decrypt_and_hash
  WITH gv: globals, sh: share, s: val, CK: list byte, H: list byte, shp: share, p: val, old: list val,
       shc: share, c: val, C: list byte, shk: share, k: val, KEY: list byte
  PRE [ tptr t_mstate, tptr tuchar, tptr tuchar, tulong, tptr tuchar ]
    PROP (writable_share sh; writable_share shp; readable_share shc; readable_share shk;
          Zlength CK = 32; Zlength H = 32; Zlength KEY = 32; Zlength C <= Int.max_unsigned;
          Zlength old = Z.max 0 (Zlength C - 16))
    PARAMS (s; p; c; Vlong (Int64.repr (Zlength C)); k) GLOBALS (gv)
    SEP (data_at sh t_mstate (mstate_val CK H) s; prim_out shp old p; hin shc C c;
         hbytes shk KEY k; blake2s_globals gv; @zero_page Noise.CS gv)
  POST [ tint ]
    PROP ()
    RETURN (Vint (match aead_dec KEY 0 H C with Some _ => Int.one | None => Int.zero end))
    SEP (data_at sh t_mstate (mstate_val CK (match aead_dec KEY 0 H C with Some _ => mix_hash H C | None => H end)) s;
         prim_out shp (match aead_dec KEY 0 H C with Some pt => bytes pt | None => old end) p;
         hin shc C c; hbytes shk KEY k; blake2s_globals gv; @zero_page Noise.CS gv).

Definition m_tai64n_spec :=
  DECLARE HH._m_tai64n
  WITH sh: share, o: val, sec: int64, nsec: int64
  PRE [ tptr tuchar, tlong, tlong ]
    PROP (writable_share sh) PARAMS (o; Vlong sec; Vlong nsec)
    SEP (hout sh 12 o)
  POST [ tvoid ]
    PROP () RETURN () SEP (hbytes sh (tai64n sec nsec) o).

(* m_create_initiation(o, spub, rpub, ss, eraw, ts): 1 and o = the model's message fields, ephemeral
   private key and state iff every step succeeds; 0 and o anything otherwise *)
Definition m_create_initiation_spec (bp cons iden: ident) :=
  DECLARE HH._m_create_initiation
  WITH gv: globals, sho: share, o: val, sh: share, ps: val, SPUB: list byte, pr: val, RPUB: list byte,
       pss: val, SS: list byte, pe: val, ERAW: list byte, pt: val, TS: list byte
  PRE [ tptr t_minit, tptr tuchar, tptr tuchar, tptr tuchar, tptr tuchar, tptr tuchar ]
    PROP (writable_share sho; readable_share sh; Zlength SPUB = 32; Zlength RPUB = 32; Zlength SS = 32;
          Zlength ERAW = 32; Zlength TS = 12)
    PARAMS (o; ps; pr; pss; pe; pt) GLOBALS (gv)
    SEP (data_at_ sho t_minit o; hbytes sh SPUB ps; hbytes sh RPUB pr; hbytes sh SS pss;
         hbytes sh ERAW pe; hbytes sh TS pt;
         hc_const gv bp basepoint9; hc_const gv cons construction_bytes; hc_const gv iden identifier_bytes;
         blake2s_globals gv; @zero_page Noise.CS gv)
  POST [ tint ]
    PROP ()
    RETURN (Vint (match m_create_initiation_model x25519 aead_enc SPUB RPUB SS ERAW TS with
                  Some _ => Int.one | None => Int.zero end))
    SEP (match m_create_initiation_model x25519 aead_enc SPUB RPUB SS ERAW TS with
         | Some (E, encs, enct, ep, ck, h) => data_at sho t_minit (minit_val E encs enct ep ck h) o
         | None => data_at_ sho t_minit o end;
         hbytes sh SPUB ps; hbytes sh RPUB pr; hbytes sh SS pss; hbytes sh ERAW pe; hbytes sh TS pt;
         hc_const gv bp basepoint9; hc_const gv cons construction_bytes; hc_const gv iden identifier_bytes;
         blake2s_globals gv; @zero_page Noise.CS gv).

(* m_consume_initiation_1(o, rid, ephemeral, enc_static): stage 1 of the responder (prot_model3's
   consume_init_stage1); on success o's state, key and initiator static are set (ts untouched) *)
Definition m_consume_initiation_1_spec (cons iden: ident) :=
  DECLARE HH._m_consume_initiation_1
  WITH gv: globals, sho: share, o: val, tsv: list val, shi: share, ri: val, I: mident,
       sh: share, pe: val, EPH: list byte, pc: val, ENCS: list byte
  PRE [ tptr t_mcinit, tptr t_mident, tptr tuchar, tptr tuchar ]
    PROP (writable_share sho; readable_share shi; readable_share sh; Zlength (mi_priv I) = 32;
          Zlength (mi_pub I) = 32; Zlength EPH = 32; Zlength ENCS = 48; Zlength tsv = 12)
    PARAMS (o; ri; pe; pc) GLOBALS (gv)
    SEP (data_at sho t_mcinit ((Zrepeat Vundef 32, Zrepeat Vundef 32), (Zrepeat Vundef 32, (Zrepeat Vundef 32, tsv))) o;
         data_at shi t_mident (mident_val I) ri; hbytes sh EPH pe; hbytes sh ENCS pc;
         hc_const gv cons construction_bytes; hc_const gv iden identifier_bytes;
         blake2s_globals gv; @zero_page Noise.CS gv)
  POST [ tint ]
    PROP ()
    RETURN (Vint (match m_consume_init1_model x25519 aead_dec I EPH ENCS with
                  Some _ => Int.one | None => Int.zero end))
    SEP (match m_consume_init1_model x25519 aead_dec I EPH ENCS with
         | Some (s, key, ck, h) => data_at sho t_mcinit (mcinit_val ck h (bytes key) (bytes s) tsv) o
         | None => data_at_ sho t_mcinit o end;
         data_at shi t_mident (mident_val I) ri; hbytes sh EPH pe; hbytes sh ENCS pc;
         hc_const gv cons construction_bytes; hc_const gv iden identifier_bytes;
         blake2s_globals gv; @zero_page Noise.CS gv).

(* m_consume_initiation_2(o, ss, enc_timestamp): stage 2 (consume_init_stage2) from o's state; the
   initiator static spub is kept *)
Definition m_consume_initiation_2_spec :=
  DECLARE HH._m_consume_initiation_2
  WITH gv: globals, sho: share, o: val, CK: list byte, H: list byte, keyv: list val, spubv: list val,
       tsv: list val, sh: share, ps: val, SS: list byte, pt: val, ENCT: list byte
  PRE [ tptr t_mcinit, tptr tuchar, tptr tuchar ]
    PROP (writable_share sho; readable_share sh; Zlength CK = 32; Zlength H = 32; Zlength keyv = 32;
          Zlength spubv = 32; Zlength tsv = 12; Zlength SS = 32; Zlength ENCT = 28)
    PARAMS (o; ps; pt) GLOBALS (gv)
    SEP (data_at sho t_mcinit (mcinit_val CK H keyv spubv tsv) o; hbytes sh SS ps; hbytes sh ENCT pt;
         blake2s_globals gv; @zero_page Noise.CS gv)
  POST [ tint ]
    PROP ()
    RETURN (Vint (match m_consume_init2_model aead_dec SS CK H ENCT with
                  Some _ => Int.one | None => Int.zero end))
    SEP (match m_consume_init2_model aead_dec SS CK H ENCT with
         | Some (t, ck, h) => data_at sho t_mcinit (mcinit_val ck h (bytes (kdf2 CK SS)) spubv (bytes t)) o
         | None => data_at_ sho t_mcinit o end;
         hbytes sh SS ps; hbytes sh ENCT pt; blake2s_globals gv; @zero_page Noise.CS gv).

(* m_create_response(o, st, ei, si, psk, eraw) *)
Definition m_create_response_spec (bp: ident) :=
  DECLARE HH._m_create_response
  WITH gv: globals, sho: share, o: val, shs: share, st: val, CK: list byte, H: list byte,
       sh: share, pi: val, EI: list byte, psi: val, SI: list byte, pp: val, PSK: list byte,
       pe: val, ERAW: list byte
  PRE [ tptr t_mresp, tptr t_mstate, tptr tuchar, tptr tuchar, tptr tuchar, tptr tuchar ]
    PROP (writable_share sho; readable_share shs; readable_share sh; Zlength CK = 32; Zlength H = 32;
          Zlength EI = 32; Zlength SI = 32; Zlength PSK = 32; Zlength ERAW = 32)
    PARAMS (o; st; pi; psi; pp; pe) GLOBALS (gv)
    SEP (data_at_ sho t_mresp o; data_at shs t_mstate (mstate_val CK H) st;
         hbytes sh EI pi; hbytes sh SI psi; hbytes sh PSK pp; hbytes sh ERAW pe;
         hc_const gv bp basepoint9; blake2s_globals gv; @zero_page Noise.CS gv)
  POST [ tint ]
    PROP ()
    RETURN (Vint (match m_create_response_model x25519 aead_enc CK H EI SI PSK ERAW with
                  Some _ => Int.one | None => Int.zero end))
    SEP (match m_create_response_model x25519 aead_enc CK H EI SI PSK ERAW with
         | Some (E, encn, ep, ck, h) => data_at sho t_mresp (mresp_val E encn ep ck h) o
         (* a failed call has written the clamped private key and the ephemeral (m_dh always writes its
            output) before returning; the state is partially mixed; enc_nothing is not written *)
         | None => EX ck': list byte, EX h': list byte,
                   data_at sho t_mresp (bytes (x25519 (clamp ERAW) basepoint9),
                                        (Zrepeat Vundef 16, (bytes (clamp ERAW), (bytes ck', bytes h')))) o end;
         data_at shs t_mstate (mstate_val CK H) st;
         hbytes sh EI pi; hbytes sh SI psi; hbytes sh PSK pp; hbytes sh ERAW pe;
         hc_const gv bp basepoint9; blake2s_globals gv; @zero_page Noise.CS gv).

(* m_consume_response(out, st, eph_priv, spriv, psk, ephemeral, enc_nothing) *)
Definition m_consume_response_spec :=
  DECLARE HH._m_consume_response
  WITH gv: globals, sho: share, o: val, shs: share, st: val, CK: list byte, H: list byte,
       sh: share, pe: val, EPRIV: list byte, ps: val, SPRIV: list byte, pp: val, PSK: list byte,
       pm: val, E: list byte, pn: val, ENCN: list byte
  PRE [ tptr t_mstate, tptr t_mstate, tptr tuchar, tptr tuchar, tptr tuchar, tptr tuchar, tptr tuchar ]
    PROP (writable_share sho; readable_share shs; readable_share sh; Zlength CK = 32; Zlength H = 32;
          Zlength EPRIV = 32; Zlength SPRIV = 32; Zlength PSK = 32; Zlength E = 32; Zlength ENCN = 16)
    PARAMS (o; st; pe; ps; pp; pm; pn) GLOBALS (gv)
    SEP (data_at_ sho t_mstate o; data_at shs t_mstate (mstate_val CK H) st;
         hbytes sh EPRIV pe; hbytes sh SPRIV ps; hbytes sh PSK pp; hbytes sh E pm; hbytes sh ENCN pn;
         blake2s_globals gv; @zero_page Noise.CS gv)
  POST [ tint ]
    PROP ()
    RETURN (Vint (match m_consume_response_model x25519 aead_dec CK H EPRIV SPRIV PSK E ENCN with
                  Some _ => Int.one | None => Int.zero end))
    SEP (match m_consume_response_model x25519 aead_dec CK H EPRIV SPRIV PSK E ENCN with
         | Some (ck, h) => data_at sho t_mstate (mstate_val ck h) o
         | None => data_at_ sho t_mstate o end;
         data_at shs t_mstate (mstate_val CK H) st;
         hbytes sh EPRIV pe; hbytes sh SPRIV ps; hbytes sh PSK pp; hbytes sh E pm; hbytes sh ENCN pn;
         blake2s_globals gv; @zero_page Noise.CS gv).

(* m_transport(first, second, ck): (KDF1, KDF2)(ck, empty) *)
Definition m_transport_spec (bp: ident) :=
  DECLARE HH._m_transport
  WITH gv: globals, sh1: share, f: val, sh2: share, s: val, shc: share, c: val, CK: list byte
  PRE [ tptr tuchar, tptr tuchar, tptr tuchar ]
    PROP (writable_share sh1; writable_share sh2; readable_share shc; Zlength CK = 32)
    PARAMS (f; s; c) GLOBALS (gv)
    SEP (hout sh1 32 f; hout sh2 32 s; hbytes shc CK c; blake2s_globals gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (hbytes sh1 (kdf1 CK []) f; hbytes sh2 (kdf2 CK []) s; hbytes shc CK c; blake2s_globals gv).

(* m_label_key(out, label[8], pub[32]) = HASH(label || pub) = label_key *)
Definition m_label_key_spec :=
  DECLARE HH._m_label_key
  WITH gv: globals, sho: share, o: val, sh: share, l: val, LABEL: list byte, p: val, PUB: list byte
  PRE [ tptr tuchar, tptr tuchar, tptr tuchar ]
    PROP (writable_share sho; readable_share sh; Zlength LABEL = 8; Zlength PUB = 32)
    PARAMS (o; l; p) GLOBALS (gv)
    SEP (hout sho 32 o; hbytes sh LABEL l; hbytes sh PUB p; blake2s_globals gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (hbytes sho (label_key LABEL PUB) o; hbytes sh LABEL l; hbytes sh PUB p; blake2s_globals gv).

(* m_mac(out, key, |K|, msg, |M|) = MAC K M (16 bytes) *)
Definition m_mac_spec :=
  DECLARE HH._m_mac
  WITH gv: globals, sho: share, o: val, shk: share, k: val, K: list byte, shm: share, m: val, M: list byte
  PRE [ tptr tuchar, tptr tuchar, tulong, tptr tuchar, tulong ]
    PROP (writable_share sho; readable_share shk; readable_share shm; Zlength K <= 32;
          Zlength M <= Int64.max_signed)
    PARAMS (o; k; Vlong (Int64.repr (Zlength K)); m; Vlong (Int64.repr (Zlength M))) GLOBALS (gv)
    SEP (hout sho 16 o; hin shk K k; hin shm M m; blake2s_globals gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (hbytes sho (MAC K M) o; hin shk K k; hin shm M m; blake2s_globals gv).

Definition m_precomputed_spec :=
  DECLARE HH._m_precomputed
  WITH sho: share, o: val, shi: share, ri: val, I: mident, shp: share, p: val, PUB: list byte
  PRE [ tptr tuchar, tptr t_mident, tptr tuchar ]
    PROP (writable_share sho; readable_share shi; readable_share shp; Zlength (mi_priv I) = 32;
          Zlength PUB = 32)
    PARAMS (o; ri; p)
    SEP (hout sho 32 o; data_at shi t_mident (mident_val I) ri; hbytes shp PUB p)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (hbytes sho (m_precomputed_model x25519 I PUB) o; data_at shi t_mident (mident_val I) ri;
         hbytes shp PUB p).

Definition m_static_public_field_spec :=
  DECLARE HH._m_static_public_field
  WITH sho: share, o: val, shi: share, ri: val, I: mident, shr: share, r: val, RAW: list byte
  PRE [ tptr tuchar, tptr t_mident, tptr tuchar ]
    PROP (writable_share sho; readable_share shi; readable_share shr; Zlength (mi_pub I) = 32;
          Zlength RAW = 32)
    PARAMS (o; ri; r)
    SEP (hout sho 32 o; data_at shi t_mident (mident_val I) ri; hbytes shr RAW r)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (hbytes sho (static_public_field RAW (mi_pub I)) o; data_at shi t_mident (mident_val I) ri;
         hbytes shr RAW r).

Definition m_ts_newer_spec :=
  DECLARE HH._m_ts_newer
  WITH sh1: share, t: val, TS: list byte, sh2: share, l: val, L: list byte
  PRE [ tptr tuchar, tptr tuchar ]
    PROP (readable_share sh1; readable_share sh2; Zlength TS = 12; Zlength L = 12)
    PARAMS (t; l)
    SEP (hbytes sh1 TS t; hbytes sh2 L l)
  POST [ tint ]
    PROP () RETURN (Vint (if ts_newer TS L then Int.one else Int.zero))
    SEP (hbytes sh1 TS t; hbytes sh2 L l).

Definition m_not_flood_spec :=
  DECLARE HH._m_not_flood
  WITH last: int64, now: int64
  PRE [ tulong, tulong ]
    PROP (Int64.signed last <= Int64.max_signed - 20000000) PARAMS (Vlong last; Vlong now) SEP ()
  POST [ tint ]
    PROP () RETURN (Vint (if not_flood last now then Int.one else Int.zero)) SEP ().

Definition m_last_consumption_spec :=
  DECLARE HH._m_last_consumption
  WITH last: int64, now: int64
  PRE [ tulong, tulong ]
    PROP () PARAMS (Vlong last; Vlong now) SEP ()
  POST [ tulong ]
    PROP () RETURN (Vlong (last_consumption last now)) SEP ().

(* ------------------------------------------------------------------------------------------------ *)
(* the device, the peers and their tables                                                           *)
(* ------------------------------------------------------------------------------------------------ *)

(* setup_device(wg, itab, ptab, raw): wg_noise_set_static_identity_private_key, wg_cookie_checker_init,
   wg_cookie_checker_precompute_device_keys on a device whose read-before-written fields are zero.
   r = the secret drawn by wg_cookie_checker_init. *)
Definition setup_identity (RAW: list byte) : identity :=
  identity_of x25519 (mkId zeros32 zeros32 false) RAW.
Definition setup_dev (wg itab ptab: val) (RAW r: list byte) (now: int64) : device :=
  let ID := setup_identity RAW in
  mkDev nullval ID (mkChk r (fst (checker_keys ID)) (snd (checker_keys ID)) now wg) ptab itab.

Definition setup_device_spec :=
  DECLARE HH._setup_device
  WITH gv: globals, S: shim, sh: share, wg: val, itab: val, ptab: val, shr: share, r: val, RAW: list byte
  PRE [ tptr t_dev, tptr t_itab, tptr t_ptab, tptr tuchar ]
    PROP (writable_share sh; readable_share shr; Zlength RAW = 32)
    PARAMS (wg; itab; ptab; r) GLOBALS (gv)
    SEP (@data_at_ Noise.CS sh t_dev wg; @data_at_ Noise.CS sh t_itab itab; @data_at_ Noise.CS sh t_ptab ptab;
         hbytes shr RAW r; shim_state gv S; wg_consts gv)
  POST [ tvoid ] EX sec: list byte,
    PROP (Zlength sec = 32) RETURN ()
    SEP (device_rep sh wg (setup_dev wg itab ptab RAW sec (s_boot S));
         itable sh itab (mkT [] []); ptable sh ptab nullval;
         hbytes shr RAW r; shim_state gv (shim_draw S sec); wg_consts gv).

(* setup_peer(peer, wg, pub, psk or NULL, id): the peer of wg_peer_create, reduced (common.h), linked at the
   head of the public-key table; its handshake entry comes out unhashed (add it to the index table's pool) *)
Definition setup_peer_val (D: device) (wg p head: val) (PUB PSK: list byte) (id: int64) : peer :=
  mkPeer wg false nullval nullval nullval (hs_initial x25519 (d_id D) (id_addr wg) PUB PSK) Int64.zero
         (cookie_set_keys cookie_zero PUB) Int.one id head.

Definition setup_peer_spec :=
  DECLARE HH._setup_peer
  WITH gv: globals, shp: share, p: val, shd: share, wg: val, D: device, head: val,
       sh: share, pp: val, PUB: list byte, pk: val, PSK: list byte, id: int64
  PRE [ tptr t_peer, tptr t_dev, tptr tuchar, tptr tuchar, tulong ]
    PROP (writable_share shp; writable_share shd; readable_share sh; Zlength PUB = 32;
          pk <> nullval -> Zlength PSK = 32; is_pointer_or_null head)
    PARAMS (p; wg; pp; pk; Vlong id) GLOBALS (gv)
    SEP (@data_at_ Noise.CS shp t_peer p; device_rep shd wg D; ptable shd (d_ptab D) head;
         hbytes sh PUB pp; if eq_dec pk nullval then emp else hbytes sh PSK pk; wg_consts gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (peer_rep shp p (setup_peer_val D wg p head PUB (if eq_dec pk nullval then zeros32 else PSK) id);
         entry_out shp (hs_addr p) (mkEntry p IDX_HANDSHAKE Int.zero);
         device_rep shd wg D; ptable shd (d_ptab D) p;
         hbytes sh PUB pp; if eq_dec pk nullval then emp else hbytes sh PSK pk; wg_consts gv).

(* is the pool entry e in the table (exactly once, hashed)? *)
Definition table_has_spec :=
  DECLARE HH._table_has
  WITH sht: share, tab: val, T: tstate, e: val
  PRE [ tptr t_itab, tptr t_entry_s ]
    PROP (readable_share sht; In e (saddrs (t_D T))) PARAMS (tab; e)
    SEP (itable sht tab T)
  POST [ tint ]
    PROP () RETURN (Vint (if vin e (t_L T) then Int.one else Int.zero)) SEP (itable sht tab T).

Definition table_index_unique_spec :=
  DECLARE HH._table_index_unique
  WITH sht: share, tab: val, T: tstate, idx: int
  PRE [ tptr t_itab, tuint ]
    PROP (readable_share sht; count_index T idx <= 1) PARAMS (tab; Vint idx)
    SEP (itable sht tab T)
  POST [ tint ]
    PROP () RETURN (Vint (if Z.eq_dec (count_index T idx) 1 then Int.one else Int.zero))
    SEP (itable sht tab T).

Definition table_len_spec :=
  DECLARE HH._table_len
  WITH sht: share, tab: val, T: tstate
  PRE [ tptr t_itab ]
    PROP (readable_share sht) PARAMS (tab)
    SEP (itable sht tab T)
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr (Zlength (t_L T)))) SEP (itable sht tab T).

(* hs_take(s, &p->handshake): the snapshot of p's handshake, its entry from the pool of the table T *)
Definition hs_take_spec :=
  DECLARE HH._hs_take
  WITH shs: share, s: val, shp: share, p: val, P: peer, sht: share, tab: val, T: tstate, E: entry
  PRE [ tptr t_hsnap, tptr t_hs ]
    PROP (writable_share shs; readable_share shp; readable_share sht; t_entry T (hs_addr p) = Some E;
          e_peer E <> Vundef; hs_sid (p_hs P) <> Vundef)
    PARAMS (s; hs_addr p)
    SEP (data_at_ shs t_hsnap s; peer_rep shp p P; itable sht tab T)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at shs t_hsnap (hsnap_val (snap_of T (hs_addr p) E (p_hs P))) s; peer_rep shp p P;
         itable sht tab T).

(* hs_same(s, &p->handshake) / hs_zeroed_from: the comparisons of pointers need valid pointers: the
   snapshot is of the same peer's handshake (same peer, same static identity at wg), its next entry is
   NULL or still in the pool *)
Definition hs_cmp_pre (sn: hsnap) (T: tstate) (p wg: val) (P: peer) (E: entry) : Prop :=
  t_entry T (hs_addr p) = Some E /\ e_peer E = p /\ e_peer (sn_entry sn) = p /\
  hs_sid (sn_hs sn) = id_addr wg /\ hs_sid (p_hs P) = id_addr wg /\
  (sn_next sn = nullval \/ In (sn_next sn) (saddrs (t_D T))).

Definition hs_same_spec :=
  DECLARE HH._hs_same
  WITH shs: share, s: val, sn: hsnap, shp: share, p: val, P: peer, sht: share, tab: val, T: tstate,
       E: entry, shd: share, wg: val, D: device
  PRE [ tptr t_hsnap, tptr t_hs ]
    PROP (readable_share shs; readable_share shp; readable_share sht; readable_share shd;
          hs_cmp_pre sn T p wg P E)
    PARAMS (s; hs_addr p)
    SEP (data_at shs t_hsnap (hsnap_val sn) s; peer_rep shp p P; itable sht tab T; device_rep shd wg D)
  POST [ tint ]
    PROP ()
    RETURN (Vint (if snap_eqb sn (snap_of T (hs_addr p) E (p_hs P)) then Int.one else Int.zero))
    SEP (data_at shs t_hsnap (hsnap_val sn) s; peer_rep shp p P; itable sht tab T; device_rep shd wg D).

Definition hs_zeroed_from_spec :=
  DECLARE HH._hs_zeroed_from
  WITH shs: share, s: val, sn: hsnap, shp: share, p: val, P: peer, sht: share, tab: val, T: tstate,
       E: entry, shd: share, wg: val, D: device
  PRE [ tptr t_hsnap, tptr t_hs ]
    PROP (readable_share shs; readable_share shp; readable_share sht; readable_share shd;
          hs_cmp_pre sn T p wg P E)
    PARAMS (s; hs_addr p)
    SEP (data_at shs t_hsnap (hsnap_val sn) s; peer_rep shp p P; itable sht tab T; device_rep shd wg D)
  POST [ tint ]
    PROP ()
    RETURN (Vint (if zeroed_from sn (snap_of T (hs_addr p) E (p_hs P)) then Int.one else Int.zero))
    SEP (data_at shs t_hsnap (hsnap_val sn) s; peer_rep shp p P; itable sht tab T; device_rep shd wg D).

(* hs_randomize(&p->handshake): any state of the five, any keys, hash, chaining key, timestamp, remote
   index, a last consumption below 2^62 *)
Definition hs_randomize_spec :=
  DECLARE HR._hs_randomize
  WITH shp: share, p: val, P: peer
  PRE [ tptr t_hs ]
    PROP (writable_share shp) PARAMS (hs_addr p)
    SEP (peer_rep shp p P)
  POST [ tvoid ] EX st: int, EX lic: int64, EX eph: list byte, EX reph: list byte, EX hash: list byte,
                 EX ck: list byte, EX ts: list byte, EX ri: int,
    PROP (In st hs_states; 0 <= Int64.unsigned lic < 2 ^ 62; Zlength eph = 32; Zlength reph = 32;
          Zlength hash = 32; Zlength ck = 32; Zlength ts = 12)
    RETURN ()
    SEP (peer_rep shp p (p_set_hs P (hs_randomized (p_hs P) st lic eph reph hash ck ts ri))).

Definition draw_hs_state_spec :=
  DECLARE HR._draw_hs_state
  WITH u: unit
  PRE [ ] PROP () PARAMS () SEP ()
  POST [ tint ] EX st: int,
    PROP (In st hs_states) RETURN (Vint st) SEP ().

(* ------------------------------------------------------------------------------------------------ *)
(* messages                                                                                         *)
(* ------------------------------------------------------------------------------------------------ *)

Definition init_img_spec :=
  DECLARE HH._init_img
  WITH shi: share, i: val, shm: share, m: val, M: init_msg
  PRE [ tptr tuchar, tptr t_init ]
    PROP (writable_share shi; readable_share shm) PARAMS (i; m)
    SEP (hout shi 148 i; init_rep shm m M)
  POST [ tvoid ]
    PROP () RETURN () SEP (hbytes shi (init_bytes M) i; init_rep shm m M).

Definition resp_img_spec :=
  DECLARE HH._resp_img
  WITH shi: share, i: val, shm: share, m: val, M: resp_msg
  PRE [ tptr tuchar, tptr t_resp ]
    PROP (writable_share shi; readable_share shm) PARAMS (i; m)
    SEP (hout shi 92 i; resp_rep shm m M)
  POST [ tvoid ]
    PROP () RETURN () SEP (hbytes shi (resp_bytes M) i; resp_rep shm m M).

Definition cookie_img_spec :=
  DECLARE HK._cookie_img
  WITH shi: share, i: val, shm: share, m: val, M: cookie_msg
  PRE [ tptr tuchar, tptr t_cmsg ]
    PROP (writable_share shi; readable_share shm) PARAMS (i; m)
    SEP (hout shi 64 i; cmsg_rep shm m M)
  POST [ tvoid ]
    PROP () RETURN () SEP (hbytes shi (cookie_msg_bytes M) i; cmsg_rep shm m M).

Definition fill_init_spec :=
  DECLARE HH._fill_init
  WITH shm: share, m: val
  PRE [ tptr t_init ]
    PROP (writable_share shm) PARAMS (m) SEP (@data_at_ Noise.CS shm t_init m)
  POST [ tvoid ] EX M: init_msg,
    PROP (im_ok M) RETURN () SEP (init_rep shm m M).

Definition fill_resp_spec :=
  DECLARE HH._fill_resp
  WITH shm: share, m: val
  PRE [ tptr t_resp ]
    PROP (writable_share shm) PARAMS (m) SEP (@data_at_ Noise.CS shm t_resp m)
  POST [ tvoid ] EX M: resp_msg,
    PROP (rm_ok M) RETURN () SEP (resp_rep shm m M).

Definition fill_cookie_msg_spec :=
  DECLARE HK._fill_cookie_msg
  WITH shm: share, m: val
  PRE [ tptr t_cmsg ]
    PROP (writable_share shm) PARAMS (m) SEP (@data_at_ Cookie.CS shm t_cmsg m)
  POST [ tvoid ] EX M: cookie_msg,
    PROP (cm_ok M) RETURN () SEP (cmsg_rep shm m M).

(* draw_real_clock(): any seconds, nanoseconds in [0, 10^9) *)
Definition draw_real_clock_spec :=
  DECLARE HH._draw_real_clock
  WITH gv: globals, S: shim
  PRE [ ] PROP () PARAMS () GLOBALS (gv) SEP (shim_state gv S)
  POST [ tvoid ] EX sec: int64, EX ns: Z,
    PROP (0 <= ns < 1000000000) RETURN ()
    SEP (shim_state gv (shim_set_real S sec (Int64.repr ns))).

(* ------------------------------------------------------------------------------------------------ *)
(* cookie snapshots (ck_snap at CKS)                                                                *)
(* ------------------------------------------------------------------------------------------------ *)

Definition ck_take_spec :=
  DECLARE HK._ck_take
  WITH shs: share, s: val, shc: share, c: val, C: cookie
  PRE [ tptr t_cksnap, tptr t_cookie ]
    PROP (writable_share shs; readable_share shc) PARAMS (s; c)
    SEP (@data_at_ CKS shs t_cksnap s; cookie_rep shc c C)
  POST [ tvoid ]
    PROP () RETURN () SEP (@data_at CKS shs t_cksnap (cksnap_val C) s; cookie_rep shc c C).

Definition ck_same_spec :=
  DECLARE HK._ck_same
  WITH shs: share, s: val, C0: cookie, shc: share, c: val, C: cookie
  PRE [ tptr t_cksnap, tptr t_cookie ]
    PROP (readable_share shs; readable_share shc) PARAMS (s; c)
    SEP (@data_at CKS shs t_cksnap (cksnap_val C0) s; cookie_rep shc c C)
  POST [ tint ]
    PROP () RETURN (Vint (if cookie_eqb C0 C then Int.one else Int.zero))
    SEP (@data_at CKS shs t_cksnap (cksnap_val C0) s; cookie_rep shc c C).

End Specs.
