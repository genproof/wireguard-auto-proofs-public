(* The specifications v5 of noise.c and the shim, for the per-law programs of the short handshake laws (hs_).

   v5 = v4 (prot_specs4.v: same names, same model prot_model3.v, same refcount_t warnings) over the
   representation of prot_repr5.v: wg_consts5, device_rep5, peer_rep5, peers_rep5 instead of wg_consts,
   device_rep, peer_rep, peers_rep; init_rep5 / resp_rep5 (macs any) for the messages; create_initiation and
   create_response also accept an uninitialised message buffer; set_static_identity_private_key accepts an
   identity whose private key and flag are uninitialised.  The specifications that mention none of these are
   v4's, unchanged (aliases below).  Only the functions the hs_ laws reach are listed (prot_G5): every
   function of noise.c but handshake_clear, keypair_get, keypairs_clear, expire_current_peer_keypairs,
   received_with_keypair and reset_last_sent_handshake; every function of the shim but refcount_inc,
   ratelimiter_allow, birthdate_has_expired and __crypto_xor.  Bodies: prot_body5_*.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import QuickProof.Env.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.protocol5.prot_repr5.
Require WgNoise.proof.protocol4.prot_specs4.
Require WgNoise.noise.code WgNoise.cookie.code WgNoise.shim.code.
Local Open Scope logic.

Module N := WgNoise.noise.code.
Module Sh := WgNoise.shim.code.

Section Specs.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.

#[local] Existing Instance Noise.CS.

(* v4's specifications, unchanged *)
Definition ktime_get_coarse_boottime_ns_spec := prot_specs4.ktime_get_coarse_boottime_ns_spec.
Definition ktime_get_real_ts64_spec := prot_specs4.ktime_get_real_ts64_spec.
Definition get_random_bytes_spec := prot_specs4.get_random_bytes_spec.
Definition get_random_bytes_wait_spec := prot_specs4.get_random_bytes_wait_spec.
Definition get_random_u32_spec := prot_specs4.get_random_u32_spec.
Definition kzalloc_spec := prot_specs4.kzalloc_spec CSw.
Definition kfree_spec := prot_specs4.kfree_spec CSw.
Definition kfree_sensitive_spec := prot_specs4.kfree_sensitive_spec CSw.
Definition wg_shim_refcount_warn_saturate_spec := prot_specs4.wg_shim_refcount_warn_saturate_spec.
Definition wg_shim_refcount_neg_spec := prot_specs4.wg_shim_refcount_neg_spec.
Definition wg_shim_refcount_inc_not_zero_spec := prot_specs4.wg_shim_refcount_inc_not_zero_spec.
Definition wg_shim_refcount_dec_and_test_spec := prot_specs4.wg_shim_refcount_dec_and_test_spec.
Definition wg_peer_get_maybe_zero_spec := prot_specs4.wg_peer_get_maybe_zero_spec.
Definition wg_shim_peer_release_spec := prot_specs4.wg_shim_peer_release_spec.
Definition wg_peer_put_spec := prot_specs4.wg_peer_put_spec.
Definition wg_index_hashtable_remove_spec := prot_specs4.wg_index_hashtable_remove_spec.
Definition wg_shim_index_in_use_spec := prot_specs4.wg_shim_index_in_use_spec.
Definition wg_index_hashtable_insert_spec := prot_specs4.wg_index_hashtable_insert_spec.
Definition wg_index_hashtable_replace_spec := prot_specs4.wg_index_hashtable_replace_spec.
Definition quickproof_rounddown_pow_of_two_spec := prot_specs4.quickproof_rounddown_pow_of_two_spec.
Definition put_unaligned_be32_spec := prot_specs4.put_unaligned_be32_spec.
Definition put_unaligned_be64_spec := prot_specs4.put_unaligned_be64_spec.
Definition curve25519_generate_secret_spec := prot_specs4.curve25519_generate_secret_spec.
Definition tai64n_now_spec := prot_specs4.tai64n_now_spec.
Definition handshake_zero_spec := prot_specs4.handshake_zero_spec.
Definition keypair_create_spec := prot_specs4.keypair_create_spec CSw.
Definition keypair_free_rcu_spec := prot_specs4.keypair_free_rcu_spec CSw.

(* v4's step results (the models of the five handshake steps) *)
Definition hs_initial := prot_specs4.hs_initial x25519.
Definition ci_res := prot_specs4.ci_res x25519 aead_enc.
Definition cin_res := prot_specs4.cin_res x25519 aead_dec.
Definition cr_res := prot_specs4.cr_res x25519 aead_enc.
Definition cre_res := prot_specs4.cre_res x25519 aead_dec.
Definition bs_res := prot_specs4.bs_res.

(* the specifications over the v5 representation *)
Definition wg_pubkey_hashtable_lookup_spec :=
  DECLARE Sh._wg_pubkey_hashtable_lookup
  WITH gv: globals, S: shim, w: list int64, sht: share, tab: val, head: val, PS: list (val * share * peer), shk: share, pk: val,
       pub: list byte
  PRE [ tptr t_ptab, tptr tuchar ]
    PROP (readable_share sht; readable_share shk; peers_wf PS; Zlength pub = 32; pk_chain head PS;
          peers_refs_ok PS)
    PARAMS (tab; pk) GLOBALS (gv)
    SEP (ptable sht tab head; peers_rep5 PS; bytes_at shk pub pk; shim_state4 gv S w)
  POST [ tptr t_peer ]
    PROP () RETURN (fst (pk_lookup PS pub))
    SEP (ptable sht tab head; peers_rep5 (snd (pk_lookup PS pub)); bytes_at shk pub pk; shim_state4 gv S w).

Definition wg_index_hashtable_lookup_spec :=
  DECLARE Sh._wg_index_hashtable_lookup
  WITH gv: globals, S: shim, w: list int64, sht: share, tab: val, T: tstate, PS: list (val * share * peer), mask: int, idx: int,
       shq: share, q: val, oldq: val
  PRE [ tptr t_itab, tint, tuint, tptr (tptr t_peer) ]
    PROP (readable_share sht; writable_share shq; pool_peers_ok T PS; peers_wf PS; peers_refs_ok PS)
    PARAMS (tab; Vint mask; Vint idx; q) GLOBALS (gv)
    SEP (itable sht tab T; peers_rep5 PS; data_at shq (tptr t_peer) oldq q; shim_state4 gv S w)
  POST [ tptr t_entry_s ]
    PROP ()
    RETURN (match t_lookup T mask idx with Some (a, _) => a | None => nullval end)
    SEP (itable sht tab T;
         peers_rep5 (match t_lookup T mask idx with Some (_, E) => peers_ref PS (e_peer E) | None => PS end);
         data_at shq (tptr t_peer) (match t_lookup T mask idx with Some (_, E) => e_peer E | None => oldq end) q;
         shim_state4 gv S w).

Definition wg_noise_init_spec :=
  DECLARE N._wg_noise_init
  WITH gv: globals, h: list byte, ck: list byte, kc: int64
  PRE [ ]
    PROP () PARAMS () GLOBALS (gv)
    SEP (noise_globals_raw gv h ck kc; wg_consts5 gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (noise_globals gv kc; wg_consts5 gv).

Definition hmac_spec :=
  DECLARE N._hmac
  WITH gv: globals, alias: bool, osh: share, out: val, ish: share, inp: val, buf: list val,
       data: list byte, ksh: share, kp: val, key: list byte
  PRE [ tptr tuchar, tptr tuchar, tptr tuchar, tulong, tulong ]
    PROP (writable_share osh; readable_share ish; readable_share ksh;
          Zlength data <= Int64.max_signed; Zlength key <= Int64.max_signed;
          alias = true -> (out = inp /\ 32 <= Zlength buf /\ Zlength data <= Zlength buf /\
                           sublist 0 (Zlength data) buf = bytes data))
    PARAMS (out; inp; kp; Vlong (Int64.repr (Zlength data)); Vlong (Int64.repr (Zlength key))) GLOBALS (gv)
    SEP (if alias then data_at osh (tarray tuchar (Zlength buf)) buf out
         else (data_at_ osh (tarray tuchar 32) out * b2s_bytes ish data inp);
         bytes_at ksh key kp; wg_consts5 gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (if alias then data_at osh (tarray tuchar (Zlength buf)) (bytes (hmac key data) ++ sublist 32 (Zlength buf) buf) out
         else (bytes_at osh (hmac key data) out * b2s_bytes ish data inp);
         bytes_at ksh key kp; wg_consts5 gv).

Definition kdf_spec :=
  DECLARE N._kdf
  WITH gv: globals, alias: bool, d1: val, d2: val, d3: val, l2: Z, l3: Z, sh1: share, sh2: share,
       sh3: share, shd: share, dp: val, data: list byte, shc: share, ckp: val, ck: list byte
  PRE [ tptr tuchar, tptr tuchar, tptr tuchar, tptr tuchar, tulong, tulong, tulong, tulong, tptr tuchar ]
    PROP (writable_share sh1; writable_share sh2; writable_share sh3; readable_share shd;
          if alias then writable_share shc else readable_share shc;
          Zlength ck = 32; Zlength data <= Int64.max_signed;
          0 <= l2 <= Int64.max_unsigned; 0 <= l3 <= Int64.max_unsigned;
          d2 <> nullval -> l2 = 32; d3 <> nullval -> l3 = 32; alias = true -> d1 = ckp)
    PARAMS (d1; d2; d3; dp; Vlong (Int64.repr 32); Vlong (Int64.repr l2); Vlong (Int64.repr l3);
            Vlong (Int64.repr (Zlength data)); ckp) GLOBALS (gv)
    SEP (if alias then bytes_at shc ck ckp
         else (bytes_at shc ck ckp * data_at_ sh1 (tarray tuchar 32) d1);
         if eq_dec d2 nullval then emp else data_at_ sh2 (tarray tuchar 32) d2;
         if eq_dec d2 nullval then emp else if eq_dec d3 nullval then emp
         else data_at_ sh3 (tarray tuchar 32) d3;
         b2s_bytes shd data dp; wg_consts5 gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (if alias then bytes_at shc (kdf1 ck data) ckp
         else (bytes_at shc ck ckp * bytes_at sh1 (kdf1 ck data) d1);
         if eq_dec d2 nullval then emp else bytes_at sh2 (kdf2 ck data) d2;
         if eq_dec d2 nullval then emp else if eq_dec d3 nullval then emp
         else bytes_at sh3 (kdf3 ck data) d3;
         b2s_bytes shd data dp; wg_consts5 gv).

Definition derive_keys_spec :=
  DECLARE N._derive_keys
  WITH gv: globals, S: shim, w: list int64, sh1: share, f: val, sh2: share, s: val, shc: share, ckp: val, ck: list byte
  PRE [ tptr t_sym, tptr t_sym, tptr tuchar ]
    PROP (writable_share sh1; writable_share sh2; readable_share shc; Zlength ck = 32)
    PARAMS (f; s; ckp) GLOBALS (gv)
    SEP (data_at_ sh1 t_sym f; data_at_ sh2 t_sym s; bytes_at shc ck ckp; shim_state4 gv S w; wg_consts5 gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (symkey_rep sh1 f (mkSym (kdf1 ck []) (s_boot S) true);
         symkey_rep sh2 s (mkSym (kdf2 ck []) (s_boot S) true);
         bytes_at shc ck ckp; shim_state4 gv S w; wg_consts5 gv).

Definition mix_dh_spec :=
  DECLARE N._mix_dh
  WITH gv: globals, shc: share, ckp: val, ck: list byte, shk: share, kp: val, shv: share, pv: val,
       priv: list byte, shb: share, pb: val, pub: list byte
  PRE [ tptr tuchar, tptr tuchar, tptr tuchar, tptr tuchar ]
    PROP (writable_share shc; writable_share shk; readable_share shv; readable_share shb;
          Zlength ck = 32; Zlength priv = 32; Zlength pub = 32)
    PARAMS (ckp; kp; pv; pb) GLOBALS (gv)
    SEP (bytes_at shc ck ckp; if eq_dec kp nullval then emp else data_at_ shk (tarray tuchar 32) kp;
         bytes_at shv priv pv; bytes_at shb pub pb; wg_consts5 gv)
  POST [ tbool ]
    PROP () RETURN (Val.of_bool (dh_ok x25519 priv pub))
    SEP (bytes_at shc (if dh_ok x25519 priv pub then kdf1 ck (x25519 priv pub) else ck) ckp;
         if eq_dec kp nullval then emp
         else if dh_ok x25519 priv pub then bytes_at shk (kdf2 ck (x25519 priv pub)) kp
         else data_at_ shk (tarray tuchar 32) kp;
         bytes_at shv priv pv; bytes_at shb pub pb; wg_consts5 gv).

Definition mix_precomputed_dh_spec :=
  DECLARE N._mix_precomputed_dh
  WITH gv: globals, kc: int64, shc: share, ckp: val, ck: list byte, shk: share, kp: val, shp: share,
       pp: val, pre: list byte
  PRE [ tptr tuchar, tptr tuchar, tptr tuchar ]
    PROP (writable_share shc; writable_share shk; readable_share shp; Zlength ck = 32; Zlength pre = 32)
    PARAMS (ckp; kp; pp) GLOBALS (gv)
    SEP (bytes_at shc ck ckp; data_at_ shk (tarray tuchar 32) kp; bytes_at shp pre pp;
         noise_globals gv kc; wg_consts5 gv)
  POST [ tbool ]
    PROP () RETURN (Val.of_bool (memneq_bool pre zeros32))
    SEP (bytes_at shc (if memneq_bool pre zeros32 then kdf1 ck pre else ck) ckp;
         if memneq_bool pre zeros32 then bytes_at shk (kdf2 ck pre) kp else data_at_ shk (tarray tuchar 32) kp;
         bytes_at shp pre pp; noise_globals gv kc; wg_consts5 gv).

Definition mix_hash_spec :=
  DECLARE N._mix_hash
  WITH gv: globals, shh: share, hp: val, h: list byte, shs: share, sp: val, src: list byte
  PRE [ tptr tuchar, tptr tuchar, tulong ]
    PROP (writable_share shh; readable_share shs; Zlength h = 32; Zlength src <= Int64.max_signed)
    PARAMS (hp; sp; Vlong (Int64.repr (Zlength src))) GLOBALS (gv)
    SEP (bytes_at shh h hp; b2s_bytes shs src sp; wg_consts5 gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (bytes_at shh (mix_hash h src) hp; b2s_bytes shs src sp; wg_consts5 gv).

Definition mix_psk_spec :=
  DECLARE N._mix_psk
  WITH gv: globals, shc: share, ckp: val, ck: list byte, shh: share, hp: val, h: list byte,
       shk: share, kp: val, shp: share, pp: val, psk: list byte
  PRE [ tptr tuchar, tptr tuchar, tptr tuchar, tptr tuchar ]
    PROP (writable_share shc; writable_share shh; writable_share shk; readable_share shp;
          Zlength ck = 32; Zlength h = 32; Zlength psk = 32)
    PARAMS (ckp; hp; kp; pp) GLOBALS (gv)
    SEP (bytes_at shc ck ckp; bytes_at shh h hp; data_at_ shk (tarray tuchar 32) kp; bytes_at shp psk pp;
         wg_consts5 gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (bytes_at shc (kdf1 ck psk) ckp; bytes_at shh (mix_hash h (kdf2 ck psk)) hp;
         bytes_at shk (kdf3 ck psk) kp; bytes_at shp psk pp; wg_consts5 gv).

Definition handshake_init_spec :=
  DECLARE N._handshake_init
  WITH gv: globals, kc: int64, shc: share, ckp: val, shh: share, hp: val, shr: share, rp: val,
       rs: list byte
  PRE [ tptr tuchar, tptr tuchar, tptr tuchar ]
    PROP (writable_share shc; writable_share shh; readable_share shr; Zlength rs = 32)
    PARAMS (ckp; hp; rp) GLOBALS (gv)
    SEP (data_at_ shc (tarray tuchar 32) ckp; data_at_ shh (tarray tuchar 32) hp; bytes_at shr rs rp;
         noise_globals gv kc; wg_consts5 gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (bytes_at shc init_ck ckp; bytes_at shh (mix_hash init_hash rs) hp; bytes_at shr rs rp;
         noise_globals gv kc; wg_consts5 gv).

Definition message_encrypt_spec :=
  DECLARE N._message_encrypt
  WITH gv: globals, shd: share, dp: val, shs: share, sp: val, m: list byte, shk: share, kp: val,
       key: list byte, shh: share, hp: val, h: list byte
  PRE [ tptr tuchar, tptr tuchar, tulong, tptr tuchar, tptr tuchar ]
    PROP (writable_share shd; readable_share shs; readable_share shk; writable_share shh;
          Zlength m <= Int.max_unsigned - 16; Zlength key = 32; Zlength h = 32)
    PARAMS (dp; sp; Vlong (Int64.repr (Zlength m)); kp; hp) GLOBALS (gv)
    SEP (data_at_ shd (tarray tuchar (Zlength m + 16)) dp; prim_bytes shs m sp; bytes_at shk key kp;
         bytes_at shh h hp; wg_consts5 gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at shd (tarray tuchar (Zlength m + 16)) (bytes (aead_enc key 0 h m)) dp;
         prim_bytes shs m sp; bytes_at shk key kp;
         bytes_at shh (mix_hash h (aead_enc key 0 h m)) hp; wg_consts5 gv).

Definition message_decrypt_spec :=
  DECLARE N._message_decrypt
  WITH gv: globals, shd: share, dp: val, old: list val, shs: share, sp: val, c: list byte, shk: share,
       kp: val, key: list byte, shh: share, hp: val, h: list byte
  PRE [ tptr tuchar, tptr tuchar, tulong, tptr tuchar, tptr tuchar ]
    PROP (writable_share shd; readable_share shs; readable_share shk; writable_share shh;
          Zlength c <= Int.max_unsigned; Zlength key = 32; Zlength h = 32;
          Zlength old = Z.max 0 (Zlength c - 16))
    PARAMS (dp; sp; Vlong (Int64.repr (Zlength c)); kp; hp) GLOBALS (gv)
    SEP (out_bytes shd old dp; prim_bytes shs c sp; bytes_at shk key kp; bytes_at shh h hp; wg_consts5 gv)
  POST [ tbool ]
    PROP ()
    RETURN (Val.of_bool (match aead_dec key 0 h c with Some _ => true | None => false end))
    SEP (out_bytes shd (match aead_dec key 0 h c with Some pt => bytes pt | None => old end) dp;
         prim_bytes shs c sp; bytes_at shk key kp;
         bytes_at shh (match aead_dec key 0 h c with Some _ => mix_hash h c | None => h end) hp;
         wg_consts5 gv).

Definition message_ephemeral_spec :=
  DECLARE N._message_ephemeral
  WITH gv: globals, alias: bool, shd: share, dp: val, shs: share, sp: val, e: list byte, shc: share,
       ckp: val, ck: list byte, shh: share, hp: val, h: list byte
  PRE [ tptr tuchar, tptr tuchar, tptr tuchar, tptr tuchar ]
    PROP (writable_share shd; readable_share shs; writable_share shc; writable_share shh;
          Zlength e = 32; Zlength ck = 32; Zlength h = 32; alias = true -> dp = sp)
    PARAMS (dp; sp; ckp; hp) GLOBALS (gv)
    SEP (if alias then bytes_at shs e sp else (data_at_ shd (tarray tuchar 32) dp * bytes_at shs e sp);
         bytes_at shc ck ckp; bytes_at shh h hp; wg_consts5 gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (if alias then bytes_at shs e sp else (bytes_at shd e dp * bytes_at shs e sp);
         bytes_at shc (kdf1 ck e) ckp; bytes_at shh (mix_hash h e) hp; wg_consts5 gv).

(* wg_noise_set_static_identity_private_key(sid, raw): static_private, has_identity and the lock any; only
   static_public must hold bytes (pub), which it keeps when raw is zero (identity_of reads only id_pub of the
   old identity) *)
Definition wg_noise_set_static_identity_private_key_spec :=
  DECLARE N._wg_noise_set_static_identity_private_key
  WITH gv: globals, sh: share, sid: val, pub: list byte, shk: share, pk: val, raw: list byte
  PRE [ tptr t_sid, tptr tuchar ]
    PROP (writable_share sh; readable_share shk; Zlength raw = 32; Zlength pub = 32) PARAMS (sid; pk) GLOBALS (gv)
    SEP (field_at sh t_sid [StructField I._static_public] (bytes pub) sid;
         field_at_ sh t_sid [StructField I._static_private] sid;
         field_at_ sh t_sid [StructField I._lock] sid;
         field_at_ sh t_sid [StructField I._has_identity] sid;
         spacer sh 69 72 sid;   (* the struct's tail padding: identity_rep's data_at owns it *)
         bytes_at shk raw pk; wg_consts5 gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (identity_rep sh sid (identity_of x25519 (mkId pub zeros32 false) raw); bytes_at shk raw pk;
         wg_consts5 gv).

Definition wg_noise_precompute_static_static_spec :=
  DECLARE N._wg_noise_precompute_static_static
  WITH gv: globals, sh: share, p: val, H: handshake, shi: share, ID: identity
  PRE [ tptr t_peer ]
    PROP (writable_share sh; readable_share shi; field_compatible t_peer [] p) PARAMS (p) GLOBALS (gv)
    SEP (hs_rep sh (hs_addr p) H; identity_rep shi (hs_sid H) ID; wg_consts5 gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (hs_rep sh (hs_addr p) (hs_set_ss H (precomputed x25519 ID (hs_rstatic H)));
         identity_rep shi (hs_sid H) ID; wg_consts5 gv).

Definition wg_noise_handshake_init_spec :=
  DECLARE N._wg_noise_handshake_init
  WITH gv: globals, sh: share, p: val, shi: share, sid: val, ID: identity, shk: share, pubp: val,
       pub: list byte, shq: share, pskp: val, psk: list byte
  PRE [ tptr t_hs, tptr t_sid, tptr tuchar, tptr tuchar, tptr t_peer ]
    PROP (writable_share sh; readable_share shi; readable_share shk; readable_share shq;
          field_compatible t_peer [] p; Zlength pub = 32; pskp <> nullval -> Zlength psk = 32)
    PARAMS (hs_addr p; sid; pubp; pskp; p) GLOBALS (gv)
    SEP (data_at_ sh t_hs (hs_addr p); identity_rep shi sid ID; bytes_at shk pub pubp;
         if eq_dec pskp nullval then emp else bytes_at shq psk pskp; wg_consts5 gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (hs_rep sh (hs_addr p) (hs_initial ID sid pub (if eq_dec pskp nullval then zeros32 else psk));
         entry_out sh (hs_addr p) (mkEntry p IDX_HANDSHAKE Int.zero);
         identity_rep shi sid ID; bytes_at shk pub pubp;
         if eq_dec pskp nullval then emp else bytes_at shq psk pskp; wg_consts5 gv).

Definition keypair_free_kref_spec :=
  DECLARE N._keypair_free_kref
  WITH gv: globals, S: shim, w: list int64, k: val, K: keypair, E: entry, shp: share, p: val, P: peer, shd: share,
       wg: val, D: device, sht: share, T: tstate
  PRE [ tptr t_kref ]
    PROP (readable_share shp; readable_share shd; writable_share sht; p_device P = wg;
          sfind (t_D T) k = Some (Ews, E); e_peer E = p)
    PARAMS (offset_val OFS_KP_REFCOUNT k) GLOBALS (gv)
    SEP (mem_mgr gv; shim_state4 gv S w; keypair_rep CSw k K; peer_rep5 shp p P; device_rep5 shd wg D;
         itable sht (d_itab D) T)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (mem_mgr gv; shim_state4 gv (shim_free S) w; peer_rep5 shp p P; device_rep5 shd wg D;
         itable sht (d_itab D) (t_free T k)).

Definition wg_noise_keypair_put_spec :=
  DECLARE N._wg_noise_keypair_put
  WITH gv: globals, S: shim, w: list int64, KS: list (val * keypair), T: tstate, k: val, unref: bool, shp: share,
       p: val, P: peer, shd: share, wg: val, D: device, sht: share
  PRE [ tptr t_kp, tbool ]
    PROP (readable_share shp; readable_share shd; writable_share sht; p_device P = wg;
          kps_in_pool T p KS; k = nullval \/ In k (map fst KS))
    PARAMS (k; Val.of_bool unref) GLOBALS (gv)
    SEP (mem_mgr gv; shim_state4 gv S w; keypairs_rep CSw KS; peer_rep5 shp p P; device_rep5 shd wg D;
         itable sht (d_itab D) T)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (mem_mgr gv; shim_state4 gv (kw_S (kp_put k unref (mkKW KS T S))) (kp_put_warn k KS w);
         keypairs_rep CSw (kw_KS (kp_put k unref (mkKW KS T S)));
         peer_rep5 shp p P; device_rep5 shd wg D; itable sht (d_itab D) (kw_T (kp_put k unref (mkKW KS T S)))).

Definition add_new_keypair_spec :=
  DECLARE N._add_new_keypair
  WITH gv: globals, S: shim, w: list int64, KS: list (val * keypair), T: tstate, shp: share, p: val, P: peer,
       shd: share, wg: val, D: device, sht: share, new: val, K: keypair
  PRE [ tptr t_kps, tptr t_kp ]
    PROP (writable_share shp; readable_share shd; writable_share sht; p_device P = wg;
          kps_in_pool T p KS; slots_ok P KS; afind KS new = Some K;
          new <> p_cur P; new <> p_prev P; new <> p_next P)
    PARAMS (kps_addr p; new) GLOBALS (gv)
    SEP (mem_mgr gv; shim_state4 gv S w; keypairs_rep CSw KS; peer_rep5 shp p P; device_rep5 shd wg D;
         itable sht (d_itab D) T)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (mem_mgr gv; shim_state4 gv (kw_S (snd (add_new_keypair_model P new (kp_init K) (mkKW KS T S)))) (add_new_keypair_warn P new (kp_init K) (mkKW KS T S) w);
         keypairs_rep CSw (kw_KS (snd (add_new_keypair_model P new (kp_init K) (mkKW KS T S))));
         peer_rep5 shp p (fst (add_new_keypair_model P new (kp_init K) (mkKW KS T S)));
         device_rep5 shd wg D;
         itable sht (d_itab D) (kw_T (snd (add_new_keypair_model P new (kp_init K) (mkKW KS T S))))).

(* create_initiation(m, &p->handshake): the message buffer m is a message (Mo = Some M) or uninitialised
   (None: the model starts from init_msg0); on success it is the model's message (macs any) *)
Definition wg_noise_handshake_create_initiation_spec :=
  DECLARE N._wg_noise_handshake_create_initiation
  WITH gv: globals, S: shim, w: list int64, kc: int64, shm: share, m: val, Mo: option init_msg, shp: share, p: val, P: peer,
       shd: share, wg: val, D: device, sht: share, T: tstate
  PRE [ tptr t_init, tptr t_hs ]
    PROP (writable_share shm; writable_share shp; readable_share shd; writable_share sht;
          p_device P = wg; hs_sid (p_hs P) = id_addr wg; hs_in_pool T p)
    PARAMS (m; hs_addr p) GLOBALS (gv)
    SEP (init_opt_rep shm m Mo; peer_rep5 shp p P; device_rep5 shd wg D; itable sht (d_itab D) T;
         shim_state4 gv S w; noise_globals gv kc; wg_consts5 gv)
  POST [ tbool ] EX r: list byte, EX idx: int,
    PROP (Zlength r = 32; fst (fst (ci_res D P (init_of Mo) S r idx)) = true -> t_fresh T (hs_addr p) idx)
    RETURN (Val.of_bool (fst (fst (ci_res D P (init_of Mo) S r idx))))
    SEP (init_opt_rep shm m (opt_after (fst (fst (ci_res D P (init_of Mo) S r idx))) Mo
                                   (snd (fst (ci_res D P (init_of Mo) S r idx))));
         peer_rep5 shp p (p_set_hs P (snd (ci_res D P (init_of Mo) S r idx)));
         device_rep5 shd wg D;
         itable sht (d_itab D) (if fst (fst (ci_res D P (init_of Mo) S r idx)) then t_insert T (hs_addr p) idx else T);
         shim_state4 gv (if id_has (d_id D)
                        then (if fst (fst (ci_res D P (init_of Mo) S r idx)) then shim_u32 (shim_draw S r) idx
                              else shim_draw S r)
                        else S) w;
         noise_globals gv kc; wg_consts5 gv).

Definition wg_noise_handshake_consume_initiation_spec :=
  DECLARE N._wg_noise_handshake_consume_initiation
  WITH gv: globals, S: shim, w: list int64, kc: int64, shm: share, m: val, M: init_msg, shd: share, wg: val, D: device,
       shpt: share, head: val, PS: list (val * share * peer)
  PRE [ tptr t_init, tptr t_dev ]
    PROP (readable_share shm; readable_share shd; readable_share shpt; peers_wf PS; pk_chain head PS;
          (* (s64)last_initiation_consumption + 20 ms: a signed addition (VST checks no overflow) *)
          Forall (fun x => match x with (_, _, P) =>
                    Int64.signed (hs_lic (p_hs P)) <= Int64.max_signed - 20000000 end) PS;
          (* every peer holds fewer than INT_MAX references (L03), so the lookup's
             reference and its put on rejection leave the count as it was (no saturation) *)
          peers_refs_ok PS)
    PARAMS (m; wg) GLOBALS (gv)
    SEP (init_rep5 shm m M; device_rep5 shd wg D; ptable shpt (d_ptab D) head; peers_rep5 PS;
         shim_state4 gv S w; noise_globals gv kc; wg_consts5 gv)
  POST [ tptr t_peer ]
    PROP () RETURN (peer_result (cin_res D PS M S))
    SEP (init_rep5 shm m M; device_rep5 shd wg D; ptable shpt (d_ptab D) head;
         peers_rep5 (peers_after PS (cin_res D PS M S));
         shim_state4 gv S w; noise_globals gv kc; wg_consts5 gv).

(* create_response(m, &p->handshake): m a message (Some M) or uninitialised (None), as create_initiation *)
Definition wg_noise_handshake_create_response_spec :=
  DECLARE N._wg_noise_handshake_create_response
  WITH gv: globals, S: shim, w: list int64, shm: share, m: val, Mo: option resp_msg, shp: share, p: val, P: peer,
       shd: share, wg: val, D: device, sht: share, T: tstate
  PRE [ tptr t_resp, tptr t_hs ]
    PROP (writable_share shm; writable_share shp; readable_share shd; writable_share sht;
          p_device P = wg; hs_in_pool T p)
    PARAMS (m; hs_addr p) GLOBALS (gv)
    SEP (resp_opt_rep shm m Mo; peer_rep5 shp p P; device_rep5 shd wg D; itable sht (d_itab D) T;
         shim_state4 gv S w; wg_consts5 gv)
  POST [ tbool ] EX r: list byte, EX idx: int,
    PROP (Zlength r = 32; fst (fst (cr_res P (resp_of Mo) r idx)) = true -> t_fresh T (hs_addr p) idx)
    RETURN (Val.of_bool (fst (fst (cr_res P (resp_of Mo) r idx))))
    SEP (resp_opt_rep shm m (opt_after (fst (fst (cr_res P (resp_of Mo) r idx))) Mo
                                   (snd (fst (cr_res P (resp_of Mo) r idx))));
         peer_rep5 shp p (p_set_hs P (snd (cr_res P (resp_of Mo) r idx)));
         device_rep5 shd wg D;
         itable sht (d_itab D) (if fst (fst (cr_res P (resp_of Mo) r idx)) then t_insert T (hs_addr p) idx else T);
         shim_state4 gv (if Int.eq (hs_state (p_hs P)) HS_CONSUMED_INITIATION
                        then (if fst (fst (cr_res P (resp_of Mo) r idx)) then shim_u32 (shim_draw S r) idx
                              else shim_draw S r)
                        else S) w;
         wg_consts5 gv).

Definition wg_noise_handshake_consume_response_spec :=
  DECLARE N._wg_noise_handshake_consume_response
  WITH gv: globals, S: shim, w: list int64, shm: share, m: val, M: resp_msg, shd: share, wg: val, D: device,
       sht: share, T: tstate, PS: list (val * share * peer)
  PRE [ tptr t_resp, tptr t_dev ]
    PROP (readable_share shm; readable_share shd; writable_share sht; pool_peers_ok T PS; peers_wf PS;
          peers_refs_ok PS)
    PARAMS (m; wg) GLOBALS (gv)
    SEP (resp_rep5 shm m M; device_rep5 shd wg D; itable sht (d_itab D) T; peers_rep5 PS;
         shim_state4 gv S w; wg_consts5 gv)
  POST [ tptr t_peer ]
    PROP () RETURN (peer_result (cre_res D T PS M))
    SEP (resp_rep5 shm m M; device_rep5 shd wg D; itable sht (d_itab D) T;
         peers_rep5 (peers_after PS (cre_res D T PS M));
         shim_state4 gv S w; wg_consts5 gv).

Definition wg_noise_handshake_begin_session_spec :=
  DECLARE N._wg_noise_handshake_begin_session
  WITH gv: globals, S: shim, w: list int64, kc: int64, KS: list (val * keypair), T: tstate, shp: share, p: val,
       P: peer, shd: share, wg: val, D: device, sht: share
  PRE [ tptr t_hs, tptr t_kps ]
    PROP (writable_share shp; readable_share shd; writable_share sht; p_device P = wg;
          field_compatible t_peer [] p; hs_in_pool T p; kps_in_pool T p KS; slots_ok P KS)
    PARAMS (hs_addr p; kps_addr p) GLOBALS (gv)
    SEP (mem_mgr gv; shim_state4 gv S w; noise_globals gv kc; wg_consts5 gv; keypairs_rep CSw KS;
         peer_rep5 shp p P; device_rep5 shd wg D; itable sht (d_itab D) T)
  POST [ tbool ] EX k: val,
    PROP (s_failnext S = true -> k = nullval;
          k <> nullval -> ~ In k (saddrs (t_D T)) /\ ~ In k (map fst KS))
    RETURN (Val.of_bool (fst (fst (fst (bs_res P p k kc KS T S)))))
    SEP (mem_mgr gv; shim_state4 gv (kw_S (snd (fst (bs_res P p k kc KS T S)))) (begin_session_warn P (hs_addr p) k kc (mkKW KS T S) w);
         noise_globals gv (snd (bs_res P p k kc KS T S)); wg_consts5 gv;
         keypairs_rep CSw (kw_KS (snd (fst (bs_res P p k kc KS T S))));
         peer_rep5 shp p (snd (fst (fst (bs_res P p k kc KS T S))));
         device_rep5 shd wg D;
         itable sht (d_itab D) (kw_T (snd (fst (bs_res P p k kc KS T S))))).

Definition prot_G5 : funspecs :=
  [quickproof_rounddown_pow_of_two_spec;
   put_unaligned_be32_spec;
   put_unaligned_be64_spec;
   curve25519_generate_secret_spec;
   wg_noise_init_spec;
   wg_noise_precompute_static_static_spec;
   wg_noise_handshake_init_spec;
   handshake_zero_spec;
   keypair_create_spec;
   keypair_free_rcu_spec;
   keypair_free_kref_spec;
   wg_noise_keypair_put_spec;
   add_new_keypair_spec;
   wg_noise_set_static_identity_private_key_spec;
   hmac_spec;
   kdf_spec;
   derive_keys_spec;
   mix_dh_spec;
   mix_precomputed_dh_spec;
   mix_hash_spec;
   mix_psk_spec;
   handshake_init_spec;
   message_encrypt_spec;
   message_decrypt_spec;
   message_ephemeral_spec;
   tai64n_now_spec;
   wg_noise_handshake_create_initiation_spec;
   wg_noise_handshake_consume_initiation_spec;
   wg_noise_handshake_create_response_spec;
   wg_noise_handshake_consume_response_spec;
   wg_noise_handshake_begin_session_spec;
   ktime_get_coarse_boottime_ns_spec;
   ktime_get_real_ts64_spec;
   get_random_bytes_spec;
   get_random_bytes_wait_spec;
   get_random_u32_spec;
   kzalloc_spec;
   kfree_spec;
   kfree_sensitive_spec;
   wg_shim_refcount_warn_saturate_spec;
   wg_shim_refcount_neg_spec;
   wg_shim_refcount_inc_not_zero_spec;
   wg_shim_refcount_dec_and_test_spec;
   wg_peer_get_maybe_zero_spec;
   wg_shim_peer_release_spec;
   wg_peer_put_spec;
   wg_pubkey_hashtable_lookup_spec;
   wg_index_hashtable_remove_spec;
   wg_shim_index_in_use_spec;
   wg_index_hashtable_insert_spec;
   wg_index_hashtable_replace_spec;
   wg_index_hashtable_lookup_spec].

End Specs.
