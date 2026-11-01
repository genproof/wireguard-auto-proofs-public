(* wg_noise_handshake_create_initiation over the v5 representation: the context of its stage lemmas and the
   state assertion they share.

   The cut of the body into the statements ci_B0 .. ci_B13 is v4's (prot4_ci_defs.v, checked there by
   ci_body_eq / ci_LB_eq).  The stage lemmas (files prot5_ci_s<X>.v) are stated over
   ci5_Delta = func_tycontext f_wg_noise_handshake_create_initiation Vprog Gprot5 nil, with the state
   assertion ci5_A.  ci5_A is v4's ci_A with the read-only globals of the hs_ programs (wg_consts5).  The
   message fields are arbitrary values: they are those of a message, or undefined when the function writes
   into uninitialised memory. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol5.prot_prog5.
Require WgNoise.noise.code WgNoise.shim.code.
Require Export WgNoise.proof.protocol4.prot4_ci_defs.

Section CI.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.
#[local] Existing Instance Noise.CS.

Definition ci5_Gn : funspecs := Gprot5 x25519 aead_enc aead_dec CSw Noise.CS.
Definition ci5_Delta : tycontext := func_tycontext ci_f (QPvarspecs Noise.qp) ci5_Gn nil.

(* The state inside the loop body; the parameters are those of ci_A (prot4_ci_defs.v). *)
Definition ci5_A (gv: globals) (kc: int64) (shm: share) (m: val) (shp: share) (p: val) (shd: share) (wg: val)
  (sid: val) (has: bool) (pub: list byte) (tab: val) (sht: share) (rs ss: list byte) (kp tp: val) (FR: mpred)
  (Pf: Prop) (ret: val) (mtype msender: val) (meph mencs menct: list val)
  (hstate: val) (heph hhash hck: list val) (kv tv: list val) (S: shim) (w: list int64) (T: tstate) : environ -> mpred :=
  PROP (Pf)
  LOCAL (temp I._ret ret; temp I._dst m; temp I._handshake (hs_addr p);
         lvar I._key (tarray tuchar 32) kp; lvar I._timestamp (tarray tuchar 12) tp; gvars gv)
  SEP (field_at shm t_init [StructField I._type; StructField I._header] mtype m;
       field_at shm t_init [StructField I._sender_index] msender m;
       field_at shm t_init [StructField I._unencrypted_ephemeral] meph m;
       field_at shm t_init [StructField I._encrypted_static] mencs m;
       field_at shm t_init [StructField I._encrypted_timestamp] menct m;
       field_at shp t_hs [StructField I._state] hstate (hs_addr p);
       field_at shp t_hs [StructField I._static_identity] sid (hs_addr p);
       field_at shp t_hs [StructField I._ephemeral_private] heph (hs_addr p);
       field_at shp t_hs [StructField I._remote_static] (bytes rs) (hs_addr p);
       field_at shp t_hs [StructField I._precomputed_static_static] (bytes ss) (hs_addr p);
       field_at shp t_hs [StructField I._hash] hhash (hs_addr p);
       field_at shp t_hs [StructField I._chaining_key] hck (hs_addr p);
       field_at shp t_peer [StructField I._device] wg p;
       field_at shd t_sid [StructField I._has_identity] (Val.of_bool has) sid;
       field_at shd t_sid [StructField I._static_public] (bytes pub) sid;
       field_at shd t_dev [StructField I._index_hashtable] tab wg;
       data_at Tsh (tarray tuchar 32) kv kp;
       data_at Tsh (tarray tuchar 12) tv tp;
       itable sht tab T; shim_state4 gv S w; noise_globals gv kc; wg_consts5 gv; FR).

End CI.
