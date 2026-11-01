(* wg_noise_handshake_create_initiation: the stages of the body and the state
   assertion they share.

   The loop body of `do { ... } while (0)` is cut into the statements ci_B1 .. ci_B13 (taken from the Clight,
   ci_body_eq checks the cut).  The stage lemmas (files prot4_ci_s<X>.v) are stated over
   ci_Delta = func_tycontext f_wg_noise_handshake_create_initiation Vprog Gn nil, with the state
   assertion ci_A: the fields the function touches as separate field_at's, everything else in an
   opaque frame FR.  The stage lemmas know nothing of the model: their outputs are variables with
   equations, and their failure exits (break) go to `RA_normal R` through a hypothesis. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol4.prot_prog4.
Require WgNoise.noise.code WgNoise.cookie.code WgNoise.shim.code.

(* ------------------------------------------------------------------------------------------------ *)
(* The statements                                                                                   *)
(* ------------------------------------------------------------------------------------------------ *)

Definition ci_f := WgNoise.noise.code.f_wg_noise_handshake_create_initiation.

Definition ci_body : statement := Eval cbv beta iota delta [ci_f WgNoise.noise.code.f_wg_noise_handshake_create_initiation fn_body] in fn_body ci_f.

(* fn_body = Ssequence ci_B0 (Ssequence (Sloop ci_LB Sbreak) ci_END) *)
Definition ci_B0 : statement := Eval cbv beta iota delta [ci_body] in
  match ci_body with Ssequence s _ => s | _ => Sskip end.
Definition ci_LB : statement := Eval cbv beta iota delta [ci_body] in
  match ci_body with Ssequence _ (Ssequence (Sloop s _) _) => s | _ => Sskip end.
Definition ci_END : statement := Eval cbv beta iota delta [ci_body] in
  match ci_body with Ssequence _ (Ssequence _ s) => s | _ => Sskip end.

(* the loop body: Ssequence B1 (Ssequence B2 ( ... (Ssequence B12 B13))) *)
Definition ci_nth (n: nat) : statement :=
  let fix go (k: nat) (s: statement) : statement :=
    match k, s with
    | O, Ssequence a _ => a
    | O, s => s
    | S k', Ssequence _ b => go k' b
    | S _, _ => Sskip
    end in go n ci_LB.

Definition ci_B1 : statement := Eval cbv beta iota delta [ci_nth ci_LB] in ci_nth 0.   (* has_identity check *)
Definition ci_B2 : statement := Eval cbv beta iota delta [ci_nth ci_LB] in ci_nth 1.   (* dst->header.type = 1 *)
Definition ci_B3 : statement := Eval cbv beta iota delta [ci_nth ci_LB] in ci_nth 2.   (* handshake_init *)
Definition ci_B4 : statement := Eval cbv beta iota delta [ci_nth ci_LB] in ci_nth 3.   (* generate_secret *)
Definition ci_B5 : statement := Eval cbv beta iota delta [ci_nth ci_LB] in ci_nth 4.   (* generate_public; break *)
Definition ci_B6 : statement := Eval cbv beta iota delta [ci_nth ci_LB] in ci_nth 5.   (* message_ephemeral *)
Definition ci_B7 : statement := Eval cbv beta iota delta [ci_nth ci_LB] in ci_nth 6.   (* mix_dh; break *)
Definition ci_B8 : statement := Eval cbv beta iota delta [ci_nth ci_LB] in ci_nth 7.   (* message_encrypt static *)
Definition ci_B9 : statement := Eval cbv beta iota delta [ci_nth ci_LB] in ci_nth 8.   (* mix_precomputed_dh; break *)
Definition ci_B10 : statement := Eval cbv beta iota delta [ci_nth ci_LB] in ci_nth 9.  (* tai64n_now *)
Definition ci_B11 : statement := Eval cbv beta iota delta [ci_nth ci_LB] in ci_nth 10. (* message_encrypt timestamp *)
Definition ci_B12 : statement := Eval cbv beta iota delta [ci_nth ci_LB] in ci_nth 11. (* index insert; sender_index *)
Definition ci_B13 : statement := Eval cbv beta iota delta [ci_LB] in
  match ci_LB with
  | Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _
    (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ s))))))))))) => s
  | _ => Sskip end.                                                                    (* state = 1; ret = 1 *)

Lemma ci_body_eq : ci_body = Ssequence ci_B0 (Ssequence (Sloop ci_LB Sbreak) ci_END).
Proof. reflexivity. Qed.

Lemma ci_LB_eq : ci_LB =
  Ssequence ci_B1 (Ssequence ci_B2 (Ssequence ci_B3 (Ssequence ci_B4 (Ssequence ci_B5 (Ssequence ci_B6
  (Ssequence ci_B7 (Ssequence ci_B8 (Ssequence ci_B9 (Ssequence ci_B10 (Ssequence ci_B11
  (Ssequence ci_B12 ci_B13))))))))))).
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------------------------------------ *)
(* The context and the state                                                                        *)
(* ------------------------------------------------------------------------------------------------ *)

Section CI.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.
#[local] Existing Instance Noise.CS.

Definition ci_Gn : funspecs := Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS.
Definition ci_Delta : tycontext := func_tycontext ci_f (QPvarspecs Noise.qp) ci_Gn nil.

(* The state inside the loop body.
   Fixed: gv; the message m (share shm); the peer p (share shp) and its handshake h = hs_addr p; the device
   wg (share shd) with its identity at sid (has_identity = has, static_public = pub) and its index table
   tab; the table's share sht; the handshake's remote static rs and precomputed static-static ss; the
   locals key and timestamp (addresses kp, tp); noise.c's globals (kc); the frame FR (the rest of the
   message, peer and device).
   Varying: Pf (a pure fact a stage establishes); ret; the message fields mtype, msender, meph, mencs,
   menct; the handshake fields hstate, heph, hhash, hck; the contents kv, tv of key and timestamp; the
   shim S; the table T. *)
Definition ci_A (gv: globals) (kc: int64) (shm: share) (m: val) (shp: share) (p: val) (shd: share) (wg: val)
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
       itable sht tab T; shim_state4 gv S w; noise_globals gv kc; wg_consts gv; FR).

End CI.
