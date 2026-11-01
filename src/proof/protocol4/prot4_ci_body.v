(* the body group `create_init` of the protocol piece v4 = v3's
   prot_body3_create_init.v re-proved against the v4 specifications (prot_specs4.v, context Gprot4 of prot_prog4.v: the
   shim's refcount_t warnings exact).  Owner of the statement: the config_any. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol4.prot_prog4.
Require WgNoise.noise.code WgNoise.cookie.code WgNoise.shim.code.
Require Import WgNoise.proof.blake2s.model.
Require Import WgNoise.proof.protocol4.prot4_ci_defs.
Require Import WgNoise.proof.protocol4.prot4_ci_sA.
Require Import WgNoise.proof.protocol4.prot4_ci_sB.
Require Import WgNoise.proof.protocol4.prot4_ci_sC.
Require Import WgNoise.proof.protocol4.prot4_ci_sD.
Require Import WgNoise.proof.protocol4.prot4_ci_sE.
Require Import WgNoise.proof.protocol4.prot4_ci_sF.

(* ------------------------------------------------------------------------------------------------ *)
(* The representation: the fields create_initiation touches, and the rest (frames).                  *)
(* Only this section depends on the exact conjuncts of init_rep / peer_rep / hs_rep / device_rep.    *)
(* ------------------------------------------------------------------------------------------------ *)

Section Rep.
Local Open Scope logic.
#[local] Existing Instance Noise.CS.

Definition prot4_ci_msg_frame (shm: share) (m: val) (M: init_msg) : mpred :=
  field_at shm t_init [StructField I._macs] (bytes (im_mac1 M), bytes (im_mac2 M)) m.

Definition prot4_ci_msg_fields (shm: share) (m: val) (M: init_msg) : mpred :=
  field_at shm t_init [StructField I._type; StructField I._header] (Vint (im_type M)) m *
  field_at shm t_init [StructField I._sender_index] (Vint (im_sender M)) m *
  field_at shm t_init [StructField I._unencrypted_ephemeral] (bytes (im_eph M)) m *
  field_at shm t_init [StructField I._encrypted_static] (bytes (im_encs M)) m *
  field_at shm t_init [StructField I._encrypted_timestamp] (bytes (im_enct M)) m.

Lemma prot4_ci_msg_eq: forall shm m M,
  data_at shm t_init (init_val M) m = prot4_ci_msg_fields shm m M * prot4_ci_msg_frame shm m M.
Proof.
intros. unfold prot4_ci_msg_fields, prot4_ci_msg_frame, init_val.
unfold_data_at (data_at _ _ _ m). unfold_field_at 1%nat. apply pred_ext; cancel.
Qed.

Lemma prot4_ci_msg_split: forall shm m M,
  init_rep shm m M |-- !! im_ok M && (prot4_ci_msg_fields shm m M * prot4_ci_msg_frame shm m M).
Proof.
intros. unfold init_rep. rewrite prot4_ci_msg_eq. entailer!.
Qed.

Lemma prot4_ci_msg_join: forall shm m M M',
  im_ok M' -> im_mac1 M' = im_mac1 M -> im_mac2 M' = im_mac2 M ->
  prot4_ci_msg_fields shm m M' * prot4_ci_msg_frame shm m M |-- init_rep shm m M'.
Proof.
intros shm m M M' Hok H1 H2. unfold init_rep. rewrite prot4_ci_msg_eq.
replace (prot4_ci_msg_frame shm m M) with (prot4_ci_msg_frame shm m M')
  by (unfold prot4_ci_msg_frame; rewrite H1, H2; reflexivity).
entailer!.
Qed.

(* the peer without the handshake fields create_initiation uses and without its device field *)
Definition prot4_ci_peer_frame (shp: share) (p: val) (P: peer) : mpred :=
  !! field_compatible t_peer [] p &&
  (field_at shp t_peer [StructField I._is_dead] (Val.of_bool (p_dead P)) p *
   kps_rep shp (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
   field_at shp t_peer [StructField I._last_sent_handshake] (Vlong (p_lsh P)) p *
   cookie_rep shp (cookie_addr p) (p_cookie P) *
   field_at shp t_peer [StructField I._refcount] (Vint (p_refs P)) p *
   field_at shp t_peer [StructField I._internal_id] (Vlong (p_id P)) p *
   field_at shp t_peer [StructField I._pubkey_next] (p_pknext P) p *
   field_at shp t_hs [StructField I._last_initiation_consumption] (Vlong (hs_lic (p_hs P))) (hs_addr p) *
   field_at shp t_hs [StructField I._remote_ephemeral] (bytes (hs_reph (p_hs P))) (hs_addr p) *
   field_at shp t_hs [StructField I._preshared_key] (bytes (hs_psk (p_hs P))) (hs_addr p) *
   field_at shp t_hs [StructField I._latest_timestamp] (bytes (hs_ts (p_hs P))) (hs_addr p) *
   field_at shp t_hs [StructField I._remote_index] (Vint (hs_rindex (p_hs P))) (hs_addr p) *
   (EX lk: val, field_at shp t_hs [StructField I._lock] lk (hs_addr p)) *
   (* the padding of the handshake and of the peer (prot_repr3's spacers) *)
   spacer shp 36 40 (hs_addr p) * spacer shp 300 304 (hs_addr p) * spacer shp 9 16 p * spacer shp 476 480 p).

Definition prot4_ci_hs_fields (shp: share) (p: val) (H: handshake) : mpred :=
  field_at shp t_hs [StructField I._state] (Vint (hs_state H)) (hs_addr p) *
  field_at shp t_hs [StructField I._static_identity] (hs_sid H) (hs_addr p) *
  field_at shp t_hs [StructField I._ephemeral_private] (bytes (hs_eph H)) (hs_addr p) *
  field_at shp t_hs [StructField I._remote_static] (bytes (hs_rstatic H)) (hs_addr p) *
  field_at shp t_hs [StructField I._precomputed_static_static] (bytes (hs_ss H)) (hs_addr p) *
  field_at shp t_hs [StructField I._hash] (bytes (hs_hash H)) (hs_addr p) *
  field_at shp t_hs [StructField I._chaining_key] (bytes (hs_ck H)) (hs_addr p).

Lemma prot4_ci_peer_split: forall shp p P,
  peer_rep shp p P |-- !! hs_ok (p_hs P) &&
    (prot4_ci_hs_fields shp p (p_hs P) * field_at shp t_peer [StructField I._device] (p_device P) p *
     prot4_ci_peer_frame shp p P).
Proof.
intros. unfold peer_rep, hs_rep, prot4_ci_hs_fields, prot4_ci_peer_frame. Intros lk.
Exists lk. entailer!.
Qed.

Lemma prot4_ci_peer_join: forall shp p P H',
  hs_ok H' -> hs_lic H' = hs_lic (p_hs P) -> hs_reph H' = hs_reph (p_hs P) ->
  hs_psk H' = hs_psk (p_hs P) -> hs_ts H' = hs_ts (p_hs P) -> hs_rindex H' = hs_rindex (p_hs P) ->
  prot4_ci_hs_fields shp p H' * field_at shp t_peer [StructField I._device] (p_device P) p *
  prot4_ci_peer_frame shp p P |-- peer_rep shp p (p_set_hs P H').
Proof.
intros shp p P H' Hok E1 E2 E3 E4 E5. unfold peer_rep, hs_rep, prot4_ci_hs_fields, prot4_ci_peer_frame.
destruct P; simpl in *. rewrite E1, E2, E3, E4, E5. Intros lk. Exists lk. entailer!.
Qed.

(* the device without has_identity, static_public and index_hashtable *)
Definition prot4_ci_dev_frame (shd: share) (wg: val) (D: device) : mpred :=
  !! (field_compatible t_dev [] wg /\ id_ok (d_id D)) &&
  (field_at shd t_dev [StructField I._dev] (d_dev D) wg *
   checker_rep shd (cc_addr wg) (d_cc D) *
   field_at shd t_dev [StructField I._peer_hashtable] (d_ptab D) wg *
   field_at shd t_sid [StructField I._static_private] (bytes (id_priv (d_id D))) (id_addr wg) *
   (EX lk: val, field_at shd t_sid [StructField I._lock] lk (id_addr wg)) *
   spacer shd 69 72 (id_addr wg)).

Definition prot4_ci_dev_fields (shd: share) (wg: val) (D: device) : mpred :=
  field_at shd t_sid [StructField I._has_identity] (Val.of_bool (id_has (d_id D))) (id_addr wg) *
  field_at shd t_sid [StructField I._static_public] (bytes (id_pub (d_id D))) (id_addr wg) *
  field_at shd t_dev [StructField I._index_hashtable] (d_itab D) wg.

Lemma prot4_ci_dev_split: forall shd wg D,
  device_rep shd wg D |-- !! id_ok (d_id D) && (prot4_ci_dev_fields shd wg D * prot4_ci_dev_frame shd wg D).
Proof.
intros. unfold device_rep, identity_rep, prot4_ci_dev_fields, prot4_ci_dev_frame. Intros lk.
unfold_data_at (data_at _ _ _ (id_addr wg)). Exists lk. entailer!.
Qed.

Lemma prot4_ci_dev_join: forall shd wg D,
  prot4_ci_dev_fields shd wg D * prot4_ci_dev_frame shd wg D |-- device_rep shd wg D.
Proof.
intros. unfold device_rep, identity_rep, prot4_ci_dev_fields, prot4_ci_dev_frame. Intros lk.
Exists lk. unfold_data_at (data_at _ _ _ (id_addr wg)). entailer!.
Qed.

End Rep.

(* ------------------------------------------------------------------------------------------------ *)
(* Lengths                                                                                          *)
(* ------------------------------------------------------------------------------------------------ *)

Lemma prot4_ci_Zlength_blake2s32: forall k m, Zlength (blake2s k 32 m) = 32.
Proof.
intros. unfold blake2s, b2s_digest_stream. cbv zeta. unfold b2s_out. rewrite Zlength_map. reflexivity.
Qed.

Lemma prot4_ci_Zlength_HASH: forall m, Zlength (HASH m) = 32.
Proof. intros. apply prot4_ci_Zlength_blake2s32. Qed.

Lemma prot4_ci_Zlength_hmac: forall k d, Zlength (hmac k d) = 32.
Proof. intros. unfold hmac. cbv zeta. apply prot4_ci_Zlength_HASH. Qed.

Lemma prot4_ci_Zlength_kdf1: forall c d, Zlength (kdf1 c d) = 32.
Proof. intros. unfold kdf1. exact (prot4_ci_Zlength_hmac _ _). Qed.

Lemma prot4_ci_Zlength_kdf2: forall c d, Zlength (kdf2 c d) = 32.
Proof. intros. unfold kdf2. exact (prot4_ci_Zlength_hmac _ _). Qed.

Lemma prot4_ci_Zlength_mix_hash: forall h d, Zlength (mix_hash h d) = 32.
Proof. intros. apply prot4_ci_Zlength_HASH. Qed.

Lemma prot4_ci_Zlength_init_ck: Zlength init_ck = 32.
Proof. apply prot4_ci_Zlength_HASH. Qed.

Lemma prot4_ci_Zlength_clamp: forall s, Zlength s = 32 -> Zlength (clamp s) = 32.
Proof. intros. unfold clamp. list_solve. Qed.

Lemma prot4_ci_Zlength_tai64n: forall a b, Zlength (tai64n a b) = 12.
Proof. intros. unfold tai64n, be64, be32. rewrite !Zlength_app, !Zlength_map. reflexivity. Qed.

(* ------------------------------------------------------------------------------------------------ *)
(* Chaining the stages                                                                              *)
(* ------------------------------------------------------------------------------------------------ *)

Lemma prot4_ci_seq2 {CS: compspecs} {Espec: OracleKind}: forall Delta P Q R s1 s2 rest,
  semax Delta P (Ssequence s1 s2) (overridePost Q R) -> semax Delta Q rest R ->
  semax Delta P (Ssequence s1 (Ssequence s2 rest)) R.
Proof.
intros. apply seq_assoc. eapply semax_seq; eassumption.
Qed.

Lemma prot4_ci_seq4 {CS: compspecs} {Espec: OracleKind}: forall Delta P Q R s1 s2 s3 s4 rest,
  semax Delta P (Ssequence s1 (Ssequence s2 (Ssequence s3 s4))) (overridePost Q R) -> semax Delta Q rest R ->
  semax Delta P (Ssequence s1 (Ssequence s2 (Ssequence s3 (Ssequence s4 rest)))) R.
Proof.
intros. apply seq_assoc. apply seq_assoc. apply seq_assoc. eapply semax_seq; [|eassumption].
apply (proj1 (seq_assoc _ _ _ _ _ _)) in H. apply (proj1 (seq_assoc _ _ _ _ _ _)) in H. exact H.
Qed.

Lemma prot4_ci_extract {CS: compspecs} {Espec: OracleKind}:
  forall Delta gv kc shm m shp p shd wg sid has pub tab sht rs ss kp tp FR
         Pf ret mt ms me mes met hst he hh hc kv tv S w T c R,
  (Pf -> semax Delta (ci_A gv kc shm m shp p shd wg sid has pub tab sht rs ss kp tp FR
                        True ret mt ms me mes met hst he hh hc kv tv S w T) c R) ->
  semax Delta (ci_A gv kc shm m shp p shd wg sid has pub tab sht rs ss kp tp FR
                 Pf ret mt ms me mes met hst he hh hc kv tv S w T) c R.
Proof.
intros. unfold ci_A in *. apply semax_extract_PROP. intros HP.
eapply semax_pre; [|apply H; exact HP].
apply andp_left2. unfold PROPx. simpl fold_right. apply andp_right; [apply prop_right; auto|].
apply andp_left2. apply derives_refl.
Qed.

(* ------------------------------------------------------------------------------------------------ *)
(* The exit of the loop                                                                             *)
(* ------------------------------------------------------------------------------------------------ *)

Section Main.
Local Open Scope logic.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.
Context (Hx: x25519_props x25519).
Context (Ha: aead_props aead_enc aead_dec).
#[local] Existing Instance Noise.CS.

Definition prot4_ci_FR (shm: share) (m: val) (M: init_msg) (shp: share) (p: val) (P: peer) (shd: share) (wg: val)
  (D: device) : mpred :=
  prot4_ci_msg_frame shm m M * prot4_ci_peer_frame shp p P * prot4_ci_dev_frame shd wg D.

(* the state after the loop (before memzero_explicit(key) and return ret) *)
Definition prot4_ci_Q (gv: globals) (kc: int64) (shm: share) (m: val) (M: init_msg) (shp: share) (p: val)
  (P: peer) (shd: share) (wg: val) (D: device) (sht: share) (T: tstate) (S: shim) (w: list int64) (kp tp: val)
  : environ -> mpred :=
  EX r: list byte, EX idx: int,
  PROP (Zlength r = 32;
        fst (fst (ci_res x25519 aead_enc D P M S r idx)) = true -> t_fresh T (hs_addr p) idx)
  LOCAL (temp I._ret (Val.of_bool (fst (fst (ci_res x25519 aead_enc D P M S r idx))));
         lvar I._key (tarray tuchar 32) kp; lvar I._timestamp (tarray tuchar 12) tp; gvars gv)
  SEP (data_at_ Tsh (tarray tuchar 32) kp; data_at_ Tsh (tarray tuchar 12) tp;
       init_rep shm m (snd (fst (ci_res x25519 aead_enc D P M S r idx)));
       peer_rep shp p (p_set_hs P (snd (ci_res x25519 aead_enc D P M S r idx)));
       device_rep shd wg D;
       itable sht (d_itab D)
         (if fst (fst (ci_res x25519 aead_enc D P M S r idx)) then t_insert T (hs_addr p) idx else T);
       shim_state4 gv (if id_has (d_id D)
                      then (if fst (fst (ci_res x25519 aead_enc D P M S r idx))
                            then shim_u32 (shim_draw S r) idx else shim_draw S r)
                      else S) w;
       noise_globals gv kc; wg_consts gv).

(* every exit: the state ci_A whose fields are those of the model's result (b, Mk, Hk) *)
Lemma prot4_ci_exit:
  forall gv kc shm m M shp p P shd wg D sht T S w kp tp
         Pf ret mt ms me mes met hst he hh hc kv tv S' T' r idx b Mk Hk,
  p_device P = wg -> hs_sid (p_hs P) = id_addr wg ->
  ci_res x25519 aead_enc D P M S r idx = (b, Mk, Hk) ->
  Zlength r = 32 -> (Pf -> b = true -> t_fresh T (hs_addr p) idx) ->
  T' = (if b then t_insert T (hs_addr p) idx else T) ->
  S' = (if id_has (d_id D) then (if b then shim_u32 (shim_draw S r) idx else shim_draw S r) else S) ->
  im_ok Mk -> im_mac1 Mk = im_mac1 M -> im_mac2 Mk = im_mac2 M ->
  hs_ok Hk -> hs_lic Hk = hs_lic (p_hs P) -> hs_reph Hk = hs_reph (p_hs P) ->
  hs_psk Hk = hs_psk (p_hs P) -> hs_ts Hk = hs_ts (p_hs P) -> hs_rindex Hk = hs_rindex (p_hs P) ->
  hs_sid Hk = hs_sid (p_hs P) -> hs_rstatic Hk = hs_rstatic (p_hs P) -> hs_ss Hk = hs_ss (p_hs P) ->
  ret = Val.of_bool b -> mt = Vint (im_type Mk) -> ms = Vint (im_sender Mk) -> me = bytes (im_eph Mk) ->
  mes = bytes (im_encs Mk) -> met = bytes (im_enct Mk) -> hst = Vint (hs_state Hk) ->
  he = bytes (hs_eph Hk) -> hh = bytes (hs_hash Hk) -> hc = bytes (hs_ck Hk) ->
  ci_A gv kc shm m shp p shd wg (id_addr wg) (id_has (d_id D)) (id_pub (d_id D)) (d_itab D) sht
    (hs_rstatic (p_hs P)) (hs_ss (p_hs P)) kp tp (prot4_ci_FR shm m M shp p P shd wg D)
    Pf ret mt ms me mes met hst he hh hc kv tv S' w T'
  |-- prot4_ci_Q gv kc shm m M shp p P shd wg D sht T S w kp tp.
Proof.
intros until Hk.
intros Hdev Hsid Hres Hr Hfr HT HS Hok Hm1 Hm2 Hhok E1 E2 E3 E4 E5 E6 E7 E8
       Eret Emt Ems Eme Emes Emet Ehst Ehe Ehh Ehc.
subst. unfold prot4_ci_Q, ci_A, prot4_ci_FR. Exists r idx. rewrite Hres. cbn [fst snd].
pose proof (prot4_ci_msg_join shm m M Mk Hok Hm1 Hm2) as JM. unfold prot4_ci_msg_fields in JM.
pose proof (prot4_ci_peer_join shp p P Hk Hhok E1 E2 E3 E4 E5) as JP. unfold prot4_ci_hs_fields in JP.
rewrite E6, Hsid, E7, E8 in JP.
pose proof (prot4_ci_dev_join shd (p_device P) D) as JD. unfold prot4_ci_dev_fields in JD.
go_lowerx. match goal with HPf: Pf |- _ => specialize (Hfr HPf) end. entailer!.
sep_apply JM. sep_apply JP. sep_apply JD. unfold data_at_. cancel.
Qed.

(* the model's result at each exit of the loop *)
Section Model.
Variables (D: device) (P: peer) (M: init_msg) (S: shim) (r: list byte) (idx: int).
Let ID := d_id D.
Let H := p_hs P.
Let e := clamp r.
Let E := x25519 e basepoint9.
Let h0 := mix_hash init_hash (hs_rstatic H).
Let ck1 := kdf1 init_ck E.
Let h1 := mix_hash h0 E.
Let ck2 := kdf1 ck1 (x25519 e (hs_rstatic H)).
Let k2 := kdf2 ck1 (x25519 e (hs_rstatic H)).
Let c := aead_enc k2 0 h1 (id_pub ID).
Let h2 := mix_hash h1 c.
Let ck3 := kdf1 ck2 (hs_ss H).
Let k3 := kdf2 ck2 (hs_ss H).
Let ts := tai64n (s_rsec S) (s_rnsec S).
Let ct := aead_enc k3 0 h2 ts.
Let h3 := mix_hash h2 ct.

Lemma prot4_ci_res0: id_has ID = false -> ci_res x25519 aead_enc D P M S r idx = (false, M, H).
Proof. intros Hh. unfold ci_res, create_initiation_model. fold ID. rewrite Hh. reflexivity. Qed.

Lemma prot4_ci_res1: id_has ID = true ->
  (memneq_bool e zeros32 && memneq_bool E zeros32)%bool = false ->
  ci_res x25519 aead_enc D P M S r idx =
  (false, mkIM (Int.repr 1) (im_sender M) (if memneq_bool e zeros32 then E else im_eph M) (im_encs M)
            (im_enct M) (im_mac1 M) (im_mac2 M),
   hs_set_eph (hs_set_ckh H init_ck h0) e).
Proof.
intros Hh Hb. unfold ci_res, create_initiation_model. fold ID H. rewrite Hh.
cbv zeta. fold e. fold E. fold h0.
destruct (memneq_bool e zeros32); [|reflexivity].
simpl in Hb. rewrite Hb. reflexivity.
Qed.

Lemma prot4_ci_res2: id_has ID = true -> memneq_bool e zeros32 = true -> memneq_bool E zeros32 = true ->
  dh_ok x25519 e (hs_rstatic H) = false ->
  ci_res x25519 aead_enc D P M S r idx =
  (false, mkIM (Int.repr 1) (im_sender M) E (im_encs M) (im_enct M) (im_mac1 M) (im_mac2 M),
   hs_set_ckh (hs_set_eph (hs_set_ckh H init_ck h0) e) ck1 h1).
Proof.
intros Hh He HE Hd. unfold ci_res, create_initiation_model. fold ID H. rewrite Hh.
cbv zeta. fold e. fold E. fold h0. rewrite He, HE. fold ck1 h1. rewrite Hd. reflexivity.
Qed.

Lemma prot4_ci_res3: id_has ID = true -> memneq_bool e zeros32 = true -> memneq_bool E zeros32 = true ->
  dh_ok x25519 e (hs_rstatic H) = true -> memneq_bool (hs_ss H) zeros32 = false ->
  ci_res x25519 aead_enc D P M S r idx =
  (false, mkIM (Int.repr 1) (im_sender M) E c (im_enct M) (im_mac1 M) (im_mac2 M),
   hs_set_ckh (hs_set_ckh (hs_set_eph (hs_set_ckh H init_ck h0) e) ck1 h1) ck2 h2).
Proof.
intros Hh He HE Hd Hs. unfold ci_res, create_initiation_model. fold ID H. rewrite Hh.
cbv zeta. fold e. fold E. fold h0. rewrite He, HE. fold ck1 h1. rewrite Hd. fold ck2 k2 c h2.
rewrite Hs. reflexivity.
Qed.

Lemma prot4_ci_res4: id_has ID = true -> memneq_bool e zeros32 = true -> memneq_bool E zeros32 = true ->
  dh_ok x25519 e (hs_rstatic H) = true -> memneq_bool (hs_ss H) zeros32 = true ->
  ci_res x25519 aead_enc D P M S r idx =
  (true, mkIM (Int.repr 1) idx E c ct (im_mac1 M) (im_mac2 M),
   hs_set_state (hs_set_ckh (hs_set_ckh (hs_set_ckh (hs_set_eph (hs_set_ckh H init_ck h0) e) ck1 h1) ck2 h2)
                   ck3 h3) HS_CREATED_INITIATION).
Proof.
intros Hh He HE Hd Hs. unfold ci_res, create_initiation_model. fold ID H. rewrite Hh.
cbv zeta. fold e. fold E. fold h0. rewrite He, HE. fold ck1 h1. rewrite Hd. fold ck2 k2 c h2.
rewrite Hs. fold ck3 k3. fold ts. fold ct h3. reflexivity.
Qed.
End Model.

Ltac prot4_ci_len Hx Ha :=
  repeat first [ rewrite prot4_ci_Zlength_kdf1 | rewrite prot4_ci_Zlength_kdf2
               | rewrite prot4_ci_Zlength_mix_hash | rewrite prot4_ci_Zlength_init_ck
               | rewrite (Hx _ _) | rewrite (aead_enc_length _ _ Ha) | rewrite prot4_ci_Zlength_tai64n
               | rewrite prot4_ci_Zlength_clamp by assumption ];
  try assumption; try lia; try (unfold id_ok in *; lia).

Ltac prot4_ci_side Hx Ha :=
  first [ reflexivity
        | intros _ X; discriminate X
        | intros X _; exact X
        | match goal with H: id_has _ = true |- _ => rewrite H; reflexivity end
        | match goal with |- im_ok _ => idtac end;
          unfold im_ok; cbn [im_eph im_encs im_enct im_mac1 im_mac2];
          try (destruct (memneq_bool _ _)); repeat split; prot4_ci_len Hx Ha
        | match goal with |- hs_ok _ => idtac end;
          unfold hs_ok; cbn [hs_eph hs_rstatic hs_reph hs_ss hs_psk hs_hash hs_ck hs_ts
                             hs_set_eph hs_set_ckh hs_set_state];
          repeat split; prot4_ci_len Hx Ha
        | destruct (memneq_bool _ _); reflexivity ].

Lemma prot4_ci_loop {Espec: OracleKind}:
  forall gv kc shm m M shp p P shd wg D sht T S w kp tp kv tv,
  writable_share shm -> writable_share shp -> readable_share shd -> writable_share sht ->
  p_device P = wg -> hs_sid (p_hs P) = id_addr wg -> hs_in_pool T p ->
  im_ok M -> hs_ok (p_hs P) -> id_ok (d_id D) -> Zlength kv = 32 -> Zlength tv = 12 ->
  semax (ci_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec CSw)
    (ci_A gv kc shm m shp p shd wg (id_addr wg) (id_has (d_id D)) (id_pub (d_id D)) (d_itab D) sht
       (hs_rstatic (p_hs P)) (hs_ss (p_hs P)) kp tp (prot4_ci_FR shm m M shp p P shd wg D)
       True (Vint Int.zero) (Vint (im_type M)) (Vint (im_sender M)) (bytes (im_eph M)) (bytes (im_encs M))
       (bytes (im_enct M)) (Vint (hs_state (p_hs P))) (bytes (hs_eph (p_hs P))) (bytes (hs_hash (p_hs P)))
       (bytes (hs_ck (p_hs P))) kv tv S w T)
    (Sloop ci_LB Sbreak)
    (normal_ret_assert (prot4_ci_Q gv kc shm m M shp p P shd wg D sht T S w kp tp)).
Proof.
intros until tv. intros SHm SHp SHd SHt Hdev Hsid Hpool HMok HHok HIok Hkv Htv.
unfold x25519_props in Hx.
remember (prot4_ci_Q gv kc shm m M shp p P shd wg D sht T S w kp tp) as Q eqn:EQ.
apply semax_loop with (Q' := Q).
2: { eapply semax_pre; [|apply semax_break]. simpl RA_break. apply andp_left2, derives_refl. }
rewrite ci_LB_eq.
(* A: has_identity *)
eapply semax_seq.
{ apply prot4_ci_sA; auto. intros Hhas. simpl RA_normal. subst Q.
  eapply prot4_ci_exit with (r := zeros32) (idx := Int.zero) (b := false) (Mk := M) (Hk := p_hs P);
    auto; try reflexivity.
  all: first [ apply prot4_ci_res0; auto | intros _ X; discriminate X | rewrite Hhas; reflexivity ]. }
apply prot4_ci_extract; intros Hhas.
destruct HMok as (HMe & HMs & HMt & HM1 & HM2).
destruct HHok as (HHe & HHrs & HHre & HHss & HHpsk & HHh & HHck & HHts).
(* B: type, handshake_init, generate_secret, generate_public *)
eapply prot4_ci_seq4.
{ eapply prot4_ci_sB; auto; try reflexivity.
  { unfold bytes; rewrite Zlength_map; auto. }
  intros r Hr Hb. simpl RA_normal. subst Q.
  eapply prot4_ci_exit with (r := r) (idx := Int.zero) (b := false)
    (Mk := mkIM (Int.repr 1) (im_sender M)
             (if memneq_bool (clamp r) zeros32 then x25519 (clamp r) basepoint9 else im_eph M)
             (im_encs M) (im_enct M) (im_mac1 M) (im_mac2 M))
    (Hk := hs_set_eph (hs_set_ckh (p_hs P) init_ck (mix_hash init_hash (hs_rstatic (p_hs P)))) (clamp r));
    auto; try reflexivity.
  2-6: prot4_ci_side Hx Ha.
  apply prot4_ci_res1; auto. }
apply extract_exists_pre; intros r. apply prot4_ci_extract; intros (Hr & He & HE).
(* C: message_ephemeral, mix_dh *)
eapply prot4_ci_seq2.
{ eapply prot4_ci_sC; auto; try reflexivity; try (prot4_ci_len Hx Ha).
  intros kv' Hd. simpl RA_normal. subst Q.
  eapply prot4_ci_exit with (r := r) (idx := Int.zero).
  3: apply prot4_ci_res2; auto.
  all: auto; try reflexivity; prot4_ci_side Hx Ha. }
apply prot4_ci_extract; intros Hd.
(* D: encrypted static, mix_precomputed_dh *)
eapply prot4_ci_seq2.
{ eapply prot4_ci_sD; auto; try reflexivity; try (prot4_ci_len Hx Ha).
  intros kv' Hs. simpl RA_normal. subst Q.
  eapply prot4_ci_exit with (r := r) (idx := Int.zero).
  3: apply prot4_ci_res3; auto.
  all: auto; try reflexivity; prot4_ci_side Hx Ha. }
apply prot4_ci_extract; intros Hs.
(* E: timestamp *)
eapply prot4_ci_seq2.
{ eapply prot4_ci_sE with (ts := tai64n (s_rsec S) (s_rnsec S)); auto; try reflexivity;
    try (prot4_ci_len Hx Ha). }
apply prot4_ci_extract; intros _.
(* F: index, state, ret; then the success exit *)
eapply semax_post.
5: eapply prot4_ci_sF with (Qc := Q) (R := normal_ret_assert Q); auto.
- cbv beta iota delta [RA_normal RA_break RA_continue RA_return overridePost loop1_ret_assert normal_ret_assert]. apply andp_left2. Intros idx. subst Q.
  eapply prot4_ci_exit with (r := r) (idx := idx).
  3: apply prot4_ci_res4; auto.
  all: auto; try reflexivity; prot4_ci_side Hx Ha.
- cbv beta iota delta [RA_normal RA_break RA_continue RA_return overridePost loop1_ret_assert normal_ret_assert]. apply andp_left2, derives_refl.
- cbv beta iota delta [RA_normal RA_break RA_continue RA_return overridePost loop1_ret_assert normal_ret_assert]. apply andp_left2, derives_refl.
- intros vl. cbv beta iota delta [RA_normal RA_break RA_continue RA_return overridePost loop1_ret_assert normal_ret_assert]. apply andp_left2, derives_refl.
Qed.

End Main.

#[local] Existing Instance Noise.CS.
Local Open Scope logic.

Theorem prot4_ci_bodies :
  forall x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs),
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  (@semax_body (QPvarspecs Noise.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
      WgNoise.noise.code.f_wg_noise_handshake_create_initiation (wg_noise_handshake_create_initiation_spec x25519 aead_enc)).
Proof.
intros x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Hx Ha Hxa.
start_function.
unfold MORE_COMMANDS, abbreviate.
match goal with |- semax _ _ ?c _ =>
  change c with (Ssequence ci_B0 (Ssequence (Sloop ci_LB Sbreak) ci_END)) end.
eapply semax_pre with (P' :=
  PROP (im_ok M; hs_ok (p_hs P); id_ok (d_id D))
  LOCAL (lvar I._key (tarray tuchar 32) v_key; lvar I._timestamp (tarray tuchar 12) v_timestamp;
         gvars gv; temp I._dst m; temp I._handshake (hs_addr p))
  SEP (@data_at_ Noise.CS Tsh (tarray tuchar 32) v_key; @data_at_ Noise.CS Tsh (tarray tuchar 12) v_timestamp;
       prot4_ci_msg_fields shm m M; prot4_ci_msg_frame shm m M;
       prot4_ci_hs_fields shp p (p_hs P); @field_at Noise.CS shp t_peer [StructField I._device] (p_device P) p;
       prot4_ci_peer_frame shp p P;
       prot4_ci_dev_fields shd wg D; prot4_ci_dev_frame shd wg D;
       itable sht (d_itab D) T; shim_state4 gv S w; noise_globals gv kc; wg_consts gv)).
{ sep_apply prot4_ci_msg_split. Intros. sep_apply prot4_ci_peer_split. Intros.
  sep_apply prot4_ci_dev_split. Intros. entailer!. }
apply semax_extract_PROP; intro HMok. apply semax_extract_PROP; intro HHok. apply semax_extract_PROP; intro HIok.
change Delta with (ci_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec CSw).
eapply semax_seq' with (P' :=
  ci_A gv kc shm m shp p shd wg (id_addr wg) (id_has (d_id D)) (id_pub (d_id D)) (d_itab D) sht
    (hs_rstatic (p_hs P)) (hs_ss (p_hs P)) v_key v_timestamp (prot4_ci_FR shm m M shp p P shd wg D)
    True (Vint Int.zero) (Vint (im_type M)) (Vint (im_sender M)) (bytes (im_eph M)) (bytes (im_encs M))
    (bytes (im_enct M)) (Vint (hs_state (p_hs P))) (bytes (hs_eph (p_hs P))) (bytes (hs_hash (p_hs P)))
    (bytes (hs_ck (p_hs P))) (Zrepeat Vundef 32) (Zrepeat Vundef 12) S w T).
{ unfold ci_Delta. simplify_func_tycontext. unfold ci_B0. abbreviate_semax.
  forward. unfold ci_A, prot4_ci_FR, prot4_ci_msg_fields, prot4_ci_hs_fields, prot4_ci_dev_fields.
  rewrite H, H0. entailer!. }
eapply semax_seq'.
{ apply prot4_ci_loop; auto. }
unfold prot4_ci_Q. Intros r idx.
change (ci_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec CSw) with Delta. unfold ci_END. abbreviate_semax.
remember (ci_res x25519 aead_enc D P M S r idx) as res eqn:Eres.
forward_call (Tsh, v_key, 32).
forward.
Exists r idx. remember (ci_res x25519 aead_enc D P M S r idx) as res eqn:Eres. clear Eres.
entailer!. destruct (fst (fst res)); reflexivity.
Qed.
