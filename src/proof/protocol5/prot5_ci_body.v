(* wg_noise_handshake_create_initiation against its v5 specification (prot_specs5.v, context Gprot5): the
   proof of prot4_ci_body.v over the v5 representation.  The message buffer is a message (Mo = Some M) or
   uninitialised memory (Mo = None); the model runs on init_of Mo.  The stage lemmas (prot5_ci_s<X>.v) do not
   depend on the message fields' values; what changes is the exit: when the function fails on an
   uninitialised buffer, the fields it has written and those still undefined together are only data_at_. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol5.prot_prog5.
Require WgNoise.noise.code WgNoise.shim.code.
Require Import WgNoise.proof.blake2s.model.
Require Import WgNoise.proof.protocol5.prot5_ci_defs.
Require Import WgNoise.proof.protocol5.prot5_ci_sA.
Require Import WgNoise.proof.protocol5.prot5_ci_sB.
Require Import WgNoise.proof.protocol5.prot5_ci_sC.
Require Import WgNoise.proof.protocol5.prot5_ci_sD.
Require Import WgNoise.proof.protocol5.prot5_ci_sE.
Require Import WgNoise.proof.protocol5.prot5_ci_sF.
Require Import WgNoise.proof.protocol4.prot4_ci_body.

(* ------------------------------------------------------------------------------------------------ *)
(* The representation: the fields create_initiation touches, and the rest (frames).                  *)
(* ------------------------------------------------------------------------------------------------ *)

Section Rep.
Local Open Scope logic.
#[local] Existing Instance Noise.CS.

(* the five message fields create_initiation writes, with arbitrary values *)
Definition ci5_msg_fields (shm: share) (m: val) (mt ms: val) (me mes met: list val) : mpred :=
  field_at shm t_init [StructField I._type; StructField I._header] mt m *
  field_at shm t_init [StructField I._sender_index] ms m *
  field_at shm t_init [StructField I._unencrypted_ephemeral] me m *
  field_at shm t_init [StructField I._encrypted_static] mes m *
  field_at shm t_init [StructField I._encrypted_timestamp] met m.

(* the macs: never written by the function *)
Definition ci5_msg_frame (shm: share) (m: val) : mpred := field_at_ shm t_init [StructField I._macs] m.

(* the fields' values before the call: those of the message, or undefined *)
Definition ci5_mt0 (Mo: option init_msg) : val := match Mo with Some M => Vint (im_type M) | None => Vundef end.
Definition ci5_ms0 (Mo: option init_msg) : val := match Mo with Some M => Vint (im_sender M) | None => Vundef end.
Definition ci5_me0 (Mo: option init_msg) : list val :=
  match Mo with Some M => bytes (im_eph M) | None => Zrepeat Vundef 32 end.
Definition ci5_mes0 (Mo: option init_msg) : list val :=
  match Mo with Some M => bytes (im_encs M) | None => Zrepeat Vundef 48 end.
Definition ci5_met0 (Mo: option init_msg) : list val :=
  match Mo with Some M => bytes (im_enct M) | None => Zrepeat Vundef 28 end.

Lemma ci5_header_eq: forall sh m v,
  field_at sh t_init [StructField I._header] v m = field_at sh t_init [StructField I._type; StructField I._header] v m.
Proof. intros. unfold_field_at 1%nat. reflexivity. Qed.

Lemma ci5_msg_data_at_: forall sh m,
  data_at_ sh t_init m =
  field_at_ sh t_init [StructField I._type; StructField I._header] m *
  field_at_ sh t_init [StructField I._sender_index] m *
  field_at_ sh t_init [StructField I._unencrypted_ephemeral] m *
  field_at_ sh t_init [StructField I._encrypted_static] m *
  field_at_ sh t_init [StructField I._encrypted_timestamp] m *
  field_at_ sh t_init [StructField I._macs] m.
Proof.
intros. unfold data_at_, field_at_.
change (field_at sh t_init [] (default_val (nested_field_type t_init [])) m) with (data_at sh t_init (default_val t_init) m).
unfold_data_at (data_at sh t_init (default_val t_init) m). unfold_field_at 1%nat.
apply pred_ext; cancel.
Qed.

Lemma ci5_msg_split: forall shm m Mo,
  init_opt_rep shm m Mo |-- !! im_ok5 (init_of Mo) &&
    (ci5_msg_fields shm m (ci5_mt0 Mo) (ci5_ms0 Mo) (ci5_me0 Mo) (ci5_mes0 Mo) (ci5_met0 Mo) * ci5_msg_frame shm m).
Proof.
intros. destruct Mo as [M|]; simpl.
- unfold init_rep5, ci5_msg_fields, ci5_msg_frame. rewrite ci5_header_eq. entailer!.
- rewrite ci5_msg_data_at_. unfold ci5_msg_fields, ci5_msg_frame. unfold field_at_ at 1 2 3 4 5.
  rewrite prop_true_andp by (unfold im_ok5, init_msg0; simpl; repeat split; reflexivity).
  apply derives_refl.
Qed.

(* every field state is a buffer; the model's message M' when the fields are its *)
Lemma ci5_msg_join: forall shm m Mo b M' mt ms me mes met,
  ((b = true \/ Mo <> None) ->
   im_ok5 M' /\ mt = Vint (im_type M') /\ ms = Vint (im_sender M') /\ me = bytes (im_eph M') /\
   mes = bytes (im_encs M') /\ met = bytes (im_enct M')) ->
  ci5_msg_fields shm m mt ms me mes met * ci5_msg_frame shm m |-- init_opt_rep shm m (opt_after b Mo M').
Proof.
intros shm m Mo b M' mt ms me mes met HM. unfold ci5_msg_fields, ci5_msg_frame.
destruct b.
- destruct HM as (Hok & -> & -> & -> & -> & ->); auto. simpl. unfold init_rep5. rewrite ci5_header_eq. entailer!.
- destruct Mo as [M|]; simpl.
  + destruct HM as (Hok & -> & -> & -> & -> & ->); [right; discriminate|]. unfold init_rep5.
    rewrite ci5_header_eq. entailer!.
  + rewrite ci5_msg_data_at_. repeat (apply sepcon_derives; [|apply derives_refl]).
    repeat (apply sepcon_derives; [|apply field_at_field_at_]). apply field_at_field_at_.
Qed.

(* the peer without the handshake fields create_initiation uses and without its device field *)
Definition ci5_peer_frame (shp: share) (p: val) (P: peer) : mpred :=
  !! field_compatible t_peer [] p &&
  (field_at shp t_peer [StructField I._is_dead] (Val.of_bool (p_dead P)) p *
   kps_rep shp (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
   field_at_ shp t_peer [StructField I._last_sent_handshake] p *
   field_at_ shp t_peer [StructField I._latest_cookie] p *
   field_at shp t_peer [StructField I._refcount] (Vint (p_refs P)) p *
   field_at_ shp t_peer [StructField I._internal_id] p *
   field_at shp t_peer [StructField I._pubkey_next] (p_pknext P) p *
   field_at shp t_hs [StructField I._last_initiation_consumption] (Vlong (hs_lic (p_hs P))) (hs_addr p) *
   field_at shp t_hs [StructField I._remote_ephemeral] (bytes (hs_reph (p_hs P))) (hs_addr p) *
   field_at shp t_hs [StructField I._preshared_key] (bytes (hs_psk (p_hs P))) (hs_addr p) *
   field_at shp t_hs [StructField I._latest_timestamp] (bytes (hs_ts (p_hs P))) (hs_addr p) *
   field_at shp t_hs [StructField I._remote_index] (Vint (hs_rindex (p_hs P))) (hs_addr p) *
   (EX lk: val, field_at shp t_hs [StructField I._lock] lk (hs_addr p)) *
   (* the padding of the handshake and of the peer (prot_repr3's spacers) *)
   spacer shp 36 40 (hs_addr p) * spacer shp 300 304 (hs_addr p) * spacer shp 9 16 p * spacer shp 476 480 p).

Lemma ci5_peer_split: forall shp p P,
  peer_rep5 shp p P |-- !! hs_ok (p_hs P) &&
    (prot4_ci_hs_fields shp p (p_hs P) *
     field_at shp t_peer [StructField I._device] (p_device P) p * ci5_peer_frame shp p P).
Proof.
intros. unfold peer_rep5, hs_rep, prot4_ci_hs_fields, ci5_peer_frame.
Intros lk. Exists lk. entailer!.
Qed.

Lemma ci5_peer_join: forall shp p P H',
  hs_ok H' -> hs_lic H' = hs_lic (p_hs P) -> hs_reph H' = hs_reph (p_hs P) ->
  hs_psk H' = hs_psk (p_hs P) -> hs_ts H' = hs_ts (p_hs P) -> hs_rindex H' = hs_rindex (p_hs P) ->
  prot4_ci_hs_fields shp p H' *
  field_at shp t_peer [StructField I._device] (p_device P) p *
  ci5_peer_frame shp p P |-- peer_rep5 shp p (p_set_hs P H').
Proof.
intros shp p P H' Hok E1 E2 E3 E4 E5.
unfold peer_rep5, hs_rep, prot4_ci_hs_fields, ci5_peer_frame.
destruct P; simpl in *. rewrite E1, E2, E3, E4, E5. Intros lk. Exists lk. entailer!.
Qed.

(* the device without has_identity, static_public and index_hashtable *)
Definition ci5_dev_frame (shd: share) (wg: val) (D: device) : mpred :=
  !! (field_compatible t_dev [] wg /\ id_ok (d_id D)) &&
  (field_at_ shd t_dev [StructField I._dev] wg *
   field_at_ shd t_dev [StructField I._cookie_checker] wg *
   field_at shd t_dev [StructField I._peer_hashtable] (d_ptab D) wg *
   field_at shd t_sid [StructField I._static_private] (bytes (id_priv (d_id D))) (id_addr wg) *
   (EX lk: val, field_at shd t_sid [StructField I._lock] lk (id_addr wg)) *
   spacer shd 69 72 (id_addr wg)).

Lemma ci5_dev_split: forall shd wg D,
  device_rep5 shd wg D |-- !! id_ok (d_id D) &&
    (prot4_ci_dev_fields shd wg D * ci5_dev_frame shd wg D).
Proof.
intros. unfold device_rep5, identity_rep, prot4_ci_dev_fields, ci5_dev_frame.
Intros lk. unfold_data_at (data_at _ _ _ (id_addr wg)). Exists lk. entailer!.
Qed.

Lemma ci5_dev_join: forall shd wg D,
  prot4_ci_dev_fields shd wg D * ci5_dev_frame shd wg D |-- device_rep5 shd wg D.
Proof.
intros. unfold device_rep5, identity_rep, prot4_ci_dev_fields, ci5_dev_frame.
Intros lk. Exists lk. unfold_data_at (data_at _ _ _ (id_addr wg)). entailer!.
Qed.

End Rep.

Lemma ci5_m0_eq: forall Mo, Mo <> None ->
  ci5_mt0 Mo = Vint (im_type (init_of Mo)) /\ ci5_ms0 Mo = Vint (im_sender (init_of Mo)) /\
  ci5_me0 Mo = bytes (im_eph (init_of Mo)) /\ ci5_mes0 Mo = bytes (im_encs (init_of Mo)) /\
  ci5_met0 Mo = bytes (im_enct (init_of Mo)).
Proof. intros [M|] HM; [repeat split | contradiction HM; reflexivity]. Qed.

Lemma ci5_extract {CS: compspecs} {Espec: OracleKind}:
  forall Delta gv kc shm m shp p shd wg sid has pub tab sht rs ss kp tp FR
         Pf ret mt ms me mes met hst he hh hc kv tv S w T c R,
  (Pf -> semax Delta (ci5_A gv kc shm m shp p shd wg sid has pub tab sht rs ss kp tp FR
                        True ret mt ms me mes met hst he hh hc kv tv S w T) c R) ->
  semax Delta (ci5_A gv kc shm m shp p shd wg sid has pub tab sht rs ss kp tp FR
                 Pf ret mt ms me mes met hst he hh hc kv tv S w T) c R.
Proof.
intros. unfold ci5_A in *. apply semax_extract_PROP. intros HP.
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
Variable CSw: compspecs.
Context (Hx: x25519_props x25519).
Context (Ha: aead_props aead_enc aead_dec).
#[local] Existing Instance Noise.CS.

Definition ci5_FR (shm: share) (m: val) (shp: share) (p: val) (P: peer) (shd: share) (wg: val) (D: device) : mpred :=
  ci5_msg_frame shm m * ci5_peer_frame shp p P * ci5_dev_frame shd wg D.

(* the state after the loop (before memzero_explicit(key) and return ret) *)
Definition ci5_Q (gv: globals) (kc: int64) (shm: share) (m: val) (Mo: option init_msg) (shp: share) (p: val)
  (P: peer) (shd: share) (wg: val) (D: device) (sht: share) (T: tstate) (S: shim) (w: list int64) (kp tp: val)
  : environ -> mpred :=
  EX r: list byte, EX idx: int,
  PROP (Zlength r = 32;
        fst (fst (ci_res x25519 aead_enc D P (init_of Mo) S r idx)) = true -> t_fresh T (hs_addr p) idx)
  LOCAL (temp I._ret (Val.of_bool (fst (fst (ci_res x25519 aead_enc D P (init_of Mo) S r idx))));
         lvar I._key (tarray tuchar 32) kp; lvar I._timestamp (tarray tuchar 12) tp; gvars gv)
  SEP (data_at_ Tsh (tarray tuchar 32) kp; data_at_ Tsh (tarray tuchar 12) tp;
       init_opt_rep shm m (opt_after (fst (fst (ci_res x25519 aead_enc D P (init_of Mo) S r idx))) Mo
                                     (snd (fst (ci_res x25519 aead_enc D P (init_of Mo) S r idx))));
       peer_rep5 shp p (p_set_hs P (snd (ci_res x25519 aead_enc D P (init_of Mo) S r idx)));
       device_rep5 shd wg D;
       itable sht (d_itab D)
         (if fst (fst (ci_res x25519 aead_enc D P (init_of Mo) S r idx)) then t_insert T (hs_addr p) idx else T);
       shim_state4 gv (if id_has (d_id D)
                      then (if fst (fst (ci_res x25519 aead_enc D P (init_of Mo) S r idx))
                            then shim_u32 (shim_draw S r) idx else shim_draw S r)
                      else S) w;
       noise_globals gv kc; wg_consts5 gv).

(* every exit: the state ci5_A whose handshake fields are those of the model's result (b, Mk, Hk), and whose
   message fields are Mk's if the function succeeded or the buffer held a message *)
Lemma ci5_exit:
  forall gv kc shm m Mo shp p P shd wg D sht T S w kp tp
         Pf ret mt ms me mes met hst he hh hc kv tv S' T' r idx b Mk Hk,
  p_device P = wg -> hs_sid (p_hs P) = id_addr wg ->
  ci_res x25519 aead_enc D P (init_of Mo) S r idx = (b, Mk, Hk) ->
  Zlength r = 32 -> (Pf -> b = true -> t_fresh T (hs_addr p) idx) ->
  T' = (if b then t_insert T (hs_addr p) idx else T) ->
  S' = (if id_has (d_id D) then (if b then shim_u32 (shim_draw S r) idx else shim_draw S r) else S) ->
  ((b = true \/ Mo <> None) ->
   im_ok5 Mk /\ mt = Vint (im_type Mk) /\ ms = Vint (im_sender Mk) /\ me = bytes (im_eph Mk) /\
   mes = bytes (im_encs Mk) /\ met = bytes (im_enct Mk)) ->
  hs_ok Hk -> hs_lic Hk = hs_lic (p_hs P) -> hs_reph Hk = hs_reph (p_hs P) ->
  hs_psk Hk = hs_psk (p_hs P) -> hs_ts Hk = hs_ts (p_hs P) -> hs_rindex Hk = hs_rindex (p_hs P) ->
  hs_sid Hk = hs_sid (p_hs P) -> hs_rstatic Hk = hs_rstatic (p_hs P) -> hs_ss Hk = hs_ss (p_hs P) ->
  ret = Val.of_bool b -> hst = Vint (hs_state Hk) ->
  he = bytes (hs_eph Hk) -> hh = bytes (hs_hash Hk) -> hc = bytes (hs_ck Hk) ->
  ci5_A gv kc shm m shp p shd wg (id_addr wg) (id_has (d_id D)) (id_pub (d_id D)) (d_itab D) sht
    (hs_rstatic (p_hs P)) (hs_ss (p_hs P)) kp tp (ci5_FR shm m shp p P shd wg D)
    Pf ret mt ms me mes met hst he hh hc kv tv S' w T'
  |-- ci5_Q gv kc shm m Mo shp p P shd wg D sht T S w kp tp.
Proof.
intros until Hk.
intros Hdev Hsid Hres Hr Hfr HT HS HM Hhok E1 E2 E3 E4 E5 E6 E7 E8
       Eret Ehst Ehe Ehh Ehc.
subst. unfold ci5_Q, ci5_A, ci5_FR. Exists r idx. rewrite Hres. cbn [fst snd].
pose proof (ci5_msg_join shm m Mo b Mk mt ms me mes met HM) as JM. unfold ci5_msg_fields in JM.
pose proof (ci5_peer_join shp p P Hk Hhok E1 E2 E3 E4 E5) as JP. unfold prot4_ci_hs_fields in JP.
rewrite E6, Hsid, E7, E8 in JP.
pose proof (ci5_dev_join shd (p_device P) D) as JD. unfold prot4_ci_dev_fields in JD.
go_lowerx. match goal with HPf: Pf |- _ => specialize (Hfr HPf) end. entailer!.
sep_apply JM. sep_apply JP. sep_apply JD. unfold data_at_. cancel.
Qed.

(* lengths of the model's byte strings (v4's tactics, local to their section there) *)
Ltac ci5_len Hx Ha :=
  repeat first [ rewrite prot4_ci_Zlength_kdf1 | rewrite prot4_ci_Zlength_kdf2
               | rewrite prot4_ci_Zlength_mix_hash | rewrite prot4_ci_Zlength_init_ck
               | rewrite (Hx _ _) | rewrite (aead_enc_length _ _ Ha) | rewrite prot4_ci_Zlength_tai64n
               | rewrite prot4_ci_Zlength_clamp by assumption ];
  try assumption; try lia; try (unfold id_ok in *; lia).

(* the side conditions of ci5_exit on the handshake and the shim *)
Ltac ci5_side Hx Ha :=
  first [ reflexivity
        | intros _ X; discriminate X
        | intros X _; exact X
        | match goal with H: id_has _ = true |- _ => rewrite H; reflexivity end
        | match goal with |- hs_ok _ => idtac end;
          unfold hs_ok; cbn [hs_eph hs_rstatic hs_reph hs_ss hs_psk hs_hash hs_ck hs_ts
                             hs_set_eph hs_set_ckh hs_set_state];
          repeat split; ci5_len Hx Ha ].

(* the side condition of ci5_exit on the message fields *)
Ltac ci5_msg_side Hx Ha :=
  match goal with |- (_ = true \/ ?Mo <> None) -> _ =>
    let Hc := fresh "Hc" in intros Hc;
    try (let Hn := fresh "Hn" in
         assert (Hn: Mo <> None) by (destruct Hc as [Hc|Hc]; [discriminate Hc|exact Hc]);
         let Q1 := fresh "Q" in let Q2 := fresh "Q" in let Q3 := fresh "Q" in
         let Q4 := fresh "Q" in let Q5 := fresh "Q" in
         destruct (ci5_m0_eq Mo Hn) as (Q1&Q2&Q3&Q4&Q5); rewrite ?Q1, ?Q2, ?Q3, ?Q4, ?Q5);
    unfold im_ok5; cbn [im_type im_sender im_eph im_encs im_enct];
    try (destruct (memneq_bool _ _));
    repeat split; try reflexivity; ci5_len Hx Ha
  end.

Lemma ci5_loop {Espec: OracleKind}:
  forall gv kc shm m Mo shp p P shd wg D sht T S w kp tp kv tv,
  writable_share shm -> writable_share shp -> readable_share shd -> writable_share sht ->
  p_device P = wg -> hs_sid (p_hs P) = id_addr wg -> hs_in_pool T p ->
  im_ok5 (init_of Mo) -> hs_ok (p_hs P) -> id_ok (d_id D) -> Zlength kv = 32 -> Zlength tv = 12 ->
  semax (ci5_Delta x25519 aead_enc aead_dec CSw)
    (ci5_A gv kc shm m shp p shd wg (id_addr wg) (id_has (d_id D)) (id_pub (d_id D)) (d_itab D) sht
       (hs_rstatic (p_hs P)) (hs_ss (p_hs P)) kp tp (ci5_FR shm m shp p P shd wg D)
       True (Vint Int.zero) (ci5_mt0 Mo) (ci5_ms0 Mo) (ci5_me0 Mo) (ci5_mes0 Mo) (ci5_met0 Mo)
       (Vint (hs_state (p_hs P))) (bytes (hs_eph (p_hs P))) (bytes (hs_hash (p_hs P)))
       (bytes (hs_ck (p_hs P))) kv tv S w T)
    (Sloop ci_LB Sbreak)
    (normal_ret_assert (ci5_Q gv kc shm m Mo shp p P shd wg D sht T S w kp tp)).
Proof.
intros until tv. intros SHm SHp SHd SHt Hdev Hsid Hpool HMok HHok HIok Hkv Htv.
unfold x25519_props in Hx.
destruct HMok as (HMe & HMs & HMt).
remember (ci5_Q gv kc shm m Mo shp p P shd wg D sht T S w kp tp) as Q eqn:EQ.
apply semax_loop with (Q' := Q).
2: { eapply semax_pre; [|apply semax_break]. simpl RA_break. apply andp_left2, derives_refl. }
rewrite ci_LB_eq.
(* A: has_identity *)
eapply semax_seq.
{ apply prot5_ci_sA; auto. intros Hhas. simpl RA_normal. subst Q.
  eapply ci5_exit with (r := zeros32) (idx := Int.zero) (b := false) (Mk := init_of Mo) (Hk := p_hs P);
    auto; try reflexivity.
  all: first [ apply prot4_ci_res0; auto | intros _ X; discriminate X | rewrite Hhas; reflexivity
             | ci5_msg_side Hx Ha ]. }
apply ci5_extract; intros Hhas.
destruct HHok as (HHe & HHrs & HHre & HHss & HHpsk & HHh & HHck & HHts).
(* B: type, handshake_init, generate_secret, generate_public *)
eapply prot4_ci_seq4.
{ eapply prot5_ci_sB; auto; try reflexivity.
  { destruct Mo as [M|]; simpl; [unfold bytes; rewrite Zlength_map; exact HMe | reflexivity]. }
  intros r Hr Hb. simpl RA_normal. subst Q.
  eapply ci5_exit with (r := r) (idx := Int.zero) (b := false)
    (Mk := mkIM (Int.repr 1) (im_sender (init_of Mo))
             (if memneq_bool (clamp r) zeros32 then x25519 (clamp r) basepoint9 else im_eph (init_of Mo))
             (im_encs (init_of Mo)) (im_enct (init_of Mo)) (im_mac1 (init_of Mo)) (im_mac2 (init_of Mo)))
    (Hk := hs_set_eph (hs_set_ckh (p_hs P) init_ck (mix_hash init_hash (hs_rstatic (p_hs P)))) (clamp r));
    auto; try reflexivity.
  all: first [ apply prot4_ci_res1; auto | ci5_msg_side Hx Ha | ci5_side Hx Ha ]. }
apply extract_exists_pre; intros r. apply ci5_extract; intros (Hr & He & HE).
(* C: message_ephemeral, mix_dh *)
eapply prot4_ci_seq2.
{ eapply prot5_ci_sC; auto; try reflexivity; try (ci5_len Hx Ha).
  intros kv' Hd. simpl RA_normal. subst Q.
  eapply ci5_exit with (r := r) (idx := Int.zero).
  3: apply prot4_ci_res2; auto.
  all: auto; try reflexivity; first [ ci5_msg_side Hx Ha | ci5_side Hx Ha ]. }
apply ci5_extract; intros Hd.
(* D: encrypted static, mix_precomputed_dh *)
eapply prot4_ci_seq2.
{ eapply prot5_ci_sD; auto; try reflexivity; try (ci5_len Hx Ha).
  intros kv' Hs. simpl RA_normal. subst Q.
  eapply ci5_exit with (r := r) (idx := Int.zero).
  3: apply prot4_ci_res3; auto.
  all: auto; try reflexivity; first [ ci5_msg_side Hx Ha | ci5_side Hx Ha ]. }
apply ci5_extract; intros Hs.
(* E: timestamp *)
eapply prot4_ci_seq2.
{ eapply prot5_ci_sE with (ts := tai64n (s_rsec S) (s_rnsec S)); auto; try reflexivity;
    try (ci5_len Hx Ha). }
apply ci5_extract; intros _.
(* F: index, state, ret; then the success exit *)
eapply semax_post.
5: eapply prot5_ci_sF with (Qc := Q) (R := normal_ret_assert Q); auto.
- cbv beta iota delta [RA_normal RA_break RA_continue RA_return overridePost loop1_ret_assert normal_ret_assert]. apply andp_left2. Intros idx. subst Q.
  eapply ci5_exit with (r := r) (idx := idx).
  3: apply prot4_ci_res4; auto.
  all: auto; try reflexivity; first [ ci5_msg_side Hx Ha | ci5_side Hx Ha ].
- cbv beta iota delta [RA_normal RA_break RA_continue RA_return overridePost loop1_ret_assert normal_ret_assert]. apply andp_left2, derives_refl.
- cbv beta iota delta [RA_normal RA_break RA_continue RA_return overridePost loop1_ret_assert normal_ret_assert]. apply andp_left2, derives_refl.
- intros vl. cbv beta iota delta [RA_normal RA_break RA_continue RA_return overridePost loop1_ret_assert normal_ret_assert]. apply andp_left2, derives_refl.
Qed.

End Main.

#[local] Existing Instance Noise.CS.
Local Open Scope logic.

Theorem prot5_ci_bodies :
  forall x25519 aead_enc aead_dec (CSw: compspecs),
  x25519_props x25519 -> aead_props aead_enc aead_dec ->
  @semax_body (QPvarspecs Noise.qp) (Gprot5 x25519 aead_enc aead_dec CSw Noise.CS) Noise.CS
    WgNoise.noise.code.f_wg_noise_handshake_create_initiation (wg_noise_handshake_create_initiation_spec x25519 aead_enc).
Proof.
intros x25519 aead_enc aead_dec CSw Hx Ha.
start_function.
unfold MORE_COMMANDS, abbreviate.
match goal with |- semax _ _ ?c _ =>
  change c with (Ssequence ci_B0 (Ssequence (Sloop ci_LB Sbreak) ci_END)) end.
eapply semax_pre with (P' :=
  PROP (im_ok5 (init_of Mo); hs_ok (p_hs P); id_ok (d_id D))
  LOCAL (lvar I._key (tarray tuchar 32) v_key; lvar I._timestamp (tarray tuchar 12) v_timestamp;
         gvars gv; temp I._dst m; temp I._handshake (hs_addr p))
  SEP (@data_at_ Noise.CS Tsh (tarray tuchar 32) v_key; @data_at_ Noise.CS Tsh (tarray tuchar 12) v_timestamp;
       ci5_msg_fields shm m (ci5_mt0 Mo) (ci5_ms0 Mo) (ci5_me0 Mo) (ci5_mes0 Mo) (ci5_met0 Mo); ci5_msg_frame shm m;
       prot4_ci_hs_fields shp p (p_hs P); @field_at Noise.CS shp t_peer [StructField I._device] (p_device P) p;
       ci5_peer_frame shp p P;
       prot4_ci_dev_fields shd wg D; ci5_dev_frame shd wg D;
       itable sht (d_itab D) T; shim_state4 gv S w; noise_globals gv kc; wg_consts5 gv)).
{ sep_apply ci5_msg_split. Intros. sep_apply ci5_peer_split. Intros.
  sep_apply ci5_dev_split. Intros. entailer!. }
apply semax_extract_PROP; intro HMok. apply semax_extract_PROP; intro HHok. apply semax_extract_PROP; intro HIok.
change Delta with (ci5_Delta x25519 aead_enc aead_dec CSw).
eapply semax_seq' with (P' :=
  ci5_A gv kc shm m shp p shd wg (id_addr wg) (id_has (d_id D)) (id_pub (d_id D)) (d_itab D) sht
    (hs_rstatic (p_hs P)) (hs_ss (p_hs P)) v_key v_timestamp (ci5_FR shm m shp p P shd wg D)
    True (Vint Int.zero) (ci5_mt0 Mo) (ci5_ms0 Mo) (ci5_me0 Mo) (ci5_mes0 Mo) (ci5_met0 Mo)
    (Vint (hs_state (p_hs P))) (bytes (hs_eph (p_hs P))) (bytes (hs_hash (p_hs P)))
    (bytes (hs_ck (p_hs P))) (Zrepeat Vundef 32) (Zrepeat Vundef 12) S w T).
{ unfold ci5_Delta. simplify_func_tycontext. unfold ci_B0. abbreviate_semax.
  forward. unfold ci5_A, ci5_FR, ci5_msg_fields, prot4_ci_hs_fields, prot4_ci_dev_fields.
  rewrite H, H0. entailer!. }
eapply semax_seq'.
{ apply ci5_loop; auto. }
unfold ci5_Q. Intros r idx.
change (ci5_Delta x25519 aead_enc aead_dec CSw) with Delta. unfold ci_END. abbreviate_semax.
forward_call (Tsh, v_key, 32).
forward.
Exists r idx. remember (ci_res x25519 aead_enc D P (init_of Mo) S r idx) as res eqn:Eres. clear Eres.
entailer!. destruct (fst (fst res)); reflexivity.
Qed.
