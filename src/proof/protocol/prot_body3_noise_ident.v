(* Body proofs of the protocol piece, group noise_ident.
   Target: prot_bodies3_noise_ident.  Prove each function's body against its specification (prot_specs3.v) in the
   compspecs of its unit, with the context Gprot3 (prot_prog3.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_prog3.
Require WgNoise.noise.code WgNoise.cookie.code WgNoise.shim.code.
Require Import VST.msl.iter_sepcon.

Section NoiseIdent.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.

#[local] Existing Instance Noise.CS.
Local Open Scope logic.

Definition Gni := Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS.

Lemma prot3_noise_ident_body_set_identity :
  @semax_body (QPvarspecs Noise.qp) Gni Noise.CS
    WgNoise.noise.code.f_wg_noise_set_static_identity_private_key (wg_noise_set_static_identity_private_key_spec x25519).
Proof.
  start_function.
  unfold identity_rep. Intros lk.
  assert_PROP (field_compatible t_sid [] sid) by entailer!.
  destruct H0 as [Hpub Hpriv].
  unfold_data_at (data_at sh t_sid _ sid).
  rewrite (field_at_data_at sh t_sid [StructField I._static_private]).
  rewrite (field_at_data_at sh t_sid [StructField I._static_public]).
  simpl nested_field_type.
  unfold bytes_at, bytes; rewrite H.
  unfold wg_consts; Intros.
  forward_call (sh, shk, field_address t_sid [StructField I._static_private] sid, pk, 32, raw).
  forward_call (sh, field_address t_sid [StructField I._static_private] sid, raw).
  forward_call (sh, field_address t_sid [StructField I._static_public] sid, map Vubyte (id_pub ID), shk, pk, raw, gv).
  { entailer!. simpl. rewrite field_address_offset by auto with field_compatible. reflexivity. }
  { rewrite Zlength_map; auto. }
  forward.
  assert_PROP (Zlength (if memneq_bool raw zeros32 then map Vubyte (x25519 raw basepoint9) else map Vubyte (id_pub ID)) = 32) by entailer!.
  assert (Hcl: Zlength (clamp raw) = 32) by (unfold clamp; rewrite !upd_Znth_Zlength by list_solve; lia).
  unfold identity_rep, identity_of, wg_consts, bytes_at, bytes; simpl id_pub; simpl id_priv; simpl id_has.
  Intros. Exists lk.
  remember (memneq_bool (x25519 raw basepoint9) zeros32) as b2.
  assert (Hb: forall b, force_val (sem_cast_i2bool (Val.of_bool b)) = Val.of_bool b) by (destruct b; reflexivity).
  rewrite Hb.
  destruct (memneq_bool raw zeros32); rewrite ?Zlength_map in H0;
  (unfold_data_at (data_at sh t_sid _ sid);
   rewrite (field_at_data_at sh t_sid [StructField I._static_private]);
   rewrite (field_at_data_at sh t_sid [StructField I._static_public]);
   simpl nested_field_type; rewrite H; entailer!; split; auto).
Qed.

Lemma prot3_noise_ident_hs_addr : forall p, field_compatible t_peer [] p ->
  field_address t_peer (DOT I._handshake) p = hs_addr p.
Proof.
  intros. rewrite field_address_offset by auto with field_compatible. reflexivity.
Qed.

Lemma prot3_noise_ident_sid_peer : forall sh p (v: val), field_compatible t_peer [] p ->
  field_at sh t_hs (DOT I._static_identity) v (hs_addr p) =
  field_at sh t_peer (DOT I._handshake DOT I._static_identity) v p.
Proof.
  intros. rewrite <- (prot3_noise_ident_hs_addr p) by auto.
  rewrite !field_at_data_at, (field_address_app t_peer (DOT I._handshake) (DOT I._static_identity)).
  reflexivity.
Qed.

Lemma prot3_noise_ident_ss_peer : forall sh p (v: list val), field_compatible t_peer [] p ->
  field_at sh t_hs (DOT I._precomputed_static_static) v (hs_addr p) =
  data_at sh (tarray tuchar 32) v (field_address t_peer (DOT I._handshake DOT I._precomputed_static_static) p).
Proof.
  intros. rewrite <- (prot3_noise_ident_hs_addr p) by auto.
  rewrite field_at_data_at, (field_address_app t_peer (DOT I._handshake) (DOT I._precomputed_static_static)).
  reflexivity.
Qed.

Lemma prot3_noise_ident_rs_peer : forall sh p (v: list val), field_compatible t_peer [] p ->
  field_at sh t_hs (DOT I._remote_static) v (hs_addr p) =
  data_at sh (tarray tuchar 32) v (field_address t_peer (DOT I._handshake DOT I._remote_static) p).
Proof.
  intros. rewrite <- (prot3_noise_ident_hs_addr p) by auto.
  rewrite field_at_data_at, (field_address_app t_peer (DOT I._handshake) (DOT I._remote_static)).
  reflexivity.
Qed.

Lemma prot3_noise_ident_sid_split : forall sh s (pub priv: list val) (lk has: val),
  data_at sh t_sid (pub, (priv, (lk, has))) s =
  field_at sh t_sid (DOT I._static_public) pub s *
  data_at sh (tarray tuchar 32) priv (field_address t_sid (DOT I._static_private) s) *
  field_at sh t_sid (DOT I._lock) lk s * field_at sh t_sid (DOT I._has_identity) has s * spacer sh 69 72 s.
Proof.
  intros. unfold_data_at (data_at _ _ _ _).
  rewrite (field_at_data_at sh t_sid (DOT I._static_private)). rewrite !sepcon_assoc. reflexivity.
Qed.

Lemma prot3_noise_ident_body_precompute :
  @semax_body (QPvarspecs Noise.qp) Gni Noise.CS
    WgNoise.noise.code.f_wg_noise_precompute_static_static (wg_noise_precompute_static_static_spec x25519).
Proof.
  start_function.
  unfold hs_rep, identity_rep. Intros lkh lki.
  rewrite (prot3_noise_ident_sid_peer sh p (hs_sid H) H0).
  forward. forward.
  { entailer!. destruct (id_has ID); simpl; auto. }
  assert_PROP (field_compatible t_sid [] (hs_sid H)) as FCs by entailer!.
  assert (FCp: field_compatible t_sid (DOT I._static_private) (hs_sid H)) by auto with field_compatible.
  assert (FCss: field_compatible t_peer (DOT I._handshake DOT I._precomputed_static_static) p) by auto with field_compatible.
  assert (FCrs: field_compatible t_peer (DOT I._handshake DOT I._remote_static) p) by auto with field_compatible.
  rewrite prot3_noise_ident_sid_split, (prot3_noise_ident_ss_peer sh p _ H0), (prot3_noise_ident_rs_peer sh p _ H0).
  unfold wg_consts. Intros.
  freeze [0;1;3;5;7;8;9;10;11;12;13;14;15;17;18;19;20;22;23] FR.
  forward_if (PROP () LOCAL (temp noise.code._t'1 (Val.of_bool (negb (id_has ID && dh_ok x25519 (id_priv ID) (hs_rstatic H)))); temp noise.code._peer p; gvars gv)
   SEP (FRZL FR;
   field_at sh t_peer (DOT I._handshake DOT I._static_identity) (hs_sid H) p;
   data_at sh (tarray tuchar 32) (bytes (hs_rstatic H)) (field_address t_peer (DOT I._handshake DOT I._remote_static) p);
   data_at sh (tarray tuchar 32) (bytes (if id_has ID then x25519 (id_priv ID) (hs_rstatic H) else hs_ss H)) (field_address t_peer (DOT I._handshake DOT I._precomputed_static_static) p);
   data_at shi (tarray tuchar 32) (bytes (id_priv ID)) (field_address t_sid (DOT I._static_private) (hs_sid H));
   curve25519_globals gv)).
  - forward. destruct (id_has ID); [inv H3|]. entailer!.
  - forward. destruct (id_has ID); [|inv H3].
    destruct H2 as [Hpub Hpriv]; destruct H1 as (?&Hrs&?).
    unfold bytes. forward_call (sh, field_address t_peer (DOT I._handshake DOT I._precomputed_static_static) p, shi, field_address t_sid (DOT I._static_private) (hs_sid H), id_priv ID, sh, field_address t_peer (DOT I._handshake DOT I._remote_static) p, hs_rstatic H, gv).
    forward. entailer!. unfold dh_ok. destruct (memneq_bool _ _); reflexivity.
  - destruct (andb (id_has ID) (dh_ok x25519 (id_priv ID) (hs_rstatic H))) eqn:Hb; simpl negb.
    + forward_if.
      { contradiction. }
      forward.
      pose proof Hb as Hb'. apply andb_prop in Hb' as [Hh _]. rewrite Hh.
      assert_PROP (Zlength (x25519 (id_priv ID) (hs_rstatic H)) = 32) as Lx.
      { entailer!. unfold bytes in *. rewrite Zlength_map in *. assumption. }
      unfold hs_rep, identity_rep, wg_consts, precomputed. rewrite Hb. unfold hs_set_ss; cbn [hs_state hs_lic hs_sid hs_eph hs_rstatic hs_reph hs_ss hs_psk hs_hash hs_ck hs_ts hs_rindex].
      thaw FR.
      rewrite <- (prot3_noise_ident_sid_peer sh p (hs_sid H) H0), <- (prot3_noise_ident_ss_peer sh p _ H0), <- (prot3_noise_ident_rs_peer sh p _ H0).
      entailer!.
      { destruct H1 as (?&?&?&?&?&?&?&?); repeat split; auto. }
      Exists lki. rewrite prot3_noise_ident_sid_split, exp_sepcon1. Exists lkh. cancel.
    + forward_if.
      2: { exfalso; apply Int.one_not_zero; assumption. }
      forward_call (sh, field_address t_peer (DOT I._handshake DOT I._precomputed_static_static) p, 0, 32).
      unfold hs_rep, identity_rep, wg_consts, precomputed. rewrite Hb. unfold hs_set_ss; cbn [hs_state hs_lic hs_sid hs_eph hs_rstatic hs_reph hs_ss hs_psk hs_hash hs_ck hs_ts hs_rindex].
      change (Zrepeat (Vubyte (Byte.repr 0)) 32) with (bytes zeros32).
      thaw FR.
      rewrite <- (prot3_noise_ident_sid_peer sh p (hs_sid H) H0), <- (prot3_noise_ident_ss_peer sh p _ H0), <- (prot3_noise_ident_rs_peer sh p _ H0).
      entailer!.
      { destruct H1 as (?&?&?&?&?&?&?&?); repeat split; auto. }
      Exists lki. rewrite prot3_noise_ident_sid_split, exp_sepcon1. Exists lkh. cancel.
Qed.

(* ---- wg_noise_handshake_clear: the handshake's entry in the itable's pool ---- *)
Lemma prot3_noise_ident_split (D: list (val * share * entry)) a sh E (f: val * share * entry -> mpred) :
  sfind D a = Some (sh, E) -> iter_sepcon f D = f (a, sh, E) * iter_sepcon f (sdel D a).
Proof.
  induction D as [|[[x shx] w] D IH]; simpl; intros H; [discriminate|].
  destruct (EqDec_val x a); [inv H; reflexivity|].
  rewrite (IH H); simpl. rewrite <- !sepcon_assoc, (sepcon_comm (f _) (f _)). reflexivity.
Qed.

Lemma prot3_noise_ident_sfind_In (D: list (val * share * entry)) a sh E :
  sfind D a = Some (sh, E) -> In (a, sh, E) D.
Proof.
  induction D as [|[[x shx] w] D IH]; simpl; intros H; [discriminate|].
  destruct (EqDec_val x a); [inv H; auto|auto].
Qed.

Lemma prot3_noise_ident_saddrs_in (D: list (val * share * entry)) x sh E :
  In (x, sh, E) D -> In x (saddrs D).
Proof.
  intros H. unfold saddrs. apply (in_map (fun '(x, _, _) => x) D (x, sh, E)) in H. exact H.
Qed.

Lemma prot3_noise_ident_entry_fa sh v p :
  field_compatible t_peer [] p ->
  data_at sh t_entry_s v (hs_addr p) = field_at sh t_hs (DOT I._entry) v (hs_addr p).
Proof.
  intros FC.
  assert (FC1: field_compatible t_peer (DOT I._handshake) p) by auto with field_compatible.
  assert (FC2: field_compatible t_hs [] (hs_addr p)).
  { apply field_compatible_nested_field in FC1.
    exact FC1. }
  assert (FC3: field_compatible t_hs (DOT I._entry) (hs_addr p)) by auto with field_compatible.
  rewrite field_at_data_at. rewrite field_address_offset by auto. simpl.
  rewrite isptr_offset_val_zero by (unfold hs_addr; destruct FC as [Hp _]; destruct p; try contradiction; exact I).
  reflexivity.
Qed.

Lemma prot3_noise_ident_open sht tab T p sh E :
  field_compatible t_peer [] p -> itable_wf T -> sfind (t_D T) (hs_addr p) = Some (sh, E) ->
  itable sht tab T =
  data_at sht t_itab (hd nullval (t_L T)) tab *
  (field_at sh t_hs (DOT I._entry) (entry_val E (succ_in (t_L T) (hs_addr p)) (vin (hs_addr p) (t_L T))) (hs_addr p) *
   iter_sepcon (pool_item_rep (t_L T)) (sdel (t_D T) (hs_addr p))).
Proof.
  intros FC W HS. unfold itable. rewrite (prot3_noise_ident_split _ _ _ _ _ HS).
  unfold pool_item_rep at 1, entry_at. rewrite prot3_noise_ident_entry_fa by auto.
  apply pred_ext; entailer!.
Qed.

Lemma prot3_noise_ident_body_hs_clear :
  @semax_body (QPvarspecs Noise.qp) Gni Noise.CS
    WgNoise.noise.code.f_wg_noise_handshake_clear wg_noise_handshake_clear_spec.
Proof.
  start_function.
  match goal with H: hs_in_pool _ _ |- _ => destruct H as (E & HE & HEp) end.
  assert_PROP (field_compatible t_peer [] p) as FC by (unfold peer_rep; entailer!).
  assert_PROP (itable_wf T) as W by (unfold itable; entailer!).
  unfold t_entry in HE. destruct (sfind (t_D T) (hs_addr p)) as [[she E']|] eqn:HS; [|discriminate]. injection HE as HE. subst E'.
  assert (WS: writable_share she).
  { destruct W as (_ & _ & _ & HF). apply prot3_noise_ident_sfind_In in HS.
    rewrite Forall_forall in HF. apply (HF _ HS). }
  rewrite (prot3_noise_ident_open sht (d_itab D) T p she E) by auto.
  flatten_sepcon_in_SEP. flatten_sepcon_in_SEP.
  unfold entry_val.
  forward.
  sep_apply (derives_refl' _ _ (eq_sym (prot3_noise_ident_open sht (d_itab D) T p she E FC W HS))).
  rewrite HEp.
  unfold peer_rep. Intros. rewrite H.
  unfold device_rep. Intros.
  forward.
  forward.
  { unfold itable. Intros. entailer!. }
  forward_call (sht, d_itab D, T, hs_addr p, @None (share * entry)).
  { unfold hs_addr; destruct FC as [Hp _]; rewrite isptr_offset_val; exact Hp. }
  { apply prop_right. simpl. unfold hs_addr; destruct FC as [Hp _]; destruct p; try contradiction; simpl.
    rewrite Ptrofs.add_zero. reflexivity. }
  { simpl raw_rep. rewrite emp_sepcon. cancel. }
  { simpl raw_ok. apply prot3_noise_ident_saddrs_in with she E. apply prot3_noise_ident_sfind_In. exact HS. }
  simpl raw_rep.
  forward_call (shp, hs_addr p, p_hs P).
  entailer!. unfold peer_rep, device_rep. simpl. entailer!.
Qed.

End NoiseIdent.

Theorem prot_bodies3_noise_ident :
  forall x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs),
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  (@semax_body (QPvarspecs Noise.qp) (Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
      WgNoise.noise.code.f_wg_noise_set_static_identity_private_key (wg_noise_set_static_identity_private_key_spec x25519)) /\
  (@semax_body (QPvarspecs Noise.qp) (Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
      WgNoise.noise.code.f_wg_noise_precompute_static_static (wg_noise_precompute_static_static_spec x25519)) /\
  (@semax_body (QPvarspecs Noise.qp) (Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
      WgNoise.noise.code.f_wg_noise_handshake_clear wg_noise_handshake_clear_spec).
Proof.
  intros. repeat match goal with |- _ /\ _ => split end; first [apply prot3_noise_ident_body_set_identity | apply prot3_noise_ident_body_precompute | apply prot3_noise_ident_body_hs_clear].
Qed.
