(* law handshake: main's phase P1, segment C = statements 14..20: the identity CHECKs, m_static_public_field x2 and their CHECKs.
   (section P1). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_specs3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.handshake.hhs3_spec.
Require Import WgNoise.proof.harness.handshake.hhs3_defs.
Require Import WgNoise.proof.harness.handshake.hhs3_conv.
Require Import WgNoise.proof.harness.handshake.hhs3_p1_defs.
Require WgNoise.harness.x_handshake.code.

#[local] Existing Instance W_handshake.
Local Open Scope Z_scope.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

#[local] Instance hhs3C_cce_N : change_composite_env Noise.CS W_handshake.
Proof. make_cs_preserve Noise.CS W_handshake. Defined.
#[local] Instance hhs3C_cce_H : change_composite_env HCS W_handshake.
Proof. make_cs_preserve HCS W_handshake. Defined.

Lemma hhs3C_bytes_eqb_refl A : bytes_eqb A A = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec A A); congruence. Qed.

#[local] Instance hhs3C_cce_NH : change_composite_env Noise.CS HCS.
Proof. make_cs_preserve Noise.CS HCS. Defined.

Lemma hhs3C_data_at_cs {cs1 cs2} {CCE: change_composite_env cs1 cs2} (sh: share) (t: type) (v1: @reptype cs1 t)
  (v2: @reptype cs2 t) (p: val) :
  JMeq v1 v2 -> cs_preserve_type cs1 cs2 (coeq _ _) t = true ->
  @data_at cs1 sh t v1 p = @data_at cs2 sh t v2 p.
Proof. intros. exact (f_equal (fun f => f p) (@data_at_change_composite cs1 cs2 CCE sh t v1 v2 H H0)). Qed.

Lemma hhs3C_field_at_cs {cs1 cs2} {CCE: change_composite_env cs1 cs2} (sh: share) (t: type) (gfs: list gfield)
  (v1: @reptype cs1 (@nested_field_type cs1 t gfs)) (v2: @reptype cs2 (@nested_field_type cs2 t gfs)) (p: val) :
  JMeq v1 v2 -> cs_preserve_type cs1 cs2 (coeq _ _) t = true ->
  @field_at cs1 sh t gfs v1 p = @field_at cs2 sh t gfs v2 p.
Proof. intros. exact (f_equal (fun f => f p) (@field_at_change_composite cs1 cs2 CCE sh t gfs v1 v2 H H0)). Qed.

Definition hhs3C_has (sh: share) (wg: val) (b: bool) : mpred :=
  @field_at W_handshake sh t_dev (DOT I._static_identity DOT I._has_identity) (Val.of_bool b) wg.
Definition hhs3C_sidrest (sh: share) (wg: val) (lk: val) : mpred :=
  (@field_at Noise.CS sh t_dev (DOT I._static_identity DOT I._lock) lk wg * spacer sh 77 80 wg)%logic.

Lemma hhs3C_sid_split sh wg pub priv (lk: val) b (v: @reptype Noise.CS t_sid) :
  @field_compatible Noise.CS t_dev [] wg -> Zlength pub = 32 -> Zlength priv = 32 ->
  v = (bytes pub, (bytes priv, (lk, Val.of_bool b))) ->
  @data_at Noise.CS sh t_sid v (id_addr wg) =
  (hhs3C_has sh wg b * hbytes sh priv (offset_val 40 wg) * hbytes sh pub (offset_val 8 wg) *
   hhs3C_sidrest sh wg lk)%logic.
Proof.
  intros FC Lpub Lpriv ->.
  assert (E: id_addr wg = @field_address Noise.CS t_dev (DOT I._static_identity) wg).
  { rewrite field_address_offset by auto with field_compatible. reflexivity. }
  transitivity (@field_at Noise.CS sh t_dev (DOT I._static_identity) (bytes pub, (bytes priv, (lk, Val.of_bool b))) wg).
  { rewrite field_at_data_at, <- E. reflexivity. }
  unfold_field_at 1%nat.
  assert (Hpub: @field_at Noise.CS sh t_dev (DOT I._static_identity DOT I._static_public) (bytes pub) wg =
                hbytes sh pub (offset_val 8 wg)).
  { rewrite field_at_data_at, field_address_offset by auto with field_compatible. unfold hbytes. rewrite Lpub.
    apply (@hhs3C_data_at_cs Noise.CS HCS _); [apply JMeq_refl | reflexivity]. }
  assert (Hpriv: @field_at Noise.CS sh t_dev (DOT I._static_identity DOT I._static_private) (bytes priv) wg =
                 hbytes sh priv (offset_val 40 wg)).
  { rewrite field_at_data_at, field_address_offset by auto with field_compatible. unfold hbytes. rewrite Lpriv.
    apply (@hhs3C_data_at_cs Noise.CS HCS _); [apply JMeq_refl | reflexivity]. }
  assert (Hhas: @field_at Noise.CS sh t_dev (DOT I._static_identity DOT I._has_identity) (Val.of_bool b) wg =
                hhs3C_has sh wg b).
  { unfold hhs3C_has. apply (@hhs3C_field_at_cs Noise.CS W_handshake _); [apply JMeq_refl | reflexivity]. }
  simpl in Hpub, Hpriv, Hhas. rewrite Hpub, Hpriv, Hhas. unfold hhs3C_sidrest. apply pred_ext; cancel.
Qed.

Definition hhs3C_ok (sh: share) (p: val) (b: bool) : mpred :=
  @field_at W_handshake sh t_mident (DOT HC._ok) (Vint (if b then Int.one else Int.zero)) p.

Lemma hhs3C_mid_split sh p I :
  @field_compatible HCS t_mident [] p -> Zlength (mi_priv I) = 32 -> Zlength (mi_pub I) = 32 ->
  @data_at HCS sh t_mident (mident_val I) p =
  (hbytes sh (mi_priv I) p * hbytes sh (mi_pub I) (offset_val 32 p) * hhs3C_ok sh p (mi_ok I))%logic.
Proof.
  intros FC Lpriv Lpub.
  unfold mident_val. unfold_data_at (@data_at HCS sh t_mident _ p).
  assert (Hpriv: @field_at HCS sh t_mident (DOT HC._priv) (bytes (mi_priv I)) p = hbytes sh (mi_priv I) p).
  { rewrite field_at_data_at, field_address_offset by auto with field_compatible. unfold hbytes. rewrite Lpriv.
    rewrite isptr_offset_val_zero by (apply field_compatible_isptr in FC; exact FC). reflexivity. }
  assert (Hpub: @field_at HCS sh t_mident (DOT HC._pub) (bytes (mi_pub I)) p = hbytes sh (mi_pub I) (offset_val 32 p)).
  { rewrite field_at_data_at, field_address_offset by auto with field_compatible. unfold hbytes. rewrite Lpub.
    reflexivity. }
  assert (Hok: @field_at HCS sh t_mident (DOT HC._ok) (Vint (if mi_ok I then Int.one else Int.zero)) p =
               hhs3C_ok sh p (mi_ok I)).
  { unfold hhs3C_ok. apply (@hhs3C_field_at_cs HCS W_handshake _); [apply JMeq_refl | reflexivity]. }
  simpl in Hpub, Hpriv, Hok. rewrite Hpub, Hpriv, Hok. apply pred_ext; cancel.
Qed.

Lemma hhs3C_setup_has raw : id_has (setup_identity x25519 raw) = mi_ok (mident_of x25519 raw).
Proof. reflexivity. Qed.
Lemma hhs3C_setup_priv raw : id_priv (setup_identity x25519 raw) = mi_priv (mident_of x25519 raw).
Proof. reflexivity. Qed.
Lemma hhs3C_setup_pub raw :
  id_pub (setup_identity x25519 raw) = static_public_field raw (mi_pub (mident_of x25519 raw)).
Proof. reflexivity. Qed.

Definition hhs3C_devrest (sh: share) (wg: val) (D: device) (lk: val) : mpred :=
  (@field_at Noise.CS sh t_dev [StructField I._dev] (d_dev D) wg * hhs3C_sidrest sh wg lk *
   checker_rep sh (cc_addr wg) (d_cc D) *
   @field_at Noise.CS sh t_dev [StructField I._peer_hashtable] (d_ptab D) wg *
   @field_at Noise.CS sh t_dev [StructField I._index_hashtable] (d_itab D) wg)%logic.

Lemma hhs3C_dev_split sh wg D :
  device_rep sh wg D =
  (EX lk: val, !! (@field_compatible Noise.CS t_dev [] wg /\ id_ok (d_id D)) &&
   (hhs3C_has sh wg (id_has (d_id D)) * hbytes sh (id_priv (d_id D)) (offset_val 40 wg) *
    hbytes sh (id_pub (d_id D)) (offset_val 8 wg) * hhs3C_devrest sh wg D lk))%logic.
Proof.
  unfold device_rep, identity_rep, hhs3C_devrest. apply pred_ext.
  - Intros lk. Exists lk. pose proof H0 as [Lp Lq].
    rewrite (hhs3C_sid_split sh wg (id_pub (d_id D)) (id_priv (d_id D)) lk (id_has (d_id D)) _ H Lp Lq eq_refl).
    entailer!.
  - Intros lk. pose proof H0 as [Lp Lq].
    entailer!.
    Exists lk.
    rewrite (hhs3C_sid_split sh wg (id_pub (d_id D)) (id_priv (d_id D)) lk (id_has (d_id D)) _ H Lp Lq eq_refl).
    cancel.
Qed.

Lemma hhs3C_mid_join sh p I :
  @field_compatible HCS t_mident [] p -> Zlength (mi_priv I) = 32 -> Zlength (mi_pub I) = 32 ->
  (hbytes sh (mi_priv I) p * hbytes sh (mi_pub I) (offset_val 32 p) *
   @field_at W_handshake sh t_mident (DOT HC._ok) (Vint (if mi_ok I then Int.one else Int.zero)) p
   |-- @data_at HCS sh t_mident (mident_val I) p)%logic.
Proof. intros. rewrite hhs3C_mid_split by auto. unfold hhs3C_ok. cancel. Qed.

Lemma hhs3C_hbytes_hout sh A p : Zlength A = 32 -> (hbytes sh A p |-- hout sh 32 p)%logic.
Proof. intros HA. unfold hbytes, hout. rewrite HA. apply data_at_data_at_. Qed.

Lemma hhs3C_dev_join sh wg D lk raw :
  d_id D = setup_identity x25519 raw -> @field_compatible Noise.CS t_dev [] wg -> id_ok (d_id D) ->
  (@field_at W_handshake sh t_dev (DOT I._static_identity DOT I._has_identity)
     (Val.of_bool (mi_ok (mident_of x25519 raw))) wg *
   hbytes sh (mi_priv (mident_of x25519 raw)) (offset_val 40 wg) *
   hbytes sh (static_public_field raw (mi_pub (mident_of x25519 raw))) (offset_val 8 wg) *
   hhs3C_devrest sh wg D lk |-- device_rep sh wg D)%logic.
Proof.
  intros HD FC ID. rewrite hhs3C_dev_split. Exists lk. rewrite HD in *.
  rewrite hhs3C_setup_has, hhs3C_setup_priv, hhs3C_setup_pub. unfold hhs3C_has. entailer!.
Qed.

Ltac hhs3C_args :=
  entailer!; simpl; rewrite ?offset_offset_val, ?isptr_offset_val_zero by auto; reflexivity.

Ltac hhs3C_dead :=
  match goal with H: _ |- _ =>
    solve [exfalso; revert H; rewrite ?Int.eq_true; simpl; intro H;
           first [discriminate H | apply H; reflexivity | exact (Int.one_not_zero H) | inversion H]] end.

Ltac hhs3C_chk1 :=
  forward; forward; apply semax_if_seq; forward_if;
  [ forward; forward; forward; forward_if; [ hhs3C_dead | forward; unfold hbytes; entailer! ]
  | hhs3C_dead ].

Lemma hhs3_p1_C_ok {Espec: OracleKind} gv L FR :
  hhs3_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hhs3_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hhs3_p1_SB x25519 gv L FR) hhs3_p1_C
    (overridePost (hhs3_p1_SB x25519 gv L FR) (hhs3_R gv)).
Proof.
  intros HH. unfold hhs3_p1_SB, hhs3_Delta, hhs3_R, hhs3_p1_C. simplify_func_tycontext. abbreviate_semax.
  Intros R S a0 f0 l0.
  unfold hhs3_globs, hhs3_cnt_temps, hhs3_lvars, hhs3_p1_rest, hhs3_scr_tmp; cbn [app].
  destruct HH as (Hx & _). pose proof H as (La & Lb & _).
  rewrite (hhs3C_dev_split Tsh (l_wa L)), (hhs3C_dev_split Tsh (l_wb L)). Intros lka lkb.
  rename H1 into FCa, H2 into IDa, H3 into FCb, H4 into IDb.
  change (d_id (hhs3_DA x25519 R L)) with (setup_identity x25519 (r_rawa R)) in *.
  change (d_id (hhs3_DB x25519 R L)) with (setup_identity x25519 (r_rawb R)) in *.
  unfold hhs3_IA, hhs3_IB.
  assert (LPa: Zlength (mi_priv (mident_of x25519 (r_rawa R))) = 32) by (destruct IDa; auto).
  assert (LPb: Zlength (mi_priv (mident_of x25519 (r_rawb R))) = 32) by (destruct IDb; auto).
  assert (LQa: Zlength (mi_pub (mident_of x25519 (r_rawa R))) = 32) by apply Hx.
  assert (LQb: Zlength (mi_pub (mident_of x25519 (r_rawb R))) = 32) by apply Hx.
  rewrite !hhs3C_setup_has, !hhs3C_setup_priv, !hhs3C_setup_pub.
  assert_PROP (@field_compatible HCS t_mident [] (l_ia L) /\ @field_compatible HCS t_mident [] (l_ib L)) as FCi
    by entailer!.
  destruct FCi as [FCia FCib].
  rewrite (hhs3C_mid_split Tsh (l_ia L)) by auto. rewrite (hhs3C_mid_split Tsh (l_ib L)) by auto.
  Intros.
  unfold hhs3C_has, hhs3C_ok.
  (* CHECK(wa.has_identity == ia.ok && wb.has_identity == ib.ok) *)
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  { apply ENTAIL_refl. }
  2: { forward. apply ENTAIL_refl. }
  { destruct (mi_ok (mident_of x25519 (r_rawa R))), (mi_ok (mident_of x25519 (r_rawb R))).
    - hhs3C_chk1.
    - hhs3C_chk1.
    - hhs3C_chk1.
    - hhs3C_chk1. }
  (* CHECK(bytes_eq(wa.static_private, ia.priv, 32)) *)
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  { apply ENTAIL_refl. }
  2: { forward. apply ENTAIL_refl. }
  { forward_call (Tsh, offset_val 40 (l_wa L), mi_priv (mident_of x25519 (r_rawa R)),
                  Tsh, l_ia L, mi_priv (mident_of x25519 (r_rawa R))).
    { rewrite LPa. hhs3C_args. }
    rewrite hhs3C_bytes_eqb_refl. forward_if; [hhs3C_dead | ]. forward. entailer!. }
  (* CHECK(bytes_eq(wb.static_private, ib.priv, 32)) *)
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  { apply ENTAIL_refl. }
  2: { forward. apply ENTAIL_refl. }
  { forward_call (Tsh, offset_val 40 (l_wb L), mi_priv (mident_of x25519 (r_rawb R)),
                  Tsh, l_ib L, mi_priv (mident_of x25519 (r_rawb R))).
    { rewrite LPb. hhs3C_args. }
    rewrite hhs3C_bytes_eqb_refl. forward_if; [hhs3C_dead | ]. forward. entailer!. }
  assert (LSa: Zlength (static_public_field (r_rawa R) (mi_pub (mident_of x25519 (r_rawa R)))) = 32)
    by (rewrite <- hhs3C_setup_pub; apply IDa).
  assert (LSb: Zlength (static_public_field (r_rawb R) (mi_pub (mident_of x25519 (r_rawb R)))) = 32)
    by (rewrite <- hhs3C_setup_pub; apply IDb).
  (* m_static_public_field(tmp, &ia, raw_a) *)
  sep_apply (hhs3C_mid_join Tsh (l_ia L) (mident_of x25519 (r_rawa R)) FCia LPa LQa).
  forward_call (Tsh, l_tmp L, Tsh, l_ia L, mident_of x25519 (r_rawa R), Tsh, l_rawa L, r_rawa R).
  (* CHECK(bytes_eq(wa.static_public, tmp, 32)) *)
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  { apply ENTAIL_refl. }
  2: { forward. apply ENTAIL_refl. }
  { forward_call (Tsh, offset_val 8 (l_wa L), static_public_field (r_rawa R) (mi_pub (mident_of x25519 (r_rawa R))),
                  Tsh, l_tmp L, static_public_field (r_rawa R) (mi_pub (mident_of x25519 (r_rawa R)))).
    { rewrite LSa. hhs3C_args. }
    rewrite hhs3C_bytes_eqb_refl. forward_if; [hhs3C_dead | ]. forward. entailer!. }
  (* m_static_public_field(tmp, &ib, raw_b) *)
  sep_apply (hhs3C_hbytes_hout Tsh _ (l_tmp L) LSa).
  sep_apply (hhs3C_mid_join Tsh (l_ib L) (mident_of x25519 (r_rawb R)) FCib LPb LQb).
  forward_call (Tsh, l_tmp L, Tsh, l_ib L, mident_of x25519 (r_rawb R), Tsh, l_rawb L, r_rawb R).
  (* CHECK(bytes_eq(wb.static_public, tmp, 32)): the last statement *)
  match goal with |- semax _ ?P _ _ => apply semax_loop with (Q' := P) end.
  { forward_call (Tsh, offset_val 8 (l_wb L), static_public_field (r_rawb R) (mi_pub (mident_of x25519 (r_rawb R))),
                  Tsh, l_tmp L, static_public_field (r_rawb R) (mi_pub (mident_of x25519 (r_rawb R)))).
    { rewrite LSb. hhs3C_args. }
    rewrite hhs3C_bytes_eqb_refl. forward_if; [hhs3C_dead | ]. forward. entailer!. }
  forward.
  sep_apply (hhs3C_hbytes_hout Tsh _ (l_tmp L) LSb).
  sep_apply (hhs3C_dev_join Tsh (l_wa L) (hhs3_DA x25519 R L) lka (r_rawa R) eq_refl FCa IDa).
  sep_apply (hhs3C_dev_join Tsh (l_wb L) (hhs3_DB x25519 R L) lkb (r_rawb R) eq_refl FCb IDb).
  Exists R S a0 f0 l0.
  unfold hhs3_IA, hhs3_IB, hhs3_globs, hhs3_cnt_temps, hhs3_lvars, hhs3_p1_rest, hhs3_scr_tmp; cbn [app].
  entailer!.
Qed.

End Seg.
