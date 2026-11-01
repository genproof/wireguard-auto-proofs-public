(* law consume_response_any, phase Q1a: statements 0..2 of P6's then-branch: fill_resp(msg); mode = nondet_u8() % 3; the mode-0 block (the receiver index of a table entry).
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_cut.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_model.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_spec.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_defs.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_conv.
Require WgNoise.harness.x_consume_response_any.code.

#[local] Existing Instance W_consume_response_any.
Local Open Scope logic.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* Helpers: compspecs conversions, an entry of the pool                    *)
(* ---------------------------------------------------------------------- *)

#[local] Instance hcr5_q1a_cce_N : change_composite_env Noise.CS W_consume_response_any.
Proof. make_cs_preserve Noise.CS W_consume_response_any. Defined.

Lemma hcr5_q1a_conv_itab sh (v: val) p :
  @data_at Noise.CS sh t_itab v p = @data_at W_consume_response_any sh t_itab v p.
Proof. rewrite (@data_at_change_composite Noise.CS W_consume_response_any _ sh t_itab v v (JMeq_refl v)); [reflexivity | prove_cs_preserve_type]. Qed.

Lemma hcr5_q1a_conv_entry sh E n h p :
  @data_at Noise.CS sh t_entry_s (entry_val E n h) p =
  @data_at W_consume_response_any sh t_entry_s (entry_val E n h) p.
Proof.
  rewrite (@data_at_change_composite Noise.CS W_consume_response_any _ sh t_entry_s (entry_val E n h) (entry_val E n h) (JMeq_refl _));
    [reflexivity | prove_cs_preserve_type].
Qed.

Lemma hcr5_q1a_conv_resp sh M p :
  @data_at Noise.CS sh t_resp (resp_val M) p =
  @data_at W_consume_response_any sh t_resp (resp_val M) p.
Proof.
  rewrite (@data_at_change_composite Noise.CS W_consume_response_any _ sh t_resp (resp_val M) (resp_val M) (JMeq_refl _));
    [reflexivity | prove_cs_preserve_type].
Qed.

Lemma hcr5_q1a_split {A: Type} (D: list (val * share * A)) a :
  In a (saddrs D) -> exists D1 sh E D2, D = D1 ++ (a, sh, E) :: D2.
Proof.
  unfold saddrs. rewrite in_map_iff. intros [[[x sh] E] [Hx Hin]]. simpl in Hx. subst x.
  apply in_split in Hin. destruct Hin as [l1 [l2 ->]]. eauto.
Qed.

Lemma hcr5_q1a_iter_split L D1 x D2 :
  iter_sepcon (pool_item_rep L) (D1 ++ x :: D2) =
  (pool_item_rep L x * iter_sepcon (pool_item_rep L) (D1 ++ D2))%logic.
Proof.
  rewrite !iter_sepcon_app. simpl.
  rewrite <- !sepcon_assoc, (sepcon_comm (iter_sepcon _ D1)). reflexivity.
Qed.

Lemma hcr5_q1a_valid L D a :
  In a (saddrs D) -> Forall (fun x => match x with (_, sh, _) => writable_share sh end) D ->
  iter_sepcon (pool_item_rep L) D |-- valid_pointer a.
Proof.
  intros Ha HF. destruct (hcr5_q1a_split D a Ha) as (D1 & sh & E & D2 & ->).
  rewrite hcr5_q1a_iter_split. apply sepcon_valid_pointer1.
  unfold pool_item_rep, entry_at. apply data_at_valid_ptr; [| simpl; lia].
  rewrite Forall_forall in HF. specialize (HF (a, sh, E) ltac:(apply in_or_app; right; left; reflexivity)).
  apply readable_nonidentity, writable_readable; exact HF.
Qed.

Lemma hcr5_q1a_isptr L D a :
  In a (saddrs D) -> iter_sepcon (pool_item_rep L) D |-- !! isptr a.
Proof.
  intros Ha. destruct (hcr5_q1a_split D a Ha) as (D1 & sh & E & D2 & ->).
  rewrite hcr5_q1a_iter_split. unfold pool_item_rep, entry_at. entailer!. destruct H; auto.
Qed.

Lemma hcr5_q1a_ptrs L D : iter_sepcon (pool_item_rep L) D |-- !! Forall isptr (saddrs D).
Proof.
  induction D as [| [[a sh] E] D IH]; [simpl; entailer! |].
  change (iter_sepcon (pool_item_rep L) ((a, sh, E) :: D)) with (pool_item_rep L (a, sh, E) * iter_sepcon (pool_item_rep L) D)%logic.
  rewrite (add_andp _ _ IH). unfold pool_item_rep at 1, entry_at. unfold saddrs; cbn [map]; fold (saddrs D).
  entailer!. all: try (constructor; auto); match goal with Hf: field_compatible _ _ _ |- _ => destruct Hf; auto end.
Qed.

Lemma hcr5_q1a_focus L D e :
  In e (saddrs D) -> Forall (fun x => match x with (_, sh, _) => writable_share sh end) D ->
  exists sh E Rst, readable_share sh /\
    iter_sepcon (pool_item_rep L) D =
    (@data_at W_consume_response_any sh t_entry_s (entry_val E (succ_in L e) (vin e L)) e * Rst)%logic.
Proof.
  intros Ha HF. destruct (hcr5_q1a_split D e Ha) as (D1 & sh & E & D2 & ->).
  exists sh, E, (iter_sepcon (pool_item_rep L) (D1 ++ D2)). split.
  - rewrite Forall_forall in HF. specialize (HF (e, sh, E) ltac:(apply in_or_app; right; left; reflexivity)).
    apply writable_readable; exact HF.
  - rewrite hcr5_q1a_iter_split. unfold pool_item_rep, entry_at. rewrite hcr5_q1a_conv_entry. reflexivity.
Qed.

Lemma hcr5_q1a_succ_in L a : succ_in L a <> nullval -> In (succ_in L a) L.
Proof.
  induction L as [| x L IH]; simpl; intros H; [congruence |].
  destruct (EqDec_val x a).
  - destruct L; simpl in *; [congruence | auto].
  - right. auto.
Qed.

Lemma hcr5_q1a_succ_pn L a : (forall x, In x L -> isptr x) -> is_pointer_or_null (succ_in L a).
Proof.
  intros HL. destruct (eq_dec (succ_in L a) nullval) as [-> | Hn]; [simpl; auto |].
  specialize (HL _ (hcr5_q1a_succ_in L a Hn)). destruct (succ_in L a); try contradiction; simpl; auto.
Qed.

Lemma hcr5_q1a_entry_next E n h :
  (let (x, _) := let (_, y) := entry_val E n h in y in x) = n.
Proof. reflexivity. Qed.

Section Phase.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hcr5_Q1a_ok {Espec: OracleKind} gv L FR :
  hcr5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec -> 
  semax (hcr5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hcr5_S5n x25519 gv L FR) hcr5_Q1a
    (overridePost (hcr5_SQ1a x25519 gv L FR) (hcr5_R gv)).
Proof.
  intros HH. unfold hcr5_S5n, hcr5_Delta, hcr5_R, hcr5_Q1a. simplify_func_tycontext. abbreviate_semax.
  Intros R S NS PS head nb T KE m.
  unfold hcr5_lvars, hcr5_scr, hcr5_snaps0, hcr5_world, hcr5_globs; cbn [app].
  forward_call (Ews, m). Intros M0. forward_call tt. Intros b.
  forward; [entailer!; match goal with Hc: _ /\ Int.repr 3 = Int.mone |- _ => destruct Hc as [_ Hc];
    apply (f_equal Int.signed) in Hc; rewrite Int.signed_repr in Hc by rep_lia; rewrite Int.signed_mone in Hc; lia end |].
  assert (Hmode: Int.mods (Int.repr b) (Int.repr 3) = Int.repr (b mod 3)).
  { unfold Int.mods. rewrite !Int.signed_repr by rep_lia. rewrite Z.rem_mod_nonneg by lia. reflexivity. }
  rewrite Hmode. set (mode := b mod 3).
  assert (Hm: 0 <= mode < 3) by (subst mode; apply Z.mod_pos_bound; lia). clearbody mode. clear Hmode.
  unfold itable, resp_rep. Intros. rewrite hcr5_q1a_conv_itab, hcr5_q1a_conv_resp.
  destruct H5 as (HwL & HwI & HwD & HwS).
  assert_PROP (Forall isptr (saddrs (t_D T))) as Hptr. { sep_apply (hcr5_q1a_ptrs (t_L T) (t_D T)). entailer!. }
  assert (HLp: forall a, In a (t_L T) -> isptr a).
  { intros a Ha. rewrite Forall_forall in Hptr. apply Hptr, HwI, Ha. }
  freeze FZ := - (data_at _ t_resp _ m) (data_at _ t_itab _ _) (iter_sepcon _ _).
  lazymatch goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?Rs))) _ _ =>
    forward_if (PROPx P (LOCALx (temp HR5._t'10 (Val.of_bool (Z.eqb mode 0 &&
      match t_L T with [] => false | _ => true end)) :: Q) (SEPx Rs))) end.
  { forward.
    { destruct (t_L T) as [| a0 L'] eqn:HL; simpl hd; entailer!.
      specialize (HLp a0 (or_introl eq_refl)). destruct a0; try contradiction; simpl; auto. }
    destruct (t_L T) as [| a0 L'] eqn:HL; simpl hd.
    - forward. entailer!.
    - forward.
      + entailer!. apply denote_tc_test_eq_split; [| auto with valid_pointer].
        apply sepcon_valid_pointer2; apply hcr5_q1a_valid; [apply HwI; left; reflexivity | exact HwS].
      + entailer!. specialize (HLp a0 (or_introl eq_refl)). destruct a0; try contradiction; reflexivity. }
  { forward. entailer!. destruct (Z.eqb_spec mode 0); [contradiction | reflexivity]. }
  lazymatch goal with |- semax _ (PROPx ?P (LOCALx (_ :: ?Q) (SEPx ?Rs))) _ _ =>
    forward_if (EX c: bool, PROPx ((c = true -> t_L T <> []) :: P)
      (LOCALx (temp HR5._t'11 (Val.of_bool c) :: Q) (SEPx Rs))) end.
  { forward_call tt. Intros b2. forward. Exists (negb (Int.eq (Int.repr (Z.land b2 1)) Int.zero)). entailer!. split.
    - intros _ HL. rewrite HL, andb_false_r in H5. inv H5.
    - destruct (Int.eq _ _); reflexivity. }
  { forward. Exists false. entailer!. }
  Intros c.
  forward_if.
  2:{ forward. thaw FZ. rewrite <- hcr5_q1a_conv_resp, <- hcr5_q1a_conv_itab. unfold hcr5_SQ1a.
      Exists R S NS PS head nb T KE m M0 mode.
      unfold hcr5_lvars, hcr5_scr, hcr5_snaps0, hcr5_world, hcr5_globs, itable, resp_rep; cbn [app]. entailer!.
      split; [| split; [| split]]; assumption. }
  assert (HL0: t_L T <> []) by (apply H5; destruct c; [reflexivity | inv H6]).
  clear H5 H6.
  forward_call tt. Intros k0. forward.
  { entailer!. destruct (t_L T) as [| a0 L'] eqn:HL; [congruence |]. simpl.
    specialize (HLp a0 (or_introl eq_refl)). destruct a0; try contradiction; simpl; auto. }
  lazymatch goal with |- semax _ (PROPx ?P (LOCALx (_ :: _ :: ?Q) (SEPx ?Rs))) _ _ =>
  forward_loop (EX e: val, EX k: Z, PROPx (In e (t_L T) :: (0 <= k <= Int64.max_unsigned) :: P)
       (LOCALx (temp HR5._e e :: temp HR5._k (Vlong (Int64.repr k)) :: Q) (SEPx Rs)))
    continue: (EX e: val, EX k: Z, PROPx (In e (t_L T) :: (succ_in (t_L T) e <> nullval) :: (0 <= k <= Int64.max_unsigned) :: P)
       (LOCALx (temp HR5._e e :: temp HR5._k (Vlong (Int64.repr k)) :: Q) (SEPx Rs)))
    break: (EX e: val, PROPx (In e (t_L T) :: P) (LOCALx (temp HR5._e e :: Q) (SEPx Rs))) end.
  { Exists (hd nullval (t_L T)) k0. entailer!. destruct (t_L T) as [| a0 L'] eqn:HL; [congruence |]. left; reflexivity. }
  { Intros e k.
    destruct (hcr5_q1a_focus (t_L T) (t_D T) e (HwI _ H6) HwS) as (sh & E & Rst & Hrd & Heq).
    rewrite Heq. Intros. forward.
    { entailer!. unfold entry_val. apply hcr5_q1a_succ_pn; auto. }
    change (let (x, _) := let (_, y) := entry_val E (succ_in (t_L T) e) (vin e (t_L T)) in y in x) with (succ_in (t_L T) e).
    gather_SEP (data_at sh t_entry_s _ e) Rst. rewrite <- Heq.
    lazymatch goal with |- semax _ (PROPx ?P (LOCALx (_ :: ?Q) (SEPx ?Rs))) _ _ =>
      forward_if (PROPx P (LOCALx (temp HR5._t'9 (Val.of_bool (if eq_dec (succ_in (t_L T) e) nullval then false else Z.gtb k 0)) :: Q) (SEPx Rs))) end.
    { apply denote_tc_test_eq_split; [| auto with valid_pointer].
      destruct (eq_dec (succ_in (t_L T) e) nullval) as [-> | Hn]; [auto with valid_pointer |].
      do 3 apply sepcon_valid_pointer1. apply hcr5_q1a_valid; [apply HwI, hcr5_q1a_succ_in, Hn | exact HwS]. }
    { forward. entailer!. destruct (eq_dec (succ_in (t_L T) e) nullval); [contradiction |]. clear - H7.
      unfold Int64.cmpu, Int64.ltu. rewrite !Int64.unsigned_repr by rep_lia.
      destruct (Z.gtb_spec k 0), (zlt 0 k); try lia; reflexivity. }
    { forward. entailer!. rewrite H8. destruct (eq_dec nullval nullval); [reflexivity | congruence]. }
    forward_if.
    { destruct (EqDec_val (succ_in (t_L T) e) nullval) as [Hn | Hn]; [inv H8 |].
      destruct (Z.gtb_spec k 0) as [Hk | Hk]; [| inv H8].
      forward. Exists e (k - 1). entailer!. }
    { forward. Exists e. entailer!. } }
  { Intros e k.
    destruct (hcr5_q1a_focus (t_L T) (t_D T) e (HwI _ H6) HwS) as (sh & E & Rst & Hrd & Heq).
    rewrite Heq. Intros. forward.
    { entailer!. unfold entry_val. apply hcr5_q1a_succ_pn; auto. }
    gather_SEP (data_at sh t_entry_s _ e) Rst. rewrite <- Heq.
    Exists (succ_in (t_L T) e) k. entailer!. apply hcr5_q1a_succ_in; auto. }
  Intros e.
  destruct (hcr5_q1a_focus (t_L T) (t_D T) e (HwI _ H6) HwS) as (sh & E & Rst & Hrd & Heq).
  rewrite Heq. Intros. forward. forward.
  gather_SEP (data_at sh t_entry_s _ e) Rst. rewrite <- Heq.
  set (M1 := mkRM (rm_type M0) (rm_sender M0) (e_index E) (rm_eph M0) (rm_encn M0) (rm_mac1 M0) (rm_mac2 M0)).
  match goal with |- context [data_at Ews t_resp ?v m] => change v with (resp_val M1) end.
  assert (HM1: rm_ok M1) by exact H3.
  thaw FZ. rewrite <- hcr5_q1a_conv_resp, <- hcr5_q1a_conv_itab. unfold hcr5_SQ1a.
  Exists R S NS PS head nb T KE m M1 mode.
  unfold hcr5_lvars, hcr5_scr, hcr5_snaps0, hcr5_world, hcr5_globs, itable, resp_rep; cbn [app]. entailer!.
  split; [| split; [| split]]; assumption.
Qed.

End Phase.
