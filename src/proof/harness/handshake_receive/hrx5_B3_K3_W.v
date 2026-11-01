(* law handshake_receive, phase B3, branch kind 3, segment W:
   stmt 5 (maybe mc->receiver_index = the index of an entry of itd's list, by a walk of nondet_size() steps): hrx5_K3_F -> hrx5_K3_F.
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_world.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_cut.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_model.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_spec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mspec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mci.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mcr.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_hmodel.
Require WgNoise.contracts.x_handshake_receive.
Require WgNoise.harness.x_handshake_receive.code.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_conv.
#[local] Existing Instance W_handshake_receive.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B3_defs.
Local Open Scope logic.

Require Import WgNoise.proof.harness.handshake_receive.hrx5_B3_K3_defs.

Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.protocol.prot_body3_shim_table1.

(* ---- helpers (prefix hrx5_k3w_; ports of consume_response_any's hcr5_q1a_* and hrx5_B4_C_W_* at W) ---- *)
#[local] Instance hrx5_k3w_cceN : change_composite_env Noise.CS W_handshake_receive.
Proof. make_cs_preserve Noise.CS W_handshake_receive. Defined.
#[local] Instance hrx5_k3w_cceC : change_composite_env Cookie.CS W_handshake_receive.
Proof. make_cs_preserve Cookie.CS W_handshake_receive. Defined.

Lemma hrx5_k3w_cmsg_W sh p M :
  cmsg_rep sh p M = !! cm_ok M && @data_at W_handshake_receive sh t_cmsg (cmsg_val M) p.
Proof.
  unfold cmsg_rep. f_equal.
  rewrite (@data_at_change_composite Cookie.CS W_handshake_receive hrx5_k3w_cceC sh t_cmsg
    (cmsg_val M) (cmsg_val M) (JMeq_refl _) eq_refl). reflexivity.
Qed.

Lemma hrx5_k3w_cmsg_W' sh p M : cm_ok M ->
  cmsg_rep sh p M = @data_at W_handshake_receive sh t_cmsg (cmsg_val M) p.
Proof.
  intros HM. rewrite hrx5_k3w_cmsg_W. apply pred_ext; entailer!.
Qed.

Lemma hrx5_k3w_itab_W sh (v: val) p :
  @data_at Noise.CS sh t_itab v p = @data_at W_handshake_receive sh t_itab v p.
Proof.
  rewrite (@data_at_change_composite Noise.CS W_handshake_receive hrx5_k3w_cceN sh t_itab v v (JMeq_refl _) eq_refl).
  reflexivity.
Qed.

Lemma hrx5_k3w_conv_entry sh E n h p :
  @data_at Noise.CS sh t_entry_s (entry_val E n h) p =
  @data_at W_handshake_receive sh t_entry_s (entry_val E n h) p.
Proof.
  rewrite (@data_at_change_composite Noise.CS W_handshake_receive hrx5_k3w_cceN sh t_entry_s
    (entry_val E n h) (entry_val E n h) (JMeq_refl _) eq_refl). reflexivity.
Qed.

Lemma hrx5_k3w_split {A: Type} (D: list (val * share * A)) a :
  In a (saddrs D) -> exists D1 sh E D2, D = D1 ++ (a, sh, E) :: D2.
Proof.
  unfold saddrs. rewrite in_map_iff. intros [[[x sh] E] [Hx Hin]]. simpl in Hx. subst x.
  apply in_split in Hin. destruct Hin as [l1 [l2 ->]]. eauto.
Qed.

Lemma hrx5_k3w_iter_split L D1 x D2 :
  iter_sepcon (pool_item_rep L) (D1 ++ x :: D2) =
  (pool_item_rep L x * iter_sepcon (pool_item_rep L) (D1 ++ D2))%logic.
Proof.
  rewrite !iter_sepcon_app. simpl.
  rewrite <- !sepcon_assoc, (sepcon_comm (iter_sepcon _ D1)). reflexivity.
Qed.

Lemma hrx5_k3w_valid L D a :
  In a (saddrs D) -> Forall (fun x => match x with (_, sh, _) => writable_share sh end) D ->
  iter_sepcon (pool_item_rep L) D |-- valid_pointer a.
Proof.
  intros Ha HF. destruct (hrx5_k3w_split D a Ha) as (D1 & sh & E & D2 & ->).
  rewrite hrx5_k3w_iter_split. apply sepcon_valid_pointer1.
  unfold pool_item_rep, entry_at. apply data_at_valid_ptr; [| simpl; lia].
  rewrite Forall_forall in HF. specialize (HF (a, sh, E) ltac:(apply in_or_app; right; left; reflexivity)).
  apply readable_nonidentity, writable_readable; exact HF.
Qed.

Lemma hrx5_k3w_ptrs L D : iter_sepcon (pool_item_rep L) D |-- !! Forall isptr (saddrs D).
Proof.
  induction D as [| [[a sh] E] D IH]; [simpl; entailer! |].
  change (iter_sepcon (pool_item_rep L) ((a, sh, E) :: D)) with (pool_item_rep L (a, sh, E) * iter_sepcon (pool_item_rep L) D)%logic.
  rewrite (add_andp _ _ IH). unfold pool_item_rep at 1, entry_at. unfold saddrs; cbn [map]; fold (saddrs D).
  entailer!. all: try (constructor; auto); match goal with Hf: field_compatible _ _ _ |- _ => destruct Hf; auto end.
Qed.

Lemma hrx5_k3w_focus L D e :
  In e (saddrs D) -> Forall (fun x => match x with (_, sh, _) => writable_share sh end) D ->
  exists sh E Rst, readable_share sh /\
    iter_sepcon (pool_item_rep L) D =
    (@data_at W_handshake_receive sh t_entry_s (entry_val E (succ_in L e) (vin e L)) e * Rst)%logic.
Proof.
  intros Ha HF. destruct (hrx5_k3w_split D e Ha) as (D1 & sh & E & D2 & ->).
  exists sh, E, (iter_sepcon (pool_item_rep L) (D1 ++ D2)). split.
  - rewrite Forall_forall in HF. specialize (HF (e, sh, E) ltac:(apply in_or_app; right; left; reflexivity)).
    apply writable_readable; exact HF.
  - rewrite hrx5_k3w_iter_split. unfold pool_item_rep, entry_at. rewrite hrx5_k3w_conv_entry. reflexivity.
Qed.

Lemma hrx5_k3w_succ_in L a : succ_in L a <> nullval -> In (succ_in L a) L.
Proof.
  induction L as [| x L IH]; simpl; intros H; [congruence |].
  destruct (EqDec_val x a).
  - destruct L; simpl in *; [congruence | auto].
  - right. auto.
Qed.

Lemma hrx5_k3w_succ_pn L a : (forall x, In x L -> isptr x) -> is_pointer_or_null (succ_in L a).
Proof.
  intros HL. destruct (eq_dec (succ_in L a) nullval) as [-> | Hn]; [simpl; auto |].
  specialize (HL _ (hrx5_k3w_succ_in L a Hn)). destruct (succ_in L a); try contradiction; simpl; auto.
Qed.

Lemma hrx5_k3w_ovn Q R : RA_normal (overridePost Q R) = Q.
Proof. destruct R; reflexivity. Qed.

Section K3W.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hrx5_K3_W_ok {Espec: OracleKind} gv L FR :
  hrx5_B3_lem_stmt x25519 ->
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_K3_F x25519 gv L FR) hrx5_K3_SW
    (overridePost (hrx5_K3_F x25519 gv L FR) (hrx5_RB x25519 gv L FR)).
Proof.
  intros HLEM HY. unfold hrx5_Delta, hrx5_K3_F, hrx5_K3_St.
  Intros R sec birth S w NS PS T head. Intros nk KE st i kc lul q proto. Intros ip4 ip6 port mc img M.
  unfold hrx5_K3_SW, hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr, hrx5_K3_XF; cbn [app].
  unfold hrx5_RB, hrx5_R. abbreviate_semax.
  rewrite (hrx5_k3w_cmsg_W' _ _ _ H4).
  unfold itable. Intros. rewrite hrx5_k3w_itab_W.
  match goal with Hw: itable_wf T |- _ => pose proof Hw as HW; destruct Hw as (HwL & HwI & HwD & HwS) end.
  assert_PROP (Forall isptr (saddrs (t_D T))) as Hptr. { sep_apply (hrx5_k3w_ptrs (t_L T) (t_D T)). entailer!. }
  assert (HLp: forall a, In a (t_L T) -> isptr a).
  { intros a Ha. rewrite Forall_forall in Hptr. apply Hptr, HwI, Ha. }
  forward.
  { entailer!. destruct (t_L T) as [| a0 L'] eqn:HL; simpl hd; [simpl; auto |].
    specialize (HLp a0 (or_introl eq_refl)). destruct a0; try contradiction; simpl; auto. }
  freeze FZ := - (data_at _ t_cmsg _ mc) (data_at _ t_itab _ _) (iter_sepcon _ _).
  lazymatch goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?Rs))) _ _ =>
    forward_if (EX c: bool, PROPx ((c = true -> t_L T <> []) :: P)
      (LOCALx (temp HRM._t'65 (Val.of_bool c) :: Q) (SEPx Rs))) end.
  { destruct (t_L T) as [| a0 L'] eqn:HL; simpl hd.
    { apply denote_tc_test_eq_split; auto with valid_pointer. }
    apply denote_tc_test_eq_split; [| auto with valid_pointer].
    apply sepcon_valid_pointer1, sepcon_valid_pointer2, hrx5_k3w_valid;
      [apply HwI; left; reflexivity | exact HwS]. }
  { forward_call tt. Intros b2. forward. Exists (negb (Int.eq (Int.repr (Z.land b2 1)) Int.zero)). entailer!. split.
    - intros _ HL. match goal with Hx: hd nullval (t_L T) <> nullval |- _ => rewrite HL in Hx; simpl in Hx; congruence end.
    - destruct (Int.eq _ _); reflexivity. }
  { forward. Exists false. entailer!. }
  Intros c.
  forward_if.
  2:{ forward.
      Exists R sec birth S w NS PS T. Exists head nk KE st i kc lul q. Exists proto ip4 ip6 port mc img M.
      thaw FZ. unfold itable. rewrite hrx5_k3w_itab_W, (hrx5_k3w_cmsg_W' _ _ _ H4). entailer!. }
  match goal with Hc: c = true -> t_L T <> [], Ht: typed_true _ (if c then _ else _) |- _ =>
    assert (HL0: t_L T <> []) by (apply Hc; destruct c; [reflexivity | inv Ht]); clear Hc Ht end.
  forward_call tt. Intros k0. forward.
  lazymatch goal with |- semax _ (PROPx ?P (LOCALx (_ :: _ :: ?Q) (SEPx ?Rs))) _ _ =>
  forward_loop (EX e: val, EX k: Z, PROPx (In e (t_L T) :: (0 <= k <= Int64.max_unsigned) :: P)
       (LOCALx (temp HRM._e e :: temp HRM._k (Vlong (Int64.repr k)) :: Q) (SEPx Rs)))
    continue: (EX e: val, EX k: Z, PROPx (In e (t_L T) :: (succ_in (t_L T) e <> nullval) :: (0 <= k <= Int64.max_unsigned) :: P)
       (LOCALx (temp HRM._e e :: temp HRM._k (Vlong (Int64.repr k)) :: Q) (SEPx Rs)))
    break: (EX e: val, PROPx (In e (t_L T) :: P) (LOCALx (temp HRM._e e :: Q) (SEPx Rs))) end.
  { Exists (hd nullval (t_L T)) k0. entailer!. destruct (t_L T) as [| a0 L'] eqn:HL; [congruence |]. left; reflexivity. }
  { Intros e k.
    match goal with He: In e (t_L T) |- _ => rename He into Hin end.
    destruct (hrx5_k3w_focus (t_L T) (t_D T) e (HwI _ Hin) HwS) as (sh & E & Rst & Hrd & Heq).
    rewrite Heq. Intros. forward.
    { entailer!. unfold entry_val. apply hrx5_k3w_succ_pn; auto. }
    change (let (x, _) := let (_, y) := entry_val E (succ_in (t_L T) e) (vin e (t_L T)) in y in x) with (succ_in (t_L T) e).
    gather_SEP (data_at sh t_entry_s _ e) Rst. rewrite <- Heq.
    lazymatch goal with |- semax _ (PROPx ?P (LOCALx (_ :: ?Q) (SEPx ?Rs))) _ _ =>
      forward_if (PROPx P (LOCALx (temp HRM._t'64 (Val.of_bool (if eq_dec (succ_in (t_L T) e) nullval then false else Z.gtb k 0)) :: Q) (SEPx Rs))) end.
    { apply denote_tc_test_eq_split; [| auto with valid_pointer].
      destruct (eq_dec (succ_in (t_L T) e) nullval) as [-> | Hn]; [auto with valid_pointer |].
      do 3 apply sepcon_valid_pointer1. apply hrx5_k3w_valid; [apply HwI, hrx5_k3w_succ_in, Hn | exact HwS]. }
    { forward. entailer!. destruct (eq_dec (succ_in (t_L T) e) nullval); [contradiction |].
      match goal with Hk: 0 <= k <= Int64.max_unsigned |- _ => clear - Hk end.
      unfold Int64.cmpu, Int64.ltu. rewrite !Int64.unsigned_repr by rep_lia.
      destruct (Z.gtb_spec k 0), (zlt 0 k); try lia; reflexivity. }
    { forward. entailer!. match goal with Hn: succ_in (t_L T) e = nullval |- _ => rewrite Hn end.
      destruct (eq_dec nullval nullval); [reflexivity | congruence]. }
    forward_if.
    { match goal with Ht: typed_true _ _ |- _ => rename Ht into Ht8 end.
      destruct (EqDec_val (succ_in (t_L T) e) nullval) as [Hn | Hn]; [inv Ht8 |].
      destruct (Z.gtb_spec k 0) as [Hk | Hk]; [| inv Ht8].
      forward. Exists e (k - 1). entailer!. }
    { forward. Exists e. entailer!. } }
  { Intros e k.
    match goal with He: In e (t_L T) |- _ => rename He into Hin end.
    destruct (hrx5_k3w_focus (t_L T) (t_D T) e (HwI _ Hin) HwS) as (sh & E & Rst & Hrd & Heq).
    rewrite Heq. Intros. forward.
    { entailer!. unfold entry_val. apply hrx5_k3w_succ_pn; auto. }
    gather_SEP (data_at sh t_entry_s _ e) Rst. rewrite <- Heq.
    Exists (succ_in (t_L T) e) k. entailer!. apply hrx5_k3w_succ_in; auto. }
  Intros e.
  match goal with He: In e (t_L T) |- _ => rename He into Hin end.
  destruct (hrx5_k3w_focus (t_L T) (t_D T) e (HwI _ Hin) HwS) as (sh & E & Rst & Hrd & Heq).
  rewrite Heq. Intros. forward. forward.
  gather_SEP (data_at sh t_entry_s _ e) Rst. rewrite <- Heq.
  set (M1 := mkCM (cm_type M) (e_index E) (cm_nonce M) (cm_enc M)).
  match goal with |- context [data_at Ews t_cmsg ?v mc] => change v with (cmsg_val M1) end.
  assert (HM1: cm_ok M1) by exact H4.
  Exists R sec birth S w NS PS T. Exists head nk KE st i kc lul q. Exists proto ip4 ip6 port mc img M1.
  thaw FZ. unfold itable. rewrite hrx5_k3w_itab_W, (hrx5_k3w_cmsg_W' _ _ _ HM1). entailer!.
Qed.

End K3W.
