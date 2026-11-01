(* law handshake_receive, B4 segment R, part N: the node walk nd = peers; for (; nd; nd = nd->next) if (&nd->p->handshake.entry == e) target = nd. *)
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
#[local] Existing Instance W_handshake_receive.
#[local] Existing Instance W_handshake_receive.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_R_pure.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_R_sep.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_R_pure.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_R_sep.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_R_defs.
Local Open Scope logic.

Module hrx5_B4_R_Nm.
Section N.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Local Notation D4 := (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec).

Definition hrx5_B4_R_NI gv L nk KE st i S lul m img n tw T (F: mpred) (NSs: list hnode4) (a: val) (NS1 NS2: list hnode4) : environ -> mpred :=
  PROPx [NSs = NS1 ++ NS2]
  (LOCALx (temp HM._nd (hrx5_head NS2) :: temp HM._target (hrx5_B4_R_lm NS1 a) :: temp HM._e a :: temp HM._acc_resp (Vint Int.zero) ::
           hrx5_B4_R_Q gv L nk KE st i S lul m img n tw)
  (SEPx [hnodes_rep4 W (hrx5_head NSs) NSs; iter_sepcon (pool_item_rep (t_L T)) (t_D T); F])).
Definition hrx5_B4_R_NC gv L nk KE st i S lul m img n tw T (F: mpred) (NSs: list hnode4) (a: val) (NS1: list hnode4) (N: hnode4)
  (NS2: list hnode4) : environ -> mpred :=
  PROPx [NSs = NS1 ++ N :: NS2]
  (LOCALx (temp HM._nd (hn_addr N) :: temp HM._target (hrx5_B4_R_lm (NS1 ++ [N]) a) :: temp HM._e a ::
           temp HM._acc_resp (Vint Int.zero) :: hrx5_B4_R_Q gv L nk KE st i S lul m img n tw)
  (SEPx [hnodes_rep4 W (hrx5_head NSs) NSs; iter_sepcon (pool_item_rep (t_L T)) (t_D T); F])).
Definition hrx5_B4_R_NB gv L nk KE st i S lul m img n tw T (F: mpred) (NSs: list hnode4) (a: val) : environ -> mpred :=
  PROPx []
  (LOCALx (temp HM._nd nullval :: temp HM._target (hrx5_B4_R_lm NSs a) :: temp HM._e a :: temp HM._acc_resp (Vint Int.zero) ::
           hrx5_B4_R_Q gv L nk KE st i S lul m img n tw)
  (SEPx [hnodes_rep4 W (hrx5_head NSs) NSs; iter_sepcon (pool_item_rep (t_L T)) (t_D T); F])).
Definition hrx5_B4_R_NIx gv L nk KE st i S lul m img n tw T (F: mpred) (NSs: list hnode4) (a: val) : environ -> mpred :=
  EX NS1: list hnode4, EX NS2: list hnode4, hrx5_B4_R_NI gv L nk KE st i S lul m img n tw T F NSs a NS1 NS2.
Definition hrx5_B4_R_NCx gv L nk KE st i S lul m img n tw T (F: mpred) (NSs: list hnode4) (a: val) : environ -> mpred :=
  EX NS1: list hnode4, EX N: hnode4, EX NS2: list hnode4, hrx5_B4_R_NC gv L nk KE st i S lul m img n tw T F NSs a NS1 N NS2.

Lemma hrx5_B4_R_Nb_nil {Espec: OracleKind} gv L nk KE st i S lul m img n tw T F NSs a NS1 Rr :
  semax D4 (hrx5_B4_R_NI gv L nk KE st i S lul m img n tw T F NSs a NS1 []) hrx5_B4_R_B2
    (loop1_ret_assert (hrx5_B4_R_NCx gv L nk KE st i S lul m img n tw T F NSs a) (overridePost (hrx5_B4_R_NB gv L nk KE st i S lul m img n tw T F NSs a) Rr)).
Proof.
  destruct Rr as [Rn Rb Rc Rret]. cbn [overridePost loop1_ret_assert].
  unfold hrx5_B4_R_NI, hrx5_B4_R_Q, hrx5_ltemps, hrx5_lvars, hrx5_Delta, hrx5_B4_R_B2. cbn [app hrx5_head]. simplify_func_tycontext.
  Intros.
  forward_if.
  - exfalso. match goal with Hc: isptr (Vlong _) |- _ => exact Hc end.
  - forward. unfold hrx5_B4_R_NB, hrx5_B4_R_Q, hrx5_ltemps, hrx5_lvars. cbn [app].
    match goal with Hl: NSs = NS1 ++ [] |- _ => rewrite app_nil_r in Hl; rewrite <- Hl end.
    entailer!.
Qed.

Lemma hrx5_B4_R_Nb_cons {Espec: OracleKind} gv L nk KE st i S lul m img n tw T F NSs a NS1 N NS2 Rr :
  Forall (fun x => match x with (_, sh, _) => writable_share sh end) (t_D T) ->
  In a (saddrs (t_D T)) -> Forall isptr (map hn_addr NSs) ->
  (forall q, In q (map hn_p NSs) -> @field_compatible W t_peer [] q /\ In (hs_addr q) (saddrs (t_D T))) ->
  semax D4 (hrx5_B4_R_NI gv L nk KE st i S lul m img n tw T F NSs a NS1 (N :: NS2)) hrx5_B4_R_B2
    (loop1_ret_assert (hrx5_B4_R_NCx gv L nk KE st i S lul m img n tw T F NSs a) (overridePost (hrx5_B4_R_NB gv L nk KE st i S lul m img n tw T F NSs a) Rr)).
Proof.
  intros Hwr Ha HptrN HfcP.
  destruct hrx5_B4_R_sep_ok as (Snode & _ & Svalid & _).
  destruct Rr as [Rn Rb Rc Rret]. cbn [overridePost loop1_ret_assert].
  unfold hrx5_B4_R_NI, hrx5_B4_R_Q, hrx5_ltemps, hrx5_lvars, hrx5_Delta, hrx5_B4_R_B2. cbn [app hrx5_head]. simplify_func_tycontext.
  Intros. match goal with Hl: NSs = NS1 ++ N :: NS2 |- _ => rename Hl into HNS end.
  assert (HinN: In (hn_addr N) (map hn_addr NSs)).
  { rewrite HNS, map_app. apply in_or_app. right. left. reflexivity. }
  assert (HpN: isptr (hn_addr N)) by (rewrite Forall_forall in HptrN; auto).
  forward_if.
  2: { exfalso. match goal with Hc: _ = nullval |- _ => change (hn_addr N = nullval) in Hc; rewrite Hc in HpN; exact HpN end. }
  assert (Hnode: hnodes_rep4 W (hrx5_head NSs) NSs |--
    (@data_at W Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, hrx5_head NS2)))) (hn_addr N) *
     (@data_at W Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, hrx5_head NS2)))) (hn_addr N) -*
      hnodes_rep4 W (hrx5_head NSs) NSs))%logic).
  { rewrite HNS. apply Snode. }
  assert (HinPN: In (hn_p N) (map hn_p NSs)).
  { rewrite HNS, map_app. apply in_or_app. right. left. reflexivity. }
  destruct (HfcP _ HinPN) as [HfcN HpoolN].
  assert (HpPN: isptr (hn_p N)) by (destruct HfcN as [? _]; assumption).
  sep_apply Hnode. Intros.
  forward.
  lazymatch goal with |- semax _ (PROPx ?P (LOCALx (_ :: _ :: _ :: ?Q) (SEPx ?Rs))) _ _ =>
    forward_if (PROPx P (LOCALx (temp HM._nd (hn_addr N) :: temp HM._target (hrx5_B4_R_lm (NS1 ++ [N]) a) :: Q) (SEPx Rs))) end.
  { apply denote_tc_test_eq_split; hrx5_B4_R_vp. }
  { match goal with Hc: offset_val 0 (offset_val 48 (hn_p N)) = a |- _ =>
      rewrite hrx5_B4_R_off48 in Hc by exact HpPN; rename Hc into Heqa end.
    forward. entailer!. rewrite hrx5_B4_R_lm_snoc.
    match goal with |- context [eq_dec ?x ?y] => destruct (eq_dec x y) end; [reflexivity | congruence]. }
  { match goal with Hc: offset_val 0 (offset_val 48 (hn_p N)) <> a |- _ =>
      rewrite hrx5_B4_R_off48 in Hc by exact HpPN; rename Hc into Hnea end.
    forward. entailer!. rewrite hrx5_B4_R_lm_snoc.
    match goal with |- context [eq_dec ?x ?y] => destruct (eq_dec x y) end; [contradiction | reflexivity]. }
  sep_apply (hrx5_B4_R_wand1 (@data_at W Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, hrx5_head NS2)))) (hn_addr N))
               (hnodes_rep4 W (hrx5_head NSs) NSs)).
  unfold hrx5_B4_R_NCx, hrx5_B4_R_NC, hrx5_B4_R_Q, hrx5_ltemps, hrx5_lvars. cbn [app].
  Exists NS1 N NS2. entailer!.
Qed.

Lemma hrx5_B4_R_Ni {Espec: OracleKind} gv L nk KE st i S lul m img n tw T F NSs a NS1 N NS2 Rr :
  Forall isptr (map hn_addr NSs) ->
  semax D4 (hrx5_B4_R_NC gv L nk KE st i S lul m img n tw T F NSs a NS1 N NS2) hrx5_B4_R_I2
    (loop2_ret_assert (hrx5_B4_R_NIx gv L nk KE st i S lul m img n tw T F NSs a) (overridePost (hrx5_B4_R_NB gv L nk KE st i S lul m img n tw T F NSs a) Rr)).
Proof.
  intros HptrN.
  destruct hrx5_B4_R_sep_ok as (Snode & _).
  destruct Rr as [Rn Rb Rc Rret]. cbn [overridePost loop2_ret_assert].
  unfold hrx5_B4_R_NC, hrx5_B4_R_Q, hrx5_ltemps, hrx5_lvars, hrx5_Delta, hrx5_B4_R_I2. cbn [app]. simplify_func_tycontext.
  Intros. match goal with Hl: NSs = NS1 ++ N :: NS2 |- _ => rename Hl into HNS end.
  assert (Hnode: hnodes_rep4 W (hrx5_head NSs) NSs |--
    (@data_at W Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, hrx5_head NS2)))) (hn_addr N) *
     (@data_at W Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, hrx5_head NS2)))) (hn_addr N) -*
      hnodes_rep4 W (hrx5_head NSs) NSs))%logic).
  { rewrite HNS. apply Snode. }
  assert (HnxP: is_pointer_or_null (hrx5_head NS2)).
  { destruct NS2 as [| N2 NS2]; simpl; auto.
    assert (Hin2: In (hn_addr N2) (map hn_addr NSs)).
    { rewrite HNS, map_app. apply in_or_app. right. right. left. reflexivity. }
    rewrite Forall_forall in HptrN. specialize (HptrN _ Hin2). destruct (hn_addr N2); try contradiction; simpl; auto. }
  sep_apply Hnode. Intros.
  forward.
  sep_apply (hrx5_B4_R_wand1 (@data_at W Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, hrx5_head NS2)))) (hn_addr N))
               (hnodes_rep4 W (hrx5_head NSs) NSs)).
  unfold hrx5_B4_R_NIx, hrx5_B4_R_NI, hrx5_B4_R_Q, hrx5_ltemps, hrx5_lvars. cbn [app].
  Exists (NS1 ++ [N]) NS2. entailer!. try subst NSs. rewrite <- app_assoc. reflexivity.
Qed.

Lemma hrx5_B4_R_Nloop {Espec: OracleKind} gv L nk KE st i S lul m img n tw T F NSs a Rr :
  Forall (fun x => match x with (_, sh, _) => writable_share sh end) (t_D T) ->
  In a (saddrs (t_D T)) -> Forall isptr (map hn_addr NSs) ->
  (forall q, In q (map hn_p NSs) -> @field_compatible W t_peer [] q /\ In (hs_addr q) (saddrs (t_D T))) ->
  semax D4 (hrx5_B4_R_NI gv L nk KE st i S lul m img n tw T F NSs a [] NSs) (Sloop hrx5_B4_R_B2 hrx5_B4_R_I2)
    (overridePost (hrx5_B4_R_NB gv L nk KE st i S lul m img n tw T F NSs a) Rr).
Proof.
  intros Hwr Ha HptrN HfcP.
  eapply semax_pre with (P' := hrx5_B4_R_NIx gv L nk KE st i S lul m img n tw T F NSs a).
  { unfold hrx5_B4_R_NIx. apply andp_left2. Exists (@nil hnode4) NSs. apply derives_refl. }
  apply semax_loop with (Q' := hrx5_B4_R_NCx gv L nk KE st i S lul m img n tw T F NSs a).
  - unfold hrx5_B4_R_NIx at 1. apply semax_extract_exists; intro NS1. apply semax_extract_exists; intro NS2.
    destruct NS2 as [| N NS2]; [apply hrx5_B4_R_Nb_nil | apply hrx5_B4_R_Nb_cons; assumption].
  - unfold hrx5_B4_R_NCx at 1. apply semax_extract_exists; intro NS1. apply semax_extract_exists; intro N.
    apply semax_extract_exists; intro NS2. apply hrx5_B4_R_Ni; assumption.
Qed.

(* it = peers; the node walk *)
Lemma hrx5_B4_R_Lnode {Espec: OracleKind} gv L nk KE st i S lul m img n tw IA NS NSs T M FX a Rr :
  hrx5_head NSs = hrx5_head NS -> In a (saddrs (t_D T)) ->
  (forall q, In q (map hn_p NSs) -> @field_compatible W t_peer [] q /\ In (hs_addr q) (saddrs (t_D T))) ->
  semax D4 (hrx5_B4_R_A3 gv L nk KE st i S lul m img n tw IA NS NSs T M FX a)
    (Ssequence hrx5_B4_R_sit (Sloop hrx5_B4_R_B2 hrx5_B4_R_I2))
    (overridePost (hrx5_B4_R_A4 gv L nk KE st i S lul m img n tw IA NS NSs T M FX a (hrx5_B4_R_lm NSs a)) Rr).
Proof.
  intros HsH Ha HfcP.
  destruct hrx5_B4_R_sep_ok as (_ & _ & _ & Sptrs & _).
  unfold hrx5_B4_R_A3, hrx5_B4_R_R, hrx5_B4_R_Q, hrx5_ltemps, hrx5_Delta, hrx5_B4_R_sit.
  simplify_func_tycontext. unfold hrx5_lvars; cbn [app].
  unfold itable. Intros.
  match goal with Hw: itable_wf T |- _ => pose proof Hw as Hwf; destruct Hw as (HwL & HwI & HwD & HwS) end.
  assert_PROP (Forall isptr (map hn_addr NSs)) as HptrN.
  { sep_apply (Sptrs (hrx5_head NS) NSs). entailer!. }
  forward.
  rewrite <- HsH.
  freeze FZ := - (hnodes_rep4 _ _ _) (iter_sepcon _ _).
  eapply semax_pre; [| eapply hrx5_B4_R_post; [| apply (hrx5_B4_R_Nloop gv L nk KE st i S lul m img n tw T (FRZL FZ) NSs a); assumption]].
  - unfold hrx5_B4_R_NI, hrx5_B4_R_Q, hrx5_ltemps, hrx5_lvars; cbn [app]. entailer!.
  - unfold hrx5_B4_R_NB, hrx5_B4_R_A4, hrx5_B4_R_R, hrx5_B4_R_Q, hrx5_ltemps, hrx5_lvars; cbn [app].
    thaw FZ. rewrite HsH. unfold itable. entailer!.
Qed.

End N.
End hrx5_B4_R_Nm.

Lemma hrx5_B4_R_N_ok : hrx5_B4_R_N_stmt.
Proof.
  unfold hrx5_B4_R_N_stmt. intros. eapply hrx5_B4_R_Nm.hrx5_B4_R_Lnode; eassumption.
Qed.
