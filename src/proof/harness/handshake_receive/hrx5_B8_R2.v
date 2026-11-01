(* law handshake_receive: phase B8, branch R
   of statement 41, corrected statement: hrx5_B8_R_stmt (hrx5_B8_defs.v) is unprovable as stated (the
   table before the packet may have a duplicate list entry: itable_wf T is lost at dispatch); hrx5_B8_R2_stmt adds
   `itable_wf T` after the case hypothesis.  The cut: hrx5_B8_R_defs.v; the segments hrx5_B8_R_{P,I,A,B,D,E}.v. *)
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_ilem.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_P.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_I.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_A.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_B.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_D.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_E.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

(* the case analysis of the precondition: its PROPs give the facts of some x *)
Lemma hrx5_B8R_ext {Espec: OracleKind} {cs: compspecs} Delta (Ps: list Prop) (Lc: list localdef) (Sp: list mpred)
  (X: Type) (F: X -> list Prop) c Post :
  (fold_right and True Ps -> exists x, fold_right and True (F x)) ->
  (forall x, semax Delta (PROPx (Ps ++ F x) (LOCALx Lc (SEPx Sp))) c Post) ->
  semax Delta (PROPx Ps (LOCALx Lc (SEPx Sp))) c Post.
Proof.
  intros HF HS.
  apply semax_pre with (EX x: X, PROPx (Ps ++ F x) (LOCALx Lc (SEPx Sp))).
  2: { Intros x. apply HS. }
  apply andp_left2. intro rho. unfold PROPx. simpl. apply derives_extract_prop. intros HP.
  destruct (HF HP) as [x Hx]. apply (exp_right x). simpl.
  apply andp_right; [| apply derives_refl].
  apply prop_right. clear - HP Hx. induction Ps; simpl in *; tauto.
Qed.

Definition hrx5_B8_R2_stmt : Prop :=
  forall (Espec: OracleKind) x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE
    st i kc lul q proto ip4 ip6 port o dp img tg ai ar d,
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hrx5_B8_isR o (hrx5_B8_path x25519 L R sec birth S w PS T kc lul q proto ip4 ip6 port o dp d) ai ar tg ->
  itable_wf T ->
  @semax W Espec (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec)
    (hrx5_B8_Q x25519 aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto
       ip4 ip6 port o dp img tg ai ar d)
    hrx5_B8_R (overridePost (hrx5_S8 x25519 gv L FR) (hrx5_RB x25519 gv L FR)).

Lemma hrx5_B8_R2_ok : hrx5_B8_R2_stmt.
Proof.
  intros Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul
    q proto ip4 ip6 port o dp img tg ai ar d HY HX HW.
  rewrite hrx5_B8R_l_eq. unfold hrx5_B8_Q. cbv zeta.
  apply (hrx5_B8R_ext _ _ _ _ (val * peer * resp_msg * list byte * list byte * Z)
           (fun x => match x with (a, P, M, ck, h, j) =>
              hrx5_B8R_facts x25519 aead_dec xaead_enc xaead_dec L R sec birth S w NS PS T kc lul q proto ip4 ip6 port
                o dp tg ai ar d a P M ck h j end)).
  { cbn [fold_right]. intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & _).
    destruct (hrx5_B8R_P_ok x25519 aead_enc aead_dec xaead_enc xaead_dec L R sec birth S w NS PS T head nk KE st i
                kc lul q proto ip4 ip6 port o dp tg ai ar d HY H1 H2 H3 H4 H5 H6 H7 H8 HX)
      as (a & P & M & ck & h & j & HF).
    exists (a, P, M, ck, h, j). exact HF. }
  intros [[[[[a P] M] ck] h] j].
  change (hrx5_seql hrx5_B8R_l) with
    (hrx5_seql (firstn 7 hrx5_B8R_l ++ (firstn 1 (skipn 7 hrx5_B8R_l) ++
      (firstn 2 (skipn 8 hrx5_B8R_l) ++ skipn 10 hrx5_B8R_l)))).
  eapply hrx5_seql_app; [discriminate | discriminate | rewrite hrx5_overridePost2 |].
  { exact (hrx5_B8R_A_ok Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk
             KE st i kc lul q proto ip4 ip6 port o dp img tg ai ar d a P M ck h j HY). }
  eapply hrx5_seql_app; [discriminate | discriminate | rewrite hrx5_overridePost2 |].
  { exact (hrx5_B8R_B_ok Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk
             KE st i kc lul q proto ip4 ip6 port o dp img tg ai ar d a P M ck h j HY HW). }
  eapply hrx5_seql_app; [discriminate | discriminate | rewrite hrx5_overridePost2 |].
  { exact (hrx5_B8R_D_ok Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk
             KE st i kc lul q proto ip4 ip6 port o dp img tg ai ar d a P M ck h j HY). }
  exact (hrx5_B8R_E_ok hrx5_B8R_I_ok Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS
           T head nk KE st i kc lul q proto ip4 ip6 port o dp img tg ai ar d a P M ck h j HY).
Qed.
