(* law handshake_receive: B8 branch R segment B: KP (kp = current keypair), K1 (CHECK !hashed && frees same), K2 (the keypair CHECK).
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_ilem.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_B_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_B_K_sep.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_B_K_lem.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_B_K_K2.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

(* Q' a sublist of Q, element by element *)
Ltac hrx5_B8RBK_sub :=
  let Q0 := fresh "Q0" in let HQ := fresh "HQ" in
  intros Q0 HQ; simpl In in HQ;
  repeat (destruct HQ as [<- | HQ]; [simpl In; repeat (first [left; reflexivity | right]) | ]);
  contradiction.

Lemma hrx5_B8RBK_close (Pl: list Prop) Q Q' R R' :
  fold_right and True Pl -> (forall q, In q Q' -> In q Q) -> fold_right_sepcon R |-- fold_right_sepcon R' ->
  PROPx [] (LOCALx Q (SEPx R)) |-- PROPx Pl (LOCALx Q' (SEPx R')).
Proof.
  intros HP HQ HR. eapply derives_trans; [apply LOCALx_shuffle_derives, HQ|].
  unfold PROPx, LOCALx, SEPx. intro rho. cbn. normalize. try (apply andp_right; [apply prop_right, HP|]).
  apply andp_derives; [apply derives_refl | apply HR].
Qed.

Lemma hrx5_B8RB_KP_ok : hrx5_B8RB_KP_stmt.
Proof.
  intros Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q
    proto ip4 ip6 port o dp img tg ai ar d a P M ck h j HY.
  cbv beta zeta delta [hrx5_B8RB_Ss hrx5_B8RB_Ssk hrx5_B8R_St].
  unfold hrx5_Delta, hrx5_B8RB_KP.
  abbreviate_semax.
  match goal with |- semax _ (PROPx ?Pl _) _ _ => assert_PROP (fold_right and True Pl) as HPall end.
  { apply andp_left2. unfold PROPx. apply andp_left1. apply derives_refl. }
  pose proof HPall as HP.
  rewrite !fold_right_and_app_low in HP.
  destruct HP as [HP0 [HG HFF]].
  unfold hrx5_B8RB_G in HG. unfold hrx5_B8RB_FA, hrx5_B8RB_FS in HFF. cbn [fold_right] in HG, HFF, HP0.
  destruct HP0 as (Hbase & Hinv & Hst & Hi & Hobj & Hmc & Hacc & Hrd & _).
  destruct HG as (HGo & HGfwd & HGai & HGar & HGtgt & HGj & HGPS & HGnp & HGtg & HGlen & HGN & HGsf & HGvin & HGep
    & HGet & HGal & HGfa & HGfr & _).
  destruct HFF as ((HFa & HFPS & HFT & HFKS & HFS & HFin & HFsf & HFz & HFx & _) & HFs & HFk & HFvh & HFvk & HFsk
    & HFinit & HFri & HFrefs & HFclr & HFw & HFWx & _).
  assert (Hsf: sfind PS a = Some (Ews, P)).
  { destruct Hinv as (_ & _ & HND & _). exact (hrx5_B8RBK_sfind_Znth PS j a Ews P HND HGj HGPS). }
  set (N := Znth j (hnodes_snapped4 T NS PS)) in HGN.
  assert (HNin: In N (hnodes_snapped4 T NS PS)).
  { apply Znth_In. rewrite hrx5_B8RBK_snapped_len by exact HGlen. lia. }
  assert (HNa: hn_addr N = tg) by (rewrite HGN; reflexivity).
  assert (HNp: hn_p N = a) by (rewrite HGN; reflexivity).
  match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?R))) _ _ =>
    apply semax_pre with (PROPx [] (LOCALx Q (SEPx R)));
    [ apply andp_left2; apply andp_derives; [apply prop_derives; intros; exact I | apply derives_refl] | ] end.
  unfold hrx5_B8R_tl, hrx5_ptrs, hrx5_lvars, hrx5_scr5, hrx5_rest, hrx5_cglobs. cbn [app].
  unfold rxw_rep at 1. Intros.
  rewrite HFPS, (hrx5_B8RBK_peers PS a Ews P (hrx5_B8RB_Pz d P M ck h) Hsf). Intros.
  assert_PROP (@field_compatible Noise.CS t_peer [] a) as Hfca.
  { unfold peer_rep at 1. entailer!. }
  sep_apply (hrx5_B8RBK_pk_kps Ews a (hrx5_B8RB_Pz d P M ck h)). Intros lk.
  pose proof (hrx5_B8RBK_nodes_acc (@field_at W Ews t_hnode4 [StructField HC._p] (hn_p N) (hn_addr N)) N
    (hnodes_snapped4 T NS PS) (hrx5_head (hnodes_snapped4 T NS PS)) HNin (fun nx => hrx5_B8RBK_nfld_p N nx)) as HA.
  unfold hrx5_B8RBK_acc in HA. sep_apply HA. clear HA. Intros.
  rewrite HNa, HNp.
  rewrite (hrx5_B8RBK_cur d P M ck h HFs).
  assert (HFKS': rw_KS (hrx5_B8R_W1 x25519 aead_dec xaead_enc xaead_dec L R sec birth S w PS T kc lul q proto ip4 ip6
    port o dp d) = [(rd_k d, hrx5_B8RB_K P M ck h kc (hrx5_B8RB_S1 x25519 R L sec birth S q lul o d))])
    by (rewrite HFKS, HFs; reflexivity).
  assert_PROP (@field_compatible Noise.CS t_kp [] (rd_k d)) as Hfck.
  { rewrite HFKS'. unfold keypairs_rep. cbn [iter_sepcon keypair_item_rep].
    sep_apply (hrx5_B8RBK_kp_fc (rd_k d) (hrx5_B8RB_K P M ck h kc (hrx5_B8RB_S1 x25519 R L sec birth S q lul o d))).
    entailer!. }
  freeze FR0 := - (field_at _ t_hnode4 _ _ _) (field_at _ t_peer _ _ _).
  forward.
  forward.
  { entailer!. destruct Hfck as [Hp _]. destruct (rd_k d); try contradiction. simpl. auto. }
  try unfold POSTCONDITION, abbreviate; try unfold overridePost.
  destruct (hrx5_RB x25519 gv L FR) as [r1 r2 r3 r4]. cbn [RA_normal].
  thaw FR0.
  match goal with |- context [(?D -* ?X)] => sep_apply (modus_ponens_wand D X) end.
  match goal with |- context [(?D -* ?X)] => sep_apply (modus_ponens_wand D X) end.
  sep_apply (derives_refl' _ _ (eq_sym (hrx5_B8RBK_peers PS a Ews P (hrx5_B8RB_Pz d P M ck h) Hsf))).
  unfold hrx5_B8R_tl, hrx5_ptrs, hrx5_lvars, hrx5_scr5, hrx5_rest, hrx5_cglobs. cbn [app].
  unfold rxw_rep at 1. rewrite HFPS.
  apply andp_left2. apply hrx5_B8RBK_close; [exact HPall | hrx5_B8RBK_sub |].
  cbn [fold_right_sepcon]. cancel.
Qed.

Lemma hrx5_B8RBK_tulong {cs1 cs2: compspecs} sh v p :
  @data_at cs1 sh tulong v p = @data_at cs2 sh tulong v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext.
  unfold field_compatible; simpl.
  split; intros (?&?&?&?&?); (repeat split); auto;
    destruct p; try contradiction; unfold align_compatible in *;
    (apply align_compatible_rec_by_value with Mint64; [reflexivity|]);
    apply (align_compatible_rec_by_value_inv _ _ Mint64) in H2; auto.
Qed.

Lemma hrx5_B8RBK_ss sh v p : @data_at CKS sh t_shimsnap v p = @data_at W sh t_shimsnap v p.
Proof.
  apply (f_equal (fun f => f p)). apply (@data_at_change_composite CKS W _ sh t_shimsnap); [apply JMeq_refl | reflexivity].
Qed.

Lemma hrx5_B8RB_K1_ok : hrx5_B8RB_K1_stmt.
Proof.
  intros Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q
    proto ip4 ip6 port o dp img tg ai ar d a P M ck h j HY.
  cbv beta zeta delta [hrx5_B8RB_Ssk hrx5_B8R_St].
  unfold hrx5_Delta, hrx5_B8RB_K1.
  abbreviate_semax.
  match goal with |- semax _ (PROPx ?Pl _) _ _ => assert_PROP (fold_right and True Pl) as HPall end.
  { apply andp_left2. unfold PROPx. apply andp_left1. apply derives_refl. }
  pose proof HPall as HP.
  rewrite !fold_right_and_app_low in HP.
  destruct HP as [HP0 [HG HFF]].
  unfold hrx5_B8RB_G in HG. unfold hrx5_B8RB_FA, hrx5_B8RB_FS in HFF. cbn [fold_right] in HG, HFF, HP0.
  destruct HP0 as (Hbase & Hinv & Hst & Hi & Hobj & Hmc & Hacc & Hrd & _).
  destruct HG as (HGo & HGfwd & HGai & HGar & HGtgt & HGj & HGPS & HGnp & HGtg & HGlen & HGN & HGsf & HGvin & HGep
    & HGet & HGal & HGfa & HGfr & _).
  destruct HFF as ((HFa & HFPS & HFT & HFKS & HFS & HFin & HFsf & HFz & HFx & _) & HFs & HFk & HFvh & HFvk & HFsk
    & HFinit & HFri & HFrefs & HFclr & HFw & HFWx & _).
  assert (Hsf: sfind PS a = Some (Ews, P)).
  { destruct Hinv as (_ & _ & HND & _). exact (hrx5_B8RBK_sfind_Znth PS j a Ews P HND HGj HGPS). }
  assert (HT3: rw_T (hrx5_B8R_W1 x25519 aead_dec xaead_enc xaead_dec L R sec birth S w PS T kc lul q proto ip4 ip6
    port o dp d) = hrx5_B8RB_T3 T a (rd_k d)) by (rewrite HFT, HFs; reflexivity).
  assert (HS3: rw_S (hrx5_B8R_W1 x25519 aead_dec xaead_enc xaead_dec L R sec birth S w PS T kc lul q proto ip4 ip6
    port o dp d) = shim_alloc_ok (hrx5_B8RB_S1 x25519 R L sec birth S q lul o d)) by (rewrite HFS, HFs; reflexivity).
  rewrite HT3 in HFsf.
  match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?R))) _ _ =>
    apply semax_pre with (PROPx [] (LOCALx Q (SEPx R)));
    [ apply andp_left2; apply andp_derives; [apply prop_derives; intros; exact I | apply derives_refl] | ] end.
  unfold hrx5_B8R_tl, hrx5_ptrs, hrx5_lvars, hrx5_scr5, hrx5_rest, hrx5_cglobs. cbn [app].
  unfold rxw_rep at 1. Intros.
  rewrite HFPS, (hrx5_B8RBK_peers PS a Ews P (hrx5_B8RB_Pz d P M ck h) Hsf). Intros.
  assert_PROP (@field_compatible Noise.CS t_hs [] (hs_addr a)) as Hfch.
  { sep_apply (hrx5_B8RBK_peer_fc Ews a (hrx5_B8RB_Pz d P M ck h)). entailer!. }
  rewrite (hrx5_B8RBK_itab x25519 aead_dec xaead_enc xaead_dec L R sec birth S w PS T kc lul q proto ip4 ip6 port o dp d),
    HT3.
  sep_apply (hrx5_B8RBK_hentry (l_itd L) (hrx5_B8RB_T3 T a (rd_k d)) (hs_addr a) (t_entry_d T (hs_addr a)) HFsf Hfch).
  Intros. rewrite HFvh. unfold entry_val. cbn [Val.of_bool].
  rewrite HS3. unfold shim_state4, shim_core. Intros.
  cbn [s_frees shim_alloc_ok]. rewrite HGfr.
  rewrite (hrx5_B8RBK_tulong (cs1 := Noise.CS) (cs2 := W) Ews _ (gv _wg_shim_frees)).
  rewrite (hrx5_B8RBK_ss Tsh _ (l_ss L)).
  freeze FR0 := - (field_at _ t_hs _ _ _) (data_at _ tulong _ (gv _wg_shim_frees)) (data_at _ t_shimsnap _ _).
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  { apply ENTAIL_refl. }
  forward.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp HRM._t'178 (Vint Int.one) :: Q) (SEPx R))) end.
  { forward. forward. forward.
    unfold Int64.cmpu. rewrite Int64.eq_true. apply andp_left2. apply LOCALx_shuffle_derives.
    hrx5_B8RBK_sub. }
  { exfalso. match goal with H: _ |- _ => apply H; reflexivity end. }
  forward_if.
  { match goal with H: Int.one = Int.zero |- _ => exfalso; exact (Int.one_not_zero H) end. }
  { forward. apply andp_left2. apply LOCALx_shuffle_derives. hrx5_B8RBK_sub. }
  forward.
  { destruct (hrx5_RB x25519 gv L FR) as [r1 r2 r3 r4]. unfold loop2_ret_assert. cbn [RA_break RA_normal].
    apply ENTAIL_refl. }
  unfold POSTCONDITION, abbreviate, overridePost.
  destruct (hrx5_RB x25519 gv L FR) as [r1 r2 r3 r4]. cbn [RA_normal].
  thaw FR0.
  match goal with |- context [(?D -* ?X)] => sep_apply (modus_ponens_wand D X) end.
  unfold hrx5_B8R_tl, hrx5_ptrs, hrx5_lvars, hrx5_scr5, hrx5_rest, hrx5_cglobs. cbn [app].
  unfold rxw_rep at 1.
  rewrite HFPS, (hrx5_B8RBK_peers PS a Ews P (hrx5_B8RB_Pz d P M ck h) Hsf).
  rewrite (hrx5_B8RBK_itab x25519 aead_dec xaead_enc xaead_dec L R sec birth S w PS T kc lul q proto ip4 ip6 port o dp d),
    HT3.
  rewrite HS3. unfold shim_state4, shim_core.
  match goal with H: shim_ok _ |- _ => rewrite (prop_true_andp _ _ H) end.
  cbn [s_frees shim_alloc_ok]. rewrite HGfr.
  rewrite (hrx5_B8RBK_tulong (cs1 := Noise.CS) (cs2 := W) Ews _ (gv _wg_shim_frees)).
  rewrite (hrx5_B8RBK_ss Tsh _ (l_ss L)).
  apply andp_left2. apply hrx5_B8RBK_close; [exact HPall | hrx5_B8RBK_sub |].
  cbn [fold_right_sepcon]. cancel.
Qed.

Lemma hrx5_B8RB_K_ok : hrx5_B8RB_KP_stmt /\ hrx5_B8RB_K1_stmt /\ hrx5_B8RB_K2_stmt.
Proof.
  exact (conj hrx5_B8RB_KP_ok (conj hrx5_B8RB_K1_ok hrx5_B8RB_K2_ok)).
Qed.
