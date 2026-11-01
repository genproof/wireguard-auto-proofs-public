(* law handshake_receive: B8 branch R segment B: C3 = CHECK(h's entry and the other fields vs the snapshot s) of the failed allocation.
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_B_C3_sep.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_B_C3_pure.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_B_C3_core.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_B_C3_open.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

(* The CHECK is proved over a small state (hrx5_B8_R_B_C3_core.v: the twenty fields it reads and a frame); Sf is
   opened into that state with the frame = a wand back to Sf's own SEP list (hrx5_B8_R_B_C3_open.v).  Port of
   hrx5_B8_I_I2.v. *)
Lemma hrx5_B8RBC3_S_eq hv sv pe nxt hb ty ix sid eph rs ss psk ts lic F :
  hrx5_B8RBC3_S hv sv pe nxt hb ty ix sid eph rs ss psk ts lic F =
  hrx5_B8RBC3_C hv sv pe nxt hb ty ix sid eph rs ss psk ts lic ++ [F].
Proof. reflexivity. Qed.

Lemma hrx5_B8RB_C3_ok : hrx5_B8RB_C3_stmt.
Proof.
  intros Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q
    proto ip4 ip6 port o dp img tg ai ar d a P M ck h j HY.
  generalize (hrx5_RB x25519 gv L FR) as Rr. intros Rr.
  cbv beta iota zeta delta [hrx5_B8RB_Sf hrx5_B8R_St hrx5_B8RB_G hrx5_B8RB_FF hrx5_B8R_tl].
  cbn [app].
  Intros.
  match goal with H: o = OResp M |- _ => subst o end.
  unfold hrx5_ptrs. cbn [app].
  match goal with
  | H0: hrx5_inv _ _ _ _ _ _ _ _ _, H12: 0 <= j < Zlength PS, H13: Znth j PS = _,
    H16: Zlength NS = Zlength PS, H18: sfind (t_D T) (hs_addr a) = _ |- _ =>
    destruct (hrx5_B8RBC3_facts x25519 R L NS PS KE T head nk a P j _ H0 H12 H13 H16 H18)
      as (Hsf & Hok & Hsid & HinT & Hsh & HinN)
  end.
  match goal with H: Znth j (hnodes_snapped4 T NS PS) = _ |- _ => rewrite H in HinN end.
  set (N := {| hn_addr := tg; hn_p := a; hn_snap := hsnap_val (hs_snap_cur T a P); hn_refs := Vint (p_refs P);
               hn_rest := prsnap_val P |}) in HinN.
  match goal with H: rw_T _ = T |- _ => rename H into HT end.
  match goal with H: rw_PS _ = supd PS a _ |- _ => rename H into HPS end.
  match goal with H: e_peer (t_entry_d T (hs_addr a)) = a |- _ => rename H into Hep end.
  match goal with |- semax _ (PROPx [] (LOCALx _ (SEPx ?SL0))) _ _ => set (SL := SL0) end.
  assert_PROP (@field_compatible Noise.CS t_peer [] a) as Hfp.
  { apply andp_left2. apply (hrx5_B8RBC3_sep_prop _ _ (rxw_rep W gv Tsh (l_wd L) head
      (hrx5_B8R_W1 x25519 aead_dec xaead_enc xaead_dec L R sec birth S w PS T kc lul q proto ip4 ip6 port
         (OResp M) dp d))); [subst SL; left; reflexivity |].
    unfold rxw_rep. rewrite HPS. sep_apply (hrx5_B8RBC3_fc_prop PS a P (p_set_refs (hrx5cr_new P M ck h) (p_refs P)) Hsf). entailer!. }
  assert (Hfc: @field_compatible Noise.CS t_hs [] (hs_addr a)) by (apply hrx5_B8RBC3_fchN; exact Hfp).
  assert_PROP (@field_compatible W t_hsnap [] (offset_val 8 tg)) as Hfs.
  { apply andp_left2.
    apply (hrx5_B8RBC3_sep_prop _ _ (hnodes_rep4 W (hrx5_head (hnodes_snapped4 T NS PS)) (hnodes_snapped4 T NS PS)));
      [subst SL; cbn [hrx5_rest app In]; right; repeat (first [left; reflexivity | right]) |].
    apply (hrx5_B8RBC3_fcs_prop _ _ N HinN). }
  assert_PROP (isptr (l_wd L)) as Pwd.
  { apply andp_left2. apply (hrx5_B8RBC3_sep_prop _ _ (rxw_rep W gv Tsh (l_wd L) head
      (hrx5_B8R_W1 x25519 aead_dec xaead_enc xaead_dec L R sec birth S w PS T kc lul q proto ip4 ip6 port
         (OResp M) dp d))); [subst SL; left; reflexivity |].
    unfold rxw_rep. sep_apply hrx5_B8RBC3_dev_ptr. entailer!. }
  assert_PROP (is_pointer_or_null (succ_in (t_L T) (hs_addr a))) as Hpn.
  { destruct (hrx5_B8RBC3_succ_in (t_L T) (hs_addr a)) as [E | E];
      [rewrite E; apply prop_right; simpl; auto |].
    apply andp_left2. apply (derives_trans _ (!! isptr (succ_in (t_L T) (hs_addr a)))).
    - apply (hrx5_B8RBC3_sep_prop _ _ (rxw_rep W gv Tsh (l_wd L) head
        (hrx5_B8R_W1 x25519 aead_dec xaead_enc xaead_dec L R sec birth S w PS T kc lul q proto ip4 ip6 port
           (OResp M) dp d))); [subst SL; left; reflexivity |].
      unfold rxw_rep. rewrite HT. sep_apply (hrx5_B8RBC3_itable_ptr Tsh (d_itab (rw_D (hrx5_B8R_W1 x25519 aead_dec xaead_enc xaead_dec L R sec birth S w PS T kc lul q proto ip4 ip6 port (OResp M) dp d))) T _ E). entailer!.
    - apply prop_derives. intros Hp. destruct (succ_in (t_L T) (hs_addr a)); simpl in *; try contradiction; auto. }
  assert (Hpa: is_pointer_or_null (e_peer (t_entry_d T (hs_addr a))))
    by (rewrite Hep; destruct Hfp as [Hp _]; destruct a; try contradiction; exact I).
  assert (Hps: is_pointer_or_null (hs_sid (p_hs P)))
    by (rewrite Hsid; unfold id_addr; destruct (l_wd L); try contradiction; exact I).
  set (Cl := hrx5_B8RBC3_Cl T a P N).
  match goal with |- semax _ (PROPx [] (LOCALx
      (temp _ ?hv :: temp _ ?sv :: temp _ ?va :: temp _ ?vs :: temp _ ?vhd :: temp _ ?vnk :: temp _ ?vkes ::
       temp _ ?vst :: temp _ ?vi :: temp _ ?vnow :: temp _ ?vlul :: temp _ ?vbuf :: temp _ ?vmi :: temp _ ?vmr ::
       temp _ ?vmc :: temp _ ?vimg :: temp _ ?vlen :: temp _ ?vkind :: temp _ ?vai :: temp _ ?var :: temp _ ?vtg ::
       temp _ ?vh0 :: temp _ ?vpath :: _) _)) _ _ =>
    set (Q := hrx5_B8RBC3_st gv L va vs vhd vnk vkes vst vi vnow vlul vbuf vmi vmr vmc vimg vlen vkind vai var vtg vh0
            vpath hv sv (e_peer (t_entry_d T (hs_addr a))) (succ_in (t_L T) (hs_addr a))
            (vin (hs_addr a) (t_L T)) (e_type (t_entry_d T (hs_addr a))) (e_index (t_entry_d T (hs_addr a)))
            (hs_sid (p_hs P)) (hs_eph (p_hs P)) (hs_rstatic (p_hs P)) (hs_ss (p_hs P)) (hs_psk (p_hs P))
            (hs_ts (p_hs P)) (hs_lic (p_hs P)) (fold_right_sepcon Cl -* fold_right_sepcon SL) [])
  end.
  apply semax_pre_post with (P' := Q) (R' := overridePost Q Rr).
  - subst Q. unfold hrx5_B8RBC3_st. apply SEP_entail.
    subst Cl SL.
    exact (hrx5_B8RBC3_open x25519 gv L R head _ _ _ _ PS T a P M ck h N HT HPS HinT Hsh Hsf Hfc HinN
             eq_refl Hok).
  - destruct Rr as [r1 r2 r3 r4]. simpl_ret_assert.
    subst Q. unfold hrx5_B8RBC3_st. rewrite hrx5_B8RBC3_S_eq.
    eapply derives_trans; [apply SEP_entail with (R' := SL); apply hrx5_B8RBC3_mp |].
    apply hrx5_B8RBC3_prop_intro. cbn [fold_right].
    repeat (apply conj; [first [assumption | reflexivity] |]). exact I.
  - intros; destruct Rr as [r1 r2 r3 r4]; simpl_ret_assert; apply andp_left2, derives_refl.
  - intros; destruct Rr as [r1 r2 r3 r4]; simpl_ret_assert; apply andp_left2, derives_refl.
  - intros; destruct Rr as [r1 r2 r3 r4]; simpl_ret_assert; apply andp_left2, derives_refl.
  - subst Q. apply hrx5_B8RBC3_core.
    unfold hrx5_B8RBC3_hyps.
    pose proof Hok as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
    split; [exact Hpa |]. split; [exact Hpn |]. split; [exact Hps |].
    split; [apply hrx5_B8RBC3_fch; exact Hfp |]. split; [exact Hfs |].
    split; [exact L1 |]. split; [exact L2 |]. split; [exact L4 |]. split; [exact L5 |]. split; [exact L8 |].
    subst Cl SL.
    exact (hrx5_B8RBC3_hv x25519 gv L R head _ _ _ _ PS T a P M ck h (hrx5_B8RBC3_Cl T a P N) HT HPS Hsf Hsid Hep).
Qed.
