(* law handshake_receive, phase B4, segment I, part L:
   lp = `nd = peers; for (; nd; nd = nd->next) if (target == NULL && bytes_eq(nd->p->handshake.remote_static, ci.spub, 32)) target = nd;` (the first-match loop; port of hci5_p7_L, whose loop wrote p instead of target and compared against peers_after: here the peers are PS itself, hrx5_B4_I_after_ok in hrx5_B4_I_pure.v gives the same facts).
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
#[local] Existing Instance W_handshake_receive.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_defs.
Local Open Scope logic.

Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_I_pure.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_I_sep.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_I_defs.
Local Open Scope logic.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hrx5_B4_I_L_ok {Espec: OracleKind} gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port M dp img s key ck1 h1 :
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hrx5_B4_I_c1f x25519 aead_dec (hrx5_ID x25519 R) M = Some (s, key, ck1, h1) ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec)
    (hrx5_B4_I_Q2 x25519 gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port M dp img s key ck1 h1) hrx5_B4_I_lp
    (overridePost (hrx5_B4_I_Qb x25519 gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port M dp img s key ck1 h1) (hrx5_RB x25519 gv L FR)).
Proof.
  intros HH Hc1.
  destruct (hrx5_B4_I_c1f_some x25519 aead_dec _ _ _ _ _ _ Hc1) as [Hfwd Hc1'].
  destruct (hrx5_B4_I_c1_some x25519 aead_dec _ _ _ _ _ _ Hc1') as [Hok H1m].
  unfold hrx5_B4_I_Q2, hrx5_B4_I_Qb, hrx5_B4_I_st, hrx5_B4_I_ci1, hrx5_B4_I_scr, hrx5_Delta, hrx5_RB, hrx5_B4_I_lp,
    hrx5_ltemps, hrx5_ptrs, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs.
  cbn [app obj_bytes obj_kind obj_rep obj_ok].
  simplify_func_tycontext. abbreviate_semax. Intros.
  destruct HH as (Hx & Ha & Hxa).
  destruct (hrx5_B4_I_len_ok x25519 aead_enc aead_dec Hx Ha) as (HlIB & Hl1 & Hlpre & Hl2).
  destruct (Hl1 _ _ _ s key ck1 h1 (proj1 (proj2 H3)) H1m) as (Hls & Hlkey & Hlck1 & Hlh1).
  destruct (hrx5_B4_I_after_ok x25519 R L NS PS KE T head nk H0) as (Hpe & Hsh & Hnone & Hsome).
  sep_apply (hrx5_B4_I_ci_spub Tsh ck1 h1 (bytes key) s (Zrepeat Vundef 12) (l_ci L) Hls).
  Intros. forward.
  set (NS' := hnodes_snapped4 T NS PS) in *.
  match goal with |- semax _ (PROPx _ (LOCALx (_ :: ?a1 :: ?a2 :: ?a3 :: ?a4 :: ?a5 :: ?a6 :: ?a7 :: ?a8 :: ?a9 ::
     ?a10 :: ?a11 :: ?a12 :: ?a13 :: ?a14 :: ?a15 :: ?a16 :: ?a17 :: temp _ _ :: ?Q) (SEPx ?Sp))) _ _ =>
  forward_loop (EX NS1: list hnode4, EX NS2: list hnode4, EX PS1: list (val * share * peer),
                EX PS2: list (val * share * peer),
     PROPx [NS' = NS1 ++ NS2; PS = PS1 ++ PS2; length NS1 = length PS1]
     (LOCALx (temp HRM._nd (hrx5_head NS2) :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: a10 :: a11 ::
              a12 :: a13 :: a14 :: a15 :: a16 :: a17 :: temp HM._target (hrx5_B4_I_fmv (hrx5_B4_I_fm NS1 PS1 s)) :: Q)
     (SEPx Sp)))
  continue: (EX NS1: list hnode4, EX N: hnode4, EX NS2: list hnode4, EX PS1: list (val * share * peer),
                EX x: val * share * peer, EX PS2: list (val * share * peer),
     PROPx [NS' = NS1 ++ N :: NS2; PS = PS1 ++ x :: PS2; length NS1 = length PS1]
     (LOCALx (temp HRM._nd (hn_addr N) :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: a10 :: a11 ::
              a12 :: a13 :: a14 :: a15 :: a16 :: a17 ::
              temp HM._target (hrx5_B4_I_fmv (hrx5_B4_I_fm (NS1 ++ [N]) (PS1 ++ [x]) s)) :: Q)
     (SEPx Sp)))
  break: (PROPx [] (LOCALx (temp HRM._nd nullval :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: a10 :: a11 ::
              a12 :: a13 :: a14 :: a15 :: a16 :: a17 :: temp HM._target (hrx5_B4_I_fmv (hrx5_B4_I_fm NS' PS s)) :: Q)
     (SEPx Sp)))
  end.
  { Exists (@nil hnode4) NS' (@nil (val * share * peer)) PS. entailer!. }
  { Intros NS1 NS2 PS1 PS2.
    match goal with Ha: NS' = NS1 ++ NS2, Hb: PS = PS1 ++ PS2, Hc: length NS1 = length PS1 |- _ =>
      rename Ha into HN, Hb into HP, Hc into HL end.
    destruct NS2 as [|N NS2].
    - assert (PS2 = []) as ->.
      { apply (hrx5_B4_I_pure_end NS1 PS1 PS2); auto.
        rewrite <- HP, <- (app_nil_r NS1), <- HN. exact Hpe. }
      forward_if.
      + exfalso. assumption.
      + forward. rewrite !app_nil_r in HN, HP. rewrite <- HN, <- HP. entailer!.
    - destruct (hrx5_B4_I_pure_split NS1 N NS2 PS1 PS2) as (x & PS2' & -> & HNx).
      { rewrite <- HN, <- HP. exact Hpe. } { exact HL. }
      destruct x as [[a sh] P]. simpl in HNx.
      assert (HinN: In (hn_addr N) (map hn_addr NS')).
      { rewrite HN, map_app. apply in_or_app. right. left. reflexivity. }
      assert (Hin: In (a, sh, P) PS).
      { rewrite HP. apply in_or_app. right. left. reflexivity. }
      assert (Hsh': sh = Ews).
      { rewrite Forall_forall in Hsh. apply (Hsh _ Hin). }
      subst sh.
      pose proof (hrx5_B4_I_hn_valid (hrx5_head NS') NS' (hn_addr N) HinN) as HvN.
      assert_PROP (Forall isptr (map hn_addr NS')) as Hptrs. { sep_apply (hrx5_B4_I_hn_isptr (hrx5_head NS') NS'). entailer!. }
      assert (HpN: isptr (hn_addr N)). { rewrite Forall_forall in Hptrs. auto. }
      forward_if.
      2: { exfalso. match goal with Hn: _ = nullval |- _ => change (hn_addr N = nullval) in Hn;
             rewrite Hn in HpN; exact HpN end. }
      destruct (hrx5_B4_I_fm NS1 PS1 s) as [[N0 x0]|] eqn:Hfm.
      + assert (HinN0: In (hn_addr N0) (map hn_addr NS')).
        { rewrite HN, map_app. apply in_or_app. left. eapply hrx5_B4_I_pure_in; eauto. }
        pose proof (hrx5_B4_I_hn_valid (hrx5_head NS') NS' (hn_addr N0) HinN0) as HvN0.
        assert (HpN0: isptr (hn_addr N0)). { rewrite Forall_forall in Hptrs. auto. }
        cbn [hrx5_B4_I_fmv].
        apply semax_if_seq. forward_if.
        * exfalso. match goal with Hn: hn_addr N0 = nullval |- _ => rewrite Hn in HpN0; exact HpN0 end.
        * forward. forward_if. 1: { hrx5_B4_I_absurd. }
          forward.
          Exists NS1 N NS2 PS1 (a, Ews, P) PS2'.
          rewrite (hrx5_B4_I_pure_snoc NS1 PS1 N (a, Ews, P) s HL), Hfm. cbn [hrx5_B4_I_fmv].
          entailer!.
      + cbn [hrx5_B4_I_fmv].
        apply semax_if_seq. forward_if.
        2: { hrx5_B4_I_absurd. }
        assert (Hnode: hnodes_rep4 W (hrx5_head NS') NS' |--
          (@data_at W Ews t_hnode4 (hrx5_B4_I_nv N (hrx5_head NS2)) (hn_addr N) *
           (@data_at W Ews t_hnode4 (hrx5_B4_I_nv N (hrx5_head NS2)) (hn_addr N) -*
            hnodes_rep4 W (hrx5_head NS') NS'))%logic).
        { rewrite HN. apply hrx5_B4_I_nv_node. }
        assert_PROP (hs_ok (p_hs P) /\ isptr a) as HokPa.
        { sep_apply (hrx5_B4_I_peers_hsok PS a Ews P Hin). entailer!. }
        destruct HokPa as [HokP Hpa].
        sep_apply Hnode. sep_apply (hrx5_B4_I_peer_rs PS a Ews P Hin). Intros.
        change (hrx5_head (N :: NS2)) with (hn_addr N).
        forward.
        match goal with |- context [temp HRM._t'359 ?v] =>
          replace v with a by (unfold hrx5_B4_I_nv; cbv beta iota; symmetry; exact HNx) end.
        assert (Hrs: Zlength (hs_rstatic (p_hs P)) = 32) by apply HokP.
        forward_call (Ews, offset_val 136 a, hs_rstatic (p_hs P), Tsh, offset_val 96 (l_ci L), s).
        1: { rewrite Hrs. entailer!. simpl. destruct (hn_p N); try contradiction.
             destruct (l_ci L); try contradiction. simpl. rewrite !Ptrofs.add_assoc. reflexivity. }
        forward.
        sep_apply (hrx5_B4_I_wand1 (hbytes Ews (hs_rstatic (p_hs P)) (offset_val 136 a)) (peers_rep PS)).
        sep_apply (hrx5_B4_I_wand1 (@data_at W Ews t_hnode4 (hrx5_B4_I_nv N (hrx5_head NS2)) (hn_addr N))
                     (hnodes_rep4 W (hrx5_head NS') NS')).
        destruct (bytes_eqb (hs_rstatic (p_hs P)) s) eqn:Hbe.
        * forward_if. 2: { hrx5_B4_I_absurd. }
          forward.
          Exists NS1 N NS2 PS1 (a, Ews, P) PS2'.
          rewrite (hrx5_B4_I_pure_snoc NS1 PS1 N (a, Ews, P) s HL), Hfm, Hbe. cbn [hrx5_B4_I_fmv].
          entailer!.
        * forward_if. 1: { hrx5_B4_I_absurd. }
          forward.
          Exists NS1 N NS2 PS1 (a, Ews, P) PS2'.
          rewrite (hrx5_B4_I_pure_snoc NS1 PS1 N (a, Ews, P) s HL), Hfm, Hbe. cbn [hrx5_B4_I_fmv].
          entailer!. }
  { Intros NS1 N NS2 PS1 x PS2.
    match goal with Ha: NS' = NS1 ++ N :: NS2, Hb: PS = PS1 ++ x :: PS2, Hc: length NS1 = length PS1 |- _ =>
      rename Ha into HN, Hb into HP, Hc into HL end.
    assert (Hnode: hnodes_rep4 W (hrx5_head NS') NS' |--
      (@data_at W Ews t_hnode4 (hrx5_B4_I_nv N (hrx5_head NS2)) (hn_addr N) *
       (@data_at W Ews t_hnode4 (hrx5_B4_I_nv N (hrx5_head NS2)) (hn_addr N) -*
        hnodes_rep4 W (hrx5_head NS') NS'))%logic).
    { rewrite HN. apply hrx5_B4_I_nv_node. }
    assert_PROP (Forall isptr (map hn_addr NS')) as Hptrs.
    { sep_apply (hrx5_B4_I_hn_isptr (hrx5_head NS') NS'). entailer!. }
    assert (Hpn2: is_pointer_or_null (hrx5_head NS2)). { rewrite HN in Hptrs. eapply hrx5_B4_I_head_pn; eauto. }
    sep_apply Hnode. Intros.
    forward.
    match goal with |- context [temp HRM._nd ?v] =>
      replace v with (hrx5_head NS2) by (unfold hrx5_B4_I_nv; reflexivity) end.
    sep_apply (hrx5_B4_I_wand1 (@data_at W Ews t_hnode4 (hrx5_B4_I_nv N (hrx5_head NS2)) (hn_addr N))
                 (hnodes_rep4 W (hrx5_head NS') NS')).
    Exists (NS1 ++ [N]) NS2 (PS1 ++ [x]) PS2.
    entailer!.
    rewrite <- !app_assoc. simpl. rewrite !length_app. simpl. auto. }
  unfold POSTCONDITION, abbreviate. simpl RA_normal.
  sep_apply (hrx5_B4_I_wand1 (hbytes Tsh s (offset_val 96 (l_ci L)))
    (@data_at HCS Tsh t_mcinit (mcinit_val ck1 h1 (bytes key) (bytes s) (Zrepeat Vundef 12)) (l_ci L))).
  entailer!.
Qed.

End Seg.
