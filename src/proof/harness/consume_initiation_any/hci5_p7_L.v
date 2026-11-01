(* law consume_initiation_any, phase P7, segment L: p = NULL; it = peers; the first-match loop.  Port of v1's hci3_p7_L.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_cut.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_model.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_globals.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_spec.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_defs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_conv.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p7_pure.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p7_defs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p7_sep.
Require WgNoise.harness.x_consume_initiation_any.code.

#[local] Existing Instance W_consume_initiation_any.
Local Open Scope Z_scope.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hci5_p7_L_ok {Espec: OracleKind} gv L FR R S w NS PS T head na KE m M s key ck1 h1 :
  hci5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hci5_p7_c1 x25519 aead_dec (hci5_IB x25519 R) M = Some (s, key, ck1, h1) ->
  semax (hci5_Delta x25519 aead_enc aead_dec)
    (hci5_p7_Q2 x25519 aead_dec gv L FR R S w NS PS T head na KE m M s key ck1 h1) hci5_p7_lp
    (overridePost (hci5_p7_Qb x25519 aead_dec gv L FR R S w NS PS T head na KE m M s key ck1 h1) (hci5_R gv)).
Proof.
  intros HH Hc1.
  destruct (hci5_p7_c1_some x25519 aead_dec _ _ _ _ _ _ Hc1) as [Hok H1m].
  unfold hci5_p7_Q2, hci5_p7_Qb, hci5_p7_st, hci5_p7_ci1, hci5_Delta, hci5_R, hci5_p7_lp, hci5_p7_sp,
    hci5_p7_sit, hci5_p7_loop, hci5_lvars, hci5_world, hci5_globs.
  cbn [app].
  simplify_func_tycontext. abbreviate_semax. Intros.
  destruct HH as (Hx & Ha & Hxa & Hrep).
  destruct (hci5_p7_len_ok x25519 aead_enc aead_dec Hx Ha) as (HlIB & Hl1 & Hlpre & Hl2).
  destruct (Hl1 _ _ _ s key ck1 h1 (proj1 (proj2 H1)) H1m) as (Hls & Hlkey & Hlck1 & Hlh1).
  assert_PROP (itable_wf T) as Hwf. { unfold itable. entailer!. }
  pose proof (hci5_p7_pure_nodup PS KE T Hwf (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 H0))))))) as Hnd.
  destruct (hci5_p7_after_ok x25519 aead_dec R L NS PS KE T head na (hci5_DB x25519 R L) M S H0 Hnd)
    as (Hpe & Hsh & Hnone & Hsome).
  sep_apply (hci5_p7_ci_spub Tsh ck1 h1 (bytes key) s (Zrepeat Vundef 12) (l_ci L) Hls).
  Intros. forward. forward.
  assert (Hhp: hnodes_peers4 NS PS) by apply H0.
  rewrite <- (hci5_p7_head_snapped T NS PS Hhp).
  set (NS' := hnodes_snapped4 T NS PS) in *.
  set (PS' := peers_after PS (cin_res x25519 aead_dec (hci5_DB x25519 R L) PS M S)) in *.
  match goal with |- semax _ (PROPx _ (LOCALx (_ :: _ :: ?Q) (SEPx ?Sp))) _ _ =>
  forward_loop (EX NS1: list hnode4, EX NS2: list hnode4, EX PS1: list (val * share * peer),
                EX PS2: list (val * share * peer),
     PROPx [NS' = NS1 ++ NS2; PS' = PS1 ++ PS2; length NS1 = length PS1]
     (LOCALx (temp HC._it (hci5_head NS2) :: temp HC._p (hci5_p7_fmv (hci5_p7_fm NS1 PS1 s)) :: Q)
     (SEPx Sp)))
  continue: (EX NS1: list hnode4, EX N: hnode4, EX NS2: list hnode4, EX PS1: list (val * share * peer),
                EX x: val * share * peer, EX PS2: list (val * share * peer),
     PROPx [NS' = NS1 ++ N :: NS2; PS' = PS1 ++ x :: PS2; length NS1 = length PS1]
     (LOCALx (temp HC._it (hn_addr N) :: temp HC._p (hci5_p7_fmv (hci5_p7_fm (NS1 ++ [N]) (PS1 ++ [x]) s)) :: Q)
     (SEPx Sp)))
  break: (PROPx [] (LOCALx (temp HC._it nullval :: temp HC._p (hci5_p7_fmv (hci5_p7_fm NS' PS' s)) :: Q)
     (SEPx Sp)))
  end.
  { Exists (@nil hnode4) NS' (@nil (val * share * peer)) PS'. entailer!. }
  { Intros NS1 NS2 PS1 PS2.
    match goal with Ha: NS' = NS1 ++ NS2, Hb: PS' = PS1 ++ PS2, Hc: length NS1 = length PS1 |- _ =>
      rename Ha into HN, Hb into HP, Hc into HL end.
    destruct NS2 as [|N NS2].
    - assert (PS2 = []) as ->.
      { apply (hci5_p7_pure_end NS1 PS1 PS2); auto.
        rewrite <- HP, <- (app_nil_r NS1), <- HN. exact Hpe. }
      forward_if.
      + exfalso. assumption.
      + forward. rewrite !app_nil_r in HN, HP. rewrite <- HN, <- HP. entailer!.
    - destruct (hci5_p7_pure_split NS1 N NS2 PS1 PS2) as (x & PS2' & -> & HNx).
      { rewrite <- HN, <- HP. exact Hpe. } { exact HL. }
      destruct x as [[a sh] P]. simpl in HNx.
      assert (HinN: In (hn_addr N) (map hn_addr NS')).
      { rewrite HN, map_app. apply in_or_app. right. left. reflexivity. }
      assert (Hin: In (a, sh, P) PS').
      { rewrite HP. apply in_or_app. right. left. reflexivity. }
      assert (Hsh': sh = Ews).
      { rewrite Forall_forall in Hsh. apply (Hsh _ Hin). }
      subst sh.
      pose proof (hci5_p7_hn_valid (hci5_head NS') NS' (hn_addr N) HinN) as HvN.
      assert_PROP (Forall isptr (map hn_addr NS')) as Hptrs. { sep_apply (hci5_p7_hn_isptr (hci5_head NS') NS'). entailer!. }
      assert (HpN: isptr (hn_addr N)). { rewrite Forall_forall in Hptrs. auto. }
      forward_if.
      2: { exfalso. match goal with Hn: _ = nullval |- _ => change (hn_addr N = nullval) in Hn;
             rewrite Hn in HpN; exact HpN end. }
      destruct (hci5_p7_fm NS1 PS1 s) as [[N0 x0]|] eqn:Hfm.
      + assert (HinN0: In (hn_addr N0) (map hn_addr NS')).
        { rewrite HN, map_app. apply in_or_app. left. eapply hci5_p7_pure_in; eauto. }
        pose proof (hci5_p7_hn_valid (hci5_head NS') NS' (hn_addr N0) HinN0) as HvN0.
        assert (HpN0: isptr (hn_addr N0)). { rewrite Forall_forall in Hptrs. auto. }
        cbn [hci5_p7_fmv].
        apply semax_if_seq. forward_if.
        * exfalso. match goal with Hn: hn_addr N0 = nullval |- _ => rewrite Hn in HpN0; exact HpN0 end.
        * forward. forward_if. 1: { hci5_p7_absurd. }
          forward.
          Exists NS1 N NS2 PS1 (a, Ews, P) PS2'.
          rewrite (hci5_p7_pure_snoc NS1 PS1 N (a, Ews, P) s HL), Hfm. cbn [hci5_p7_fmv].
          entailer!.
      + cbn [hci5_p7_fmv].
        apply semax_if_seq. forward_if.
        2: { hci5_p7_absurd. }
        assert (Hnode: hnodes_rep4 W (hci5_head NS') NS' |--
          (@data_at W Ews t_hnode4 (hci5_p7_nv N (hci5_head NS2)) (hn_addr N) *
           (@data_at W Ews t_hnode4 (hci5_p7_nv N (hci5_head NS2)) (hn_addr N) -*
            hnodes_rep4 W (hci5_head NS') NS'))%logic).
        { rewrite HN. apply hci5_p7_nv_node. }
        assert_PROP (hs_ok (p_hs P) /\ isptr a) as HokPa.
        { sep_apply (hci5_p7_peers_hsok PS' a Ews P Hin). entailer!. }
        destruct HokPa as [HokP Hpa].
        sep_apply Hnode. sep_apply (hci5_p7_peer_rs PS' a Ews P Hin). Intros.
        change (hci5_head (N :: NS2)) with (hn_addr N).
        forward.
        match goal with |- context [temp HC._t'95 ?v] =>
          replace v with a by (unfold hci5_p7_nv; cbv beta iota; symmetry; exact HNx) end.
        assert (Hrs: Zlength (hs_rstatic (p_hs P)) = 32) by apply HokP.
        forward_call (Ews, offset_val 136 a, hs_rstatic (p_hs P), Tsh, offset_val 96 (l_ci L), s).
        1: { rewrite Hrs. entailer!. simpl. destruct (hn_p N); try contradiction.
             destruct (l_ci L); try contradiction. simpl. rewrite !Ptrofs.add_assoc. reflexivity. }
        forward.
        sep_apply (hci5_p7_wand1 (hbytes Ews (hs_rstatic (p_hs P)) (offset_val 136 a)) (peers_rep PS')).
        sep_apply (hci5_p7_wand1 (@data_at W Ews t_hnode4 (hci5_p7_nv N (hci5_head NS2)) (hn_addr N))
                     (hnodes_rep4 W (hci5_head NS') NS')).
        destruct (bytes_eqb (hs_rstatic (p_hs P)) s) eqn:Hbe.
        * forward_if. 2: { hci5_p7_absurd. }
          forward.
          Exists NS1 N NS2 PS1 (a, Ews, P) PS2'.
          rewrite (hci5_p7_pure_snoc NS1 PS1 N (a, Ews, P) s HL), Hfm, Hbe. cbn [hci5_p7_fmv].
          entailer!.
        * forward_if. 1: { hci5_p7_absurd. }
          forward.
          Exists NS1 N NS2 PS1 (a, Ews, P) PS2'.
          rewrite (hci5_p7_pure_snoc NS1 PS1 N (a, Ews, P) s HL), Hfm, Hbe. cbn [hci5_p7_fmv].
          entailer!. }
  { Intros NS1 N NS2 PS1 x PS2.
    match goal with Ha: NS' = NS1 ++ N :: NS2, Hb: PS' = PS1 ++ x :: PS2, Hc: length NS1 = length PS1 |- _ =>
      rename Ha into HN, Hb into HP, Hc into HL end.
    assert (Hnode: hnodes_rep4 W (hci5_head NS') NS' |--
      (@data_at W Ews t_hnode4 (hci5_p7_nv N (hci5_head NS2)) (hn_addr N) *
       (@data_at W Ews t_hnode4 (hci5_p7_nv N (hci5_head NS2)) (hn_addr N) -*
        hnodes_rep4 W (hci5_head NS') NS'))%logic).
    { rewrite HN. apply hci5_p7_nv_node. }
    assert_PROP (Forall isptr (map hn_addr NS')) as Hptrs.
    { sep_apply (hci5_p7_hn_isptr (hci5_head NS') NS'). entailer!. }
    assert (Hpn2: is_pointer_or_null (hci5_head NS2)). { rewrite HN in Hptrs. eapply hci5_p7_head_pn; eauto. }
    sep_apply Hnode. Intros.
    forward.
    match goal with |- context [temp HC._it ?v] =>
      replace v with (hci5_head NS2) by (unfold hci5_p7_nv; reflexivity) end.
    sep_apply (hci5_p7_wand1 (@data_at W Ews t_hnode4 (hci5_p7_nv N (hci5_head NS2)) (hn_addr N))
                 (hnodes_rep4 W (hci5_head NS') NS')).
    Exists (NS1 ++ [N]) NS2 (PS1 ++ [x]) PS2.
    entailer!.
    rewrite <- !app_assoc. simpl. rewrite !length_app. simpl. auto. }
  assert (Hh: hci5_head NS' = hci5_head NS) by (apply hci5_p7_head_snapped; exact Hhp).
  unfold POSTCONDITION, abbreviate. simpl RA_normal.
  sep_apply (hci5_p7_wand1 (hbytes Tsh s (offset_val 96 (l_ci L)))
    (@data_at HCS Tsh t_mcinit (mcinit_val ck1 h1 (bytes key) (bytes s) (Zrepeat Vundef 12)) (l_ci L))).
  rewrite Hh. entailer!.
Qed.

End Seg.
