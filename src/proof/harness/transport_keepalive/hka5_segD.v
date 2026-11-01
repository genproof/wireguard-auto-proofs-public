(* segment D of main's loop body (statement 17: the verdict: rc_same on a bad tag; wm_accepts, wg_counter_validate, the CHECKs, wm_commit (its failure: frees and break), have_auth, last_nonce on a good one).
   States and segments: hka5_defs.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_dec3.
Require Import WgNoise.proof.counter.counter_spec.
Require Import WgNoise.proof.harness.transport_keepalive.hka5_defs.
Require Import WgNoise.proof.harness.transport_keepalive.hka5e_lemmas.
Require WgNoise.proof.harness.counter.hcnt_defs3.

#[local] Existing Instance W_transport_keepalive.
Local Open Scope Z_scope.

Ltac hka5d_post := unfold hka5_LR, hka5_R;
  cbn [RA_break RA_normal loop1_ret_assert overridePost frame_ret_assert function_body_ret_assert].

Lemma hka5d_ok_facts top S bm n : 0 <= n -> cnt_inv top S bm -> cnt_ok top S n = true ->
  0 <= top <= CNT_R /\ 0 <= n < CNT_R /\ Forall (fun x => 0 <= x < CNT_R) S.
Proof.
  intros Hn Hc Hok. pose proof (cnt_top_range _ _ _ Hc) as Ht. pose proof (cnt_L_range _ _ _ Hc) as HL.
  unfold cnt_ok in Hok. rewrite !andb_true_iff in Hok. destruct Hok as (((H1 & H2) & H3) & H4).
  apply Z.ltb_lt in H2. apply Z.leb_le in H3.
  split; [lia |]. split; [lia |].
  apply Forall_forall. intros x Hx. specialize (HL x Hx). lia.
Qed.

Lemma hka5d_words top S bm : cnt_inv top S bm -> 0 <= top <= Int64.max_unsigned /\ ht4k_words bm.
Proof.
  intros Hc. pose proof (cnt_top_range _ _ _ Hc). split.
  - unfold CNT_R, CNT_W in *. rep_lia.
  - split; [apply (cnt_len _ _ _ Hc) | apply (cnt_words _ _ _ Hc)].
Qed.

Lemma hka5d_S_range top S bm : cnt_inv top S bm -> Forall (fun x => 0 <= x <= Int64.max_unsigned) S.
Proof.
  intros Hc. pose proof (cnt_top_range _ _ _ Hc). pose proof (cnt_L_range _ _ _ Hc) as HL.
  apply Forall_forall. intros x Hx. specialize (HL x Hx). unfold CNT_R, CNT_W in *. rep_lia.
Qed.

Ltac hka5d_eq_contra :=
  exfalso; match goal with Hx: Int.repr (Z.b2z (Int64.eq ?a ?a)) = Int.zero |- _ =>
    rewrite Int64.eq_true in Hx; apply Int.one_not_zero; exact Hx end.

Lemma hka5d_top_ok top S n : cnt_ok top S n = true ->
  cnt_top' top S n = Z.max top (n + 1) /\ cnt_L' top S n = n :: S.
Proof. intros H. unfold cnt_top', cnt_L'. rewrite H. auto. Qed.

Lemma hka5d_top_nok top S n : cnt_ok top S n = false -> cnt_top' top S n = top /\ cnt_L' top S n = S.
Proof. intros H. unfold cnt_top', cnt_L'. rewrite H. auto. Qed.

Lemma hka5_segD_ok {Espec: OracleKind} gv vrc vwm vsnap vkey key steps FR i top S bm ha ln nonce hdr c pkt po rp okv :
  semax hka5_Delta (hka5_PD gv vrc vwm vsnap vkey key steps FR i top S bm ha ln nonce hdr c pkt po rp okv) hka5_segD
    (overridePost (hka5_QD gv vrc vwm vsnap vkey key steps FR i hdr c pkt po rp)
                  (hka5_LR gv vrc vwm vsnap vkey key steps FR)).
Proof.
  unfold hka5_Delta, hka5_PD, hka5_segD, hka5_tB, hka5_tl, hka5_lv, hka5_cw, hka5_fr, hka5_pkt.
  simpl app. abbreviate_semax. Intros.
  assert (Hf := H). destruct Hf as (Hi & Hs & Hk & Hc & Hha & Hln).
  destruct (hka5d_words _ _ _ Hc) as [Htop Hw].
  forward_if.
  - (* bad tag: CHECK(rc_same(&snap, &rc)) *)
    match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
    + apply ENTAIL_refl.
    + forward_call (Tsh, vsnap, top, bm, Tsh, vrc, top, bm).
      rewrite (if_true _ (Z.eq_dec top top)) by reflexivity.
      rewrite (if_true _ (list_eq_dec Z.eq_dec bm bm)) by reflexivity.
      forward_if; [exfalso; discriminate |].
      forward. entailer!.
    + forward. apply ENTAIL_refl.
    + unfold POSTCONDITION, abbreviate. hka5d_post. unfold hka5_QD, hka5_PE, hka5_tl, hka5_lv, hka5_cw, hka5_fr, hka5_pkt. simpl app.
      Exists top S bm ha ln. entailer!.
  - (* good tag: the counter verdict against the shadow model *)
    forward_call (Tsh, vwm, top, S, nonce).
    { apply (hka5d_S_range _ _ _ Hc). }
    forward_call (Tsh, vrc, top, S, bm, nonce).
    Intros bm'.
    destruct (cnt_ok top S nonce) eqn:Hok.
    + destruct (hka5d_top_ok _ _ _ Hok) as [Et EL]. rewrite Et in *. rewrite EL in H5.
      destruct (hka5d_ok_facts _ _ _ nonce ltac:(lia) Hc Hok) as (Ht & Hn & HS).
      match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
      * apply ENTAIL_refl.
      * forward_if; [exfalso; discriminate |]. forward. entailer!.
      * forward. apply ENTAIL_refl.
      * forward_if (PROP ()
          LOCAL (temp KA._r (Val.of_bool true); temp KA._pred (Vint Int.one); temp KA._ok (Vint okv);
            temp KA._nonce (Vlong (Int64.repr nonce)); temp KA._enc_len (Vlong (Int64.repr (Zlength c)));
            temp KA._pt_len (Vlong (Int64.repr 0)); temp KA._pkt pkt; temp KA._pt_out po; temp KA._ref_pt rp;
            temp KA._i (Vlong (Int64.repr i)); temp KA._steps (Vlong (Int64.repr steps));
            temp KA._have_auth (Vint (Int.repr ha)); temp KA._last_nonce (Vlong (Int64.repr ln));
            lvar KA._rc ht4k_trc vrc; lvar KA._wm ht4k_twm vwm; lvar KA._snap ht4k_tsnap vsnap;
            lvar KA._key (tarray tuchar 32) vkey; gvars gv)
          SEP (data_at Tsh ht4k_trc (ht4k_rc (Z.max top (nonce + 1)) bm') vrc;
            ht4k_wm Tsh (Z.max top (nonce + 1)) (ht4k_prune (Z.max top (nonce + 1)) (nonce :: S)) vwm;
            malloc_token Ews (tarray tuchar (16 + Zlength c)) pkt; data_at Ews (tarray tuchar 16) hdr pkt;
            data_at Ews (tarray tuchar (Zlength c)) (map Vubyte c) (offset_val 16 pkt);
            hka5_mb po; hka5_mb rp; data_at Tsh ht4k_tsnap (ht4k_snap top bm) vsnap;
            data_at Tsh (tarray tuchar 32) (map Vubyte key) vkey; mem_mgr gv; zero_page gv;
            ht4_minusp hka5_mp gv; FR)).
        { match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
          - apply ENTAIL_refl.
          - forward_if; [exfalso; discriminate |]. forward. entailer!.
          - forward. apply ENTAIL_refl.
          - forward_call (Tsh, vwm, top, S, nonce, gv).
            Intros b. destruct b.
            + forward_if; [exfalso; discriminate |]. forward.
              hka5d_post. entailer!.
            + forward_if; [| exfalso; auto].
              assert_PROP (malloc_compatible (sizeof (tarray tuchar (16 + Zlength c))) pkt) as Hmc by entailer!.
              assert_PROP (isptr pkt) as Hpk by entailer!.
              assert (Hfc: field_compatible (tarray tuchar (16 + Zlength c)) [] pkt)
                by (apply hka5e_fc; [pose proof (Zlength_nonneg c); lia | exact Hmc]).
              sep_apply (hka5e_pkt_join Ews pkt hdr c H3 Hfc).
              forward_call (tarray tuchar (16 + Zlength c), pkt, gv).
              { rewrite (if_false _ (eq_dec pkt nullval)) by (intro; subst; contradiction). cancel. }
              forward_call (tarray tuchar 0, po, gv).
              { unfold hka5_mb. cancel. }
              forward_call (tarray tuchar 0, rp, gv).
              forward.
              hka5d_post. unfold hka5_Brk, hka5_lv, hka5_fr.
              Exists top S. entailer!. }
        { exfalso. apply Int.one_not_zero. assumption. }
        match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
        -- apply ENTAIL_refl.
        -- unfold ht4k_wm. Intros wp. forward. forward. forward_if.
           { hka5d_eq_contra. }
           forward. unfold ht4k_wm. Exists wp. entailer!.
        -- forward. apply ENTAIL_refl.
        -- forward. forward.
           hka5d_post. unfold hka5_QD, hka5_PE, hka5_tl, hka5_lv, hka5_cw, hka5_fr, hka5_pkt. simpl app.
           Exists (Z.max top (nonce + 1)) (ht4k_prune (Z.max top (nonce + 1)) (nonce :: S)) bm' 1 nonce.
           entailer!.
           unfold hka5_facts. split; [lia |]. split; [lia |]. split; [lia |].
           split; [apply hcnt_defs3.cnt_inv_prune3; exact H5 |]. rep_lia.
    + destruct (hka5d_top_nok _ _ _ Hok) as [Et EL]. rewrite Et in *. rewrite EL in H5.
      match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
      * apply ENTAIL_refl.
      * forward_if; [exfalso; discriminate |]. forward. entailer!.
      * forward. apply ENTAIL_refl.
      * forward_if (PROP ()
          LOCAL (temp KA._r (Val.of_bool false); temp KA._pred (Vint Int.zero); temp KA._ok (Vint okv);
            temp KA._nonce (Vlong (Int64.repr nonce)); temp KA._enc_len (Vlong (Int64.repr (Zlength c)));
            temp KA._pt_len (Vlong (Int64.repr 0)); temp KA._pkt pkt; temp KA._pt_out po; temp KA._ref_pt rp;
            temp KA._i (Vlong (Int64.repr i)); temp KA._steps (Vlong (Int64.repr steps));
            temp KA._have_auth (Vint (Int.repr ha)); temp KA._last_nonce (Vlong (Int64.repr ln));
            lvar KA._rc ht4k_trc vrc; lvar KA._wm ht4k_twm vwm; lvar KA._snap ht4k_tsnap vsnap;
            lvar KA._key (tarray tuchar 32) vkey; gvars gv)
          SEP (data_at Tsh ht4k_trc (ht4k_rc top bm') vrc; ht4k_wm Tsh top S vwm;
            malloc_token Ews (tarray tuchar (16 + Zlength c)) pkt; data_at Ews (tarray tuchar 16) hdr pkt;
            data_at Ews (tarray tuchar (Zlength c)) (map Vubyte c) (offset_val 16 pkt);
            hka5_mb po; hka5_mb rp; data_at Tsh ht4k_tsnap (ht4k_snap top bm) vsnap;
            data_at Tsh (tarray tuchar 32) (map Vubyte key) vkey; mem_mgr gv; zero_page gv;
            ht4_minusp hka5_mp gv; FR)).
        { exfalso. auto. }
        { forward. hka5d_post. entailer!. }
        match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
        -- apply ENTAIL_refl.
        -- unfold ht4k_wm. Intros wp. forward. forward. forward_if.
           { hka5d_eq_contra. }
           forward. unfold ht4k_wm. Exists wp. entailer!.
        -- forward. apply ENTAIL_refl.
        -- forward. forward.
           hka5d_post. unfold hka5_QD, hka5_PE, hka5_tl, hka5_lv, hka5_cw, hka5_fr, hka5_pkt. simpl app.
           Exists top S bm' 1 nonce.
           entailer!.
           unfold hka5_facts. split; [lia |]. split; [lia |]. split; [lia |].
           split; [exact H5 |]. rep_lia.
Qed.
