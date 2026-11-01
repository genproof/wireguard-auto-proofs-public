(* The law hs_begin_session_state: main's body. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.proof.assembly.asm_env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol5.prot_repr5.
Require Import WgNoise.proof.protocol5.prot_prog5.
Require Import WgNoise.proof.harness.hs_common.hs_specs.
Require Import WgNoise.proof.harness.hs_common.hs_worlds.
Require Import WgNoise.proof.harness.hs_common.hs_globals.
Require Import WgNoise.proof.harness.hs_common.hs_asm.
Require Import WgNoise.proof.harness.hs_begin_session_state.hsbs_model.
Require Import WgNoise.proof.harness.hs_begin_session_state.hsbs_spec.
Require Import WgNoise.proof.harness.hs_begin_session_state.hsbs_conv.
Require Import WgNoise.proof.harness.hs_begin_session_state.hsbs_lemmas.
Local Open Scope logic.

#[local] Instance hbs_cce_H : change_composite_env CSh W_hbs.
Proof. make_cs_preserve CSh W_hbs. Defined.

Lemma hbs_conv_pair sh p : @data_at_ CSh sh t_pair p = @data_at_ W_hbs sh t_pair p.
Proof. rewrite (@data_at__change_composite CSh W_hbs _ sh t_pair); [reflexivity | prove_cs_preserve_type]. Qed.

#[local] Existing Instance W_hbs.

(* the harness's `completed`: the state is CREATED_RESPONSE or CONSUMED_RESPONSE *)
Definition hbs_completed (s: int) : bool := orb (Int.eq s HS_CREATED_RESPONSE) (Int.eq s HS_CONSUMED_RESPONSE).

(* main's postcondition (any) in the canonical form VST's return needs *)
Lemma hbs_post_canon {Espec: OracleKind} {cs: compspecs} Delta P c gv F :
  semax Delta P c (frame_ret_assert (function_body_ret_assert tint (PROP () LOCAL () SEP (TT))) F) ->
  semax Delta P c (frame_ret_assert (function_body_ret_assert tint (hs_post gv)) F).
Proof.
  intros H. eapply semax_post; [| | | | apply H]; intros; simpl; intros rho; apply andp_left2;
    try apply derives_refl.
  apply sepcon_derives; [| apply derives_refl]. destruct vl; simpl; unfold hs_post;
    [apply andp_derives; [apply derives_refl | apply TT_right] | apply derives_refl].
Qed.

(* the definedness of x == x for a slot x (hbs_test_eq_self) *)
Ltac hbs_tc tab :=
  match goal with |- _ |-- denote_tc_test_eq ?x ?x =>
    match goal with Hk: kps_in_pool ?T _ ?KS |- _ =>
      eapply derives_trans; [| apply (hbs_test_eq_self Tsh tab T _ KS x TT Hk); assumption];
      cbn [d_itab pair_devA hs_dev]; cancel
    end
  end.

Section Main.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).

(* the loop invariant: A's peer in any state P, its keypairs KS and its table T satisfying begin_session's
   requirements (bsw_inv), any shim state, any keypair counter; the rest of struct pair as new_pair left it *)
Definition hbs_inv (gv: globals) (v_p: val) (araw braw psk: list byte) : environ -> mpred :=
  let ap := pair_ap v_p in
  EX P: peer, EX KS: list (val * keypair), EX T: tstate, EX S: shim, EX w: list int64, EX kc: int64,
    PROP (bsw_inv ap Tsh P KS T; p_device P = pair_a v_p)
    LOCAL (temp HBS._slots (kps_addr ap); temp HBS._h (hs_addr ap);
           lvar HBS._p (Tstruct HBS._pair noattr) v_p; gvars gv)
    SEP (device_rep5 Tsh (pair_a v_p) (pair_devA x25519 v_p araw);
         device_rep5 Tsh (pair_b v_p) (pair_devB x25519 v_p braw);
         itable Tsh (pair_ai v_p) T;
         itable Tsh (pair_bi v_p) (hs_table Tsh (pair_bp v_p));
         ptable Tsh (pair_ak v_p) ap;
         ptable Tsh (pair_bk v_p) (pair_bp v_p);
         peer_rep5 Tsh ap P;
         peer_rep5 Tsh (pair_bp v_p) (pair_peerB x25519 v_p araw braw psk);
         keypairs_rep W_hbs KS;
         noise_globals gv kc; wg_consts5 gv; mem_mgr gv;
         shim_state4 gv S w; TT; has_ext tt).

Lemma hbs_main_body :
  x25519_props x25519 -> aead_props aead_enc aead_dec ->
  @semax_body (QPvarspecs hbs_prog) (hbs_Gmain x25519 aead_enc aead_dec) W_hbs HBS.f_main (hs_main_spec hbs_prog).
Proof.
  intros Hx Ha.
  unfold hs_main_spec, QPmain_spec_ext', NDmk_funspec.
  split3; [reflexivity | reflexivity | ]. intros Espec DTL gv.
  eapply (main_pre_InitGpred (hs_globals0 gv));
    [apply hs_init_globals_begin_session_state | reflexivity
    | apply Forall_forall; intros x Hx'; vm_compute in Hx'; repeat destruct Hx' as [Hx'|Hx']; try contradiction; subst x; vm_compute; exact I | ].
  process_stackframe_of.
  unfold hs_globals0. rewrite <- hbs_conv_pair.
  sep_apply (create_mem_mgr gv).
  cbv beta iota delta [fn_body HBS.f_main].
  apply hbs_post_canon.
  abbreviate_semax.
  forward_call (gv, Tsh, v_p, zeros32, zeros32, Int64.zero).
  Intros vret. destruct vret as [[araw braw] psk]. cbn [fst snd].
  unfold hs_pair. Intros.
  forward. forward.
  forward_loop (hbs_inv gv v_p araw braw psk) break: (hbs_inv gv v_p araw braw psk).
  { Exists (pair_peerA x25519 v_p araw braw psk) (@nil (val * keypair)) (hs_table Tsh (pair_ap v_p)) hs_shim0 hs_w0
      Int64.zero.
    entailer!.
    split3; [apply bsw_inv_init; reflexivity | |].
    all: unfold kps_addr, hs_addr, pair_ap, field_address; rewrite if_true by auto with field_compatible;
      destruct v_p; try contradiction; reflexivity. }
  - (* the body *)
    unfold hbs_inv. Intros P KS T S w kc.
    rewrite (hbs_peer_split Tsh (pair_ap v_p) P). Intros. unfold hbs_hsW, hbs_kpsW. Intros lk.
    forward_call tt. Intros st.
    forward.
    forward_call tt. Intros ri.
    forward.
    assert_PROP (field_compatible t_hs [StructField I._ephemeral_private] (hs_addr (pair_ap v_p)) /\
                 field_compatible t_hs [StructField I._remote_ephemeral] (hs_addr (pair_ap v_p)) /\
                 field_compatible t_hs [StructField I._hash] (hs_addr (pair_ap v_p)) /\
                 field_compatible t_hs [StructField I._chaining_key] (hs_addr (pair_ap v_p)) /\
                 field_compatible t_hs [StructField I._latest_timestamp] (hs_addr (pair_ap v_p)))
      as HF by entailer!.
    destruct HF as (F1 & F2 & F3 & F4 & F5).
    rewrite (field_at_data_at Tsh t_hs [StructField I._ephemeral_private]).
    forward_call (field_address t_hs [StructField I._ephemeral_private] (hs_addr (pair_ap v_p)), 32, Tsh).
    Intros eph.
    rewrite (field_at_data_at Tsh t_hs [StructField I._remote_ephemeral]).
    forward_call (field_address t_hs [StructField I._remote_ephemeral] (hs_addr (pair_ap v_p)), 32, Tsh).
    Intros reph.
    rewrite (field_at_data_at Tsh t_hs [StructField I._hash]).
    forward_call (field_address t_hs [StructField I._hash] (hs_addr (pair_ap v_p)), 32, Tsh).
    Intros hh.
    rewrite (field_at_data_at Tsh t_hs [StructField I._chaining_key]).
    forward_call (field_address t_hs [StructField I._chaining_key] (hs_addr (pair_ap v_p)), 32, Tsh).
    Intros ck.
    rewrite (field_at_data_at Tsh t_hs [StructField I._latest_timestamp]).
    forward_call (field_address t_hs [StructField I._latest_timestamp] (hs_addr (pair_ap v_p)), 12, Tsh).
    Intros ts.
    forward.
    forward_if (temp HBS._t'4 (Vint (if hbs_completed (Int.repr st) then Int.one else Int.zero))).
    { forward. entailer!. }
    { forward. forward. entailer!.
      unfold hbs_completed, HS_CREATED_RESPONSE, HS_CONSUMED_RESPONSE.
      rewrite (Int.eq_false (Int.repr st) (Int.repr 3))
        by (intro E; apply H19; apply repr_inj_unsigned; [rep_lia | rep_lia | exact E]).
      destruct (zeq st 4) as [-> | n]; simpl; [reflexivity |].
      rewrite Int.eq_false by (intro E; apply n; apply repr_inj_unsigned; [rep_lia | rep_lia | exact E]).
      reflexivity. }
    forward.
    assert_PROP (is_pointer_or_null (p_cur P) /\ is_pointer_or_null (p_prev P) /\ is_pointer_or_null (p_next P))
      as HPN.
    { destruct H3 as (_ & _ & Hsl & _). sep_apply (hbs_slots_ptr W_hbs P KS Hsl). entailer!. }
    destruct HPN as (HPc & HPp & HPn).
    forward. forward. forward.
    rewrite hbs_shim_split. Intros. forward. sep_apply hbs_shim_join.
    sep_apply (hbs_fold Tsh (pair_ap v_p) P lk (Int.repr st) (Int.repr ri) eph reph hh ck ts).
    set (P1 := p_set_hs P (hbs_hs_set (p_hs P) (Int.repr st) (Int.repr ri) (map Byte.repr eph)
                 (map Byte.repr reph) (map Byte.repr hh) (map Byte.repr ck) (map Byte.repr ts))).
    destruct H3 as (Hb1 & Hb2 & Hb3 & Hb4).
    forward_call (gv, S, w, kc, KS, T, Tsh, pair_ap v_p, P1, Tsh, pair_a v_p, pair_devA x25519 v_p araw, Tsh).
    { eapply bsw_hs_in_pool; eassumption. }
    Intros k.
    unfold bs_res, prot_specs4.bs_res.
    pose proof (bsw_inv_step P1 (pair_ap v_p) Tsh k kc KS T S (conj Hb1 (conj Hb2 (conj Hb3 Hb4))) H19) as Hstep.
    destruct (hbs_completed (Int.repr st)) eqn:EC.
    + (* a completed handshake: no check *)
      destruct (begin_session_model P1 (hs_addr (pair_ap v_p)) k kc {| kw_KS := KS; kw_T := T; kw_S := S |})
        as [[[b P2] W2] kc2] eqn:EB.
      cbn [fst snd] in *. destruct Hstep as [Hi2 Hd2].
      forward_if (hbs_inv gv v_p araw braw psk).
      { exfalso. apply Int.one_not_zero. assumption. }
      { forward.
      unfold hbs_inv. Exists P2 (kw_KS W2) (kw_T W2) (kw_S W2)
        (begin_session_warn P1 (hs_addr (pair_ap v_p)) k kc {| kw_KS := KS; kw_T := T; kw_S := S |} w) kc2.
      entailer!; [rewrite Hd2; exact H4 | apply derives_refl]. }
      unfold hbs_inv. Intros P' KS' T' S' w' kc'.
      forward_call tt. Intros c.
      forward_if.
      * forward. unfold hbs_inv. Exists P' KS' T' S' w' kc'. entailer!.
      * forward. unfold hbs_inv. Exists P' KS' T' S' w' kc'. entailer!.
    + (* a call in another state: the checks *)
      unfold hbs_completed in EC. apply orb_false_elim in EC. destruct EC as [E3 E4].
      rewrite (bsw_reject P1 (pair_ap v_p) k kc KS T S E3 E4) in *.
      assert (EW: begin_session_warn P1 (hs_addr (pair_ap v_p)) k kc {| kw_KS := KS; kw_T := T; kw_S := S |} w = w).
      { unfold begin_session_warn. change (hs_state (p_hs P1)) with (Int.repr st). rewrite E3, E4. reflexivity. }
      rewrite EW. cbn [fst snd kw_S kw_KS kw_T] in *.
      forward_if (hbs_inv gv v_p araw braw psk).
      2: { exfalso. match goal with H: _ <> _ |- _ => apply H; reflexivity end. }
      forward_if (temp HBS._t'6 (Vint Int.one)).
      { rewrite hbs_shim_split. Intros. forward. forward. sep_apply hbs_shim_join. entailer!.
        unfold Int64.cmpu. rewrite Int64.eq_true. reflexivity. }
      { exfalso. match goal with H: _ <> _ |- _ => apply H; reflexivity end. }
      forward_call Int.one.
      rewrite (hbs_peer_split Tsh (pair_ap v_p) P1). Intros. unfold hbs_kpsW. Intros lk2.
      change (p_cur P1) with (p_cur P); change (p_prev P1) with (p_prev P); change (p_next P1) with (p_next P).
      destruct Hb3 as [Hsl _]. inversion Hsl as [| ? ? Sc Hsl2]. inversion Hsl2 as [| ? ? Sp Hsl3].
      inversion Hsl3 as [| ? ? Sn _]. clear Hsl Hsl2 Hsl3.
      forward.
      forward_if (temp HBS._t'7 (Vint Int.one)).
      { hbs_tc (pair_ai v_p). }
      { forward. forward.
        { entailer!. hbs_tc (pair_ai v_p). }
        entailer!. rewrite hbs_cmp_self by assumption. reflexivity. }
      { exfalso. match goal with H: _ <> _ |- _ => apply H; reflexivity end. }
      forward_call Int.one.
      forward.
      forward_call Int.one.
      { hbs_tc (pair_ai v_p). }
      { entailer!. rewrite hbs_cmp_self by assumption. reflexivity. }
      { unfold hbs_inv. Exists P1 KS T S w kc.
        rewrite (hbs_peer_split Tsh (pair_ap v_p) P1). unfold hbs_kpsW. Exists lk2.
        destruct Hstep as [Hi1 _]. entailer!. apply derives_refl. }
      unfold hbs_inv. Intros P' KS' T' S' w' kc'.
      forward_call tt. Intros c.
      forward_if.
      * forward. unfold hbs_inv. Exists P' KS' T' S' w' kc'. entailer!.
      * forward. unfold hbs_inv. Exists P' KS' T' S' w' kc'. entailer!.
  - (* after the loop: struct pair is given back, main returns 0 *)
    unfold hbs_inv. Intros P KS T S w kc.
    destruct H3 as [Hb1 _].
    assert (HbB: bsw_hs (hs_table Tsh (pair_bp v_p)) (pair_bp v_p) Tsh).
    { exists (mkEntry (pair_bp v_p) IDX_HANDSHAKE Int.zero). simpl.
      destruct (EqDec_val (hs_addr (pair_bp v_p)) (hs_addr (pair_bp v_p))); [auto | congruence]. }
    sep_apply (hbs_close Tsh v_p (pair_devA x25519 v_p araw) (pair_devB x25519 v_p braw) T
                 (hs_table Tsh (pair_bp v_p)) (pair_ap v_p) (pair_bp v_p) P (pair_peerB x25519 v_p araw braw psk)
                 H2 Hb1 HbB).
    rewrite hbs_conv_pair.
    forward.
    cancel.
Qed.

End Main.
