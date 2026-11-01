(* law hs_replay_initiation: main's body against its specification (hs_asm.hs_main_spec: the initial globals,
   any postcondition), in the law's world W_hs_replay_initiation.

   main builds the pair (new_pair), sets any clocks, lets A create an initiation and B consume it; if B accepted,
   B may answer (create_response) and begin its session; at any clocks the same message is consumed again and
   gp_assert checks the result is NULL.  The model argument is hri_model.v: B's peer keeps its remote static key,
   precomputed DH and latest timestamp through create_response and begin_session, so the replay decrypts to the
   same timestamp and is rejected. *)
Require WgNoise.proof.assembly.asm_env.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.protocol5.prot_repr5.
Require Import WgNoise.proof.protocol5.prot_specs5.
Require Import WgNoise.proof.harness.hs_common.hs_specs.
Require Import WgNoise.proof.harness.hs_common.hs_worlds.
Require Import WgNoise.proof.harness.hs_common.hs_globals.
Require Import WgNoise.proof.harness.hs_common.hs_asm.
Require Import WgNoise.proof.harness.hs_replay_initiation.hri_model.
Require Import WgNoise.proof.harness.hs_replay_initiation.hri_close.
Require WgNoise.contracts.hs_replay_initiation.
Require WgNoise.harness.hs_replay_initiation.code.
Local Open Scope logic.

Module HR := WgNoise.harness.hs_replay_initiation.code.
Definition hri_prog := WgNoise.contracts.hs_replay_initiation.whole_prog.

(* the specifications of the harness's own functions main reaches (its copies of the hs_laws.h helpers) *)
Definition hri_Gl (x25519: list byte -> list byte -> list byte) : funspecs :=
  [any_u64_spec; any_clocks_spec; new_device_spec x25519; new_peer_spec x25519; new_pair_spec x25519].

(* the imports: the environment's functions the harness calls, and the protocol's specifications *)
Definition hri_Il (x25519: list byte -> list byte -> list byte)
    (aead_enc: list byte -> Z -> list byte -> list byte -> list byte)
    (aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte)) (W: compspecs) : funspecs :=
  [nondet_u8_spec; nondet_u32_spec; @asm_env.nondet_bytes_spec W; gp_assert_spec] ++
  prot_G5 x25519 aead_enc aead_dec W.

Definition hri_G x25519 aead_enc aead_dec : funspecs :=
  hri_Il x25519 aead_enc aead_dec W_hs_replay_initiation ++ hs_main_spec hri_prog :: hri_Gl x25519.

(* main's locals: the world's data_at_ of their structs is the one of the specifications' compspecs *)
#[local] Instance hri_cce_N : change_composite_env Noise.CS W_hs_replay_initiation.
Proof. make_cs_preserve Noise.CS W_hs_replay_initiation. Defined.
#[local] Instance hri_cce_H : change_composite_env CSh W_hs_replay_initiation.
Proof. make_cs_preserve CSh W_hs_replay_initiation. Defined.

Lemma hri_conv_pair sh p : @data_at_ CSh sh t_pair p = @data_at_ W_hs_replay_initiation sh t_pair p.
Proof. rewrite (@data_at__change_composite CSh W_hs_replay_initiation _ sh t_pair); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hri_conv_init sh p : @data_at_ Noise.CS sh t_init p = @data_at_ W_hs_replay_initiation sh t_init p.
Proof. rewrite (@data_at__change_composite Noise.CS W_hs_replay_initiation _ sh t_init); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hri_conv_resp sh p : @data_at_ Noise.CS sh t_resp p = @data_at_ W_hs_replay_initiation sh t_resp p.
Proof. rewrite (@data_at__change_composite Noise.CS W_hs_replay_initiation _ sh t_resp); [reflexivity | prove_cs_preserve_type]. Qed.

(* a list of one peer *)
Lemma hri_peers1 a sh P : peer_rep5 sh a P |-- peers_rep5 [(a, sh, P)].
Proof. unfold peers_rep5. simpl. rewrite sepcon_emp. apply derives_refl. Qed.

Lemma hri_peers1' a sh P : peers_rep5 [(a, sh, P)] |-- peer_rep5 sh a P.
Proof. unfold peers_rep5. simpl. rewrite sepcon_emp. apply derives_refl. Qed.

(* the test of consume_initiation's result against NULL: B's peer is a valid pointer *)
Lemma hri_tc_peer sh p P R :
  readable_share sh -> peer_rep5 sh p P * R |-- denote_tc_test_eq p (Vlong (Int64.repr 0)).
Proof.
  intros Hsh. unfold peer_rep5. Intros.
  apply denote_tc_test_eq_split; [|apply valid_pointer_null].
  do 11 apply sepcon_valid_pointer1. apply field_at_valid_ptr0; auto.
  all: first [apply readable_nonidentity; auto | simpl; lia].
Qed.

(* B's peer is not NULL *)
Lemma hri_pair_bp_nn p : @field_compatible CSh t_pair [] p -> pair_bp p <> nullval.
Proof.
  intros Hf E. unfold pair_bp in E. rewrite field_compatible_field_address in E by auto with field_compatible.
  destruct p; try contradiction; discriminate.
Qed.

(* a peer's address is a struct wg_peer's *)
Lemma hri_peer_fc sh p P R : peer_rep5 sh p P * R |-- !! @field_compatible Noise.CS t_peer [] p.
Proof. unfold peer_rep5. Intros. apply prop_right; auto. Qed.

(* no keypairs *)
Lemma hri_kp_nil_eq cs : keypairs_rep cs [] = emp.
Proof. reflexivity. Qed.
Lemma hri_kp_nil cs : emp |-- keypairs_rep cs [].
Proof. rewrite hri_kp_nil_eq. apply derives_refl. Qed.

(* main's postcondition (any) in VST's canonical form *)
Lemma hri_post_canon {Espec: OracleKind} {cs: compspecs} Delta P c gv F :
  semax Delta P c (frame_ret_assert (function_body_ret_assert tint (PROP () LOCAL () SEP (TT))) F) ->
  semax Delta P c (frame_ret_assert (function_body_ret_assert tint (hs_post gv)) F).
Proof.
  intros H. eapply semax_post; [| | | | apply H]; intros; simpl; intros rho; apply andp_left2;
    try apply derives_refl.
  apply sepcon_derives; [| apply derives_refl]. revert rho. apply bind_ret_derives. intros rho. apply TT_right.
Qed.

(* new_pair's tables: each holds its peer's handshake entry *)
Lemma hri_table_hs sh pa : hs_in_pool (hs_table sh pa) pa.
Proof.
  unfold hs_in_pool, t_entry, hs_table. cbn. destruct (EqDec_val (hs_addr pa) (hs_addr pa)); [|congruence].
  eexists; split; reflexivity.
Qed.

Lemma hri_table_pool sh pa : hri_in_pool (hs_table sh pa) (hs_addr pa) sh.
Proof.
  unfold hri_in_pool, hs_table. cbn. destruct (EqDec_val (hs_addr pa) (hs_addr pa)); [|congruence].
  eexists; reflexivity.
Qed.

(* the stack frame at a return: the pair, closed by hri_pair_close, and the two messages *)
Lemma hri_ret v_p v_message v_response DA DB TA TB ka kb PA PB Mo Mr :
  @field_compatible CSh t_pair [] v_p ->
  hri_in_pool TA (hs_addr (pair_ap v_p)) Tsh -> hri_in_pool TB (hs_addr (pair_bp v_p)) Tsh ->
  device_rep5 Tsh (pair_a v_p) DA * device_rep5 Tsh (pair_b v_p) DB *
  itable Tsh (pair_ai v_p) TA * itable Tsh (pair_bi v_p) TB *
  ptable Tsh (pair_ak v_p) ka * ptable Tsh (pair_bk v_p) kb *
  peer_rep5 Tsh (pair_ap v_p) PA * peer_rep5 Tsh (pair_bp v_p) PB *
  init_opt_rep Tsh v_message Mo * resp_opt_rep Tsh v_response Mr
  |-- @data_at_ W_hs_replay_initiation Tsh t_pair v_p * @data_at_ W_hs_replay_initiation Tsh t_init v_message *
      @data_at_ W_hs_replay_initiation Tsh t_resp v_response * TT.
Proof.
  intros Hf HA HB.
  destruct hri_close_all as (Ci & Cr & Cp).
  rewrite <- hri_conv_pair, <- hri_conv_init, <- hri_conv_resp.
  sep_apply (Cp Tsh v_p DA DB TA TB ka kb PA PB Hf HA HB).
  assert (Hm: init_opt_rep Tsh v_message Mo |-- @data_at_ Noise.CS Tsh t_init v_message)
    by (destruct Mo; [apply Ci | apply derives_refl]).
  assert (Hr: resp_opt_rep Tsh v_response Mr |-- @data_at_ Noise.CS Tsh t_resp v_response)
    by (destruct Mr; [apply Cr | apply derives_refl]).
  sep_apply Hm. sep_apply Hr. cancel.
Qed.

Section Main.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
#[local] Existing Instance W_hs_replay_initiation.

Lemma hri_main_body :
  semax_body (QPvarspecs hri_prog) (hri_G x25519 aead_enc aead_dec) HR.f_main (hs_main_spec hri_prog).
Proof.
  unfold hs_main_spec, QPmain_spec_ext', NDmk_funspec.
  split3; [reflexivity | reflexivity | ]. intros Espec DTL gv.
  eapply (main_pre_InitGpred (hs_globals0 gv));
    [apply hs_init_globals_replay_initiation | reflexivity
    | apply Forall_forall; intros x Hx; vm_compute in Hx; repeat destruct Hx as [Hx|Hx]; try contradiction; subst x; vm_compute; exact I | ].
  process_stackframe_of.
  unfold hs_globals0.
  sep_apply (create_mem_mgr gv).
  change (Tstruct HR._pair noattr) with t_pair.
  change (Tstruct HR._message_handshake_initiation noattr) with t_init.
  change (Tstruct HR._message_handshake_response noattr) with t_resp.
  rewrite <- hri_conv_pair, <- hri_conv_init, <- hri_conv_resp.
  simpl fn_body. apply hri_post_canon. abbreviate_semax.
  (* new_pair(&p); any_clocks(); *)
  forward_call (gv, Tsh, v_p, zeros32, zeros32, Int64.zero).
  Intros vr. destruct vr as [[araw braw] psk]. cbn [fst snd] in *.
  forward_call (gv, hs_shim0, hs_w0).
  Intros vc. destruct vc as [[b1 rs1] rn1]. cbn [fst snd] in *.
  unfold hs_pair. Intros.
  (* A's initiation *)
  change (@data_at_ W_hs_replay_initiation Tsh t_init v_message) with (init_opt_rep Tsh v_message None).
  forward_call (gv, shim_clocks hs_shim0 b1 rs1 rn1, hs_w0, Int64.zero, Tsh, v_message, @None init_msg, Tsh,
    pair_ap v_p, pair_peerA x25519 v_p araw braw psk, Tsh, pair_a v_p, pair_devA x25519 v_p araw, Tsh,
    hs_table Tsh (pair_ap v_p)).
  { entailer!. unfold pair_ap, hs_addr. rewrite field_compatible_field_address by auto with field_compatible.
    simpl. destruct v_p; try contradiction; simpl. f_equal. }
  { apply hri_table_hs. }
  Intros vret. destruct vret as [r1 idx1]. cbn [fst snd].
  destruct (ci_res x25519 aead_enc (pair_devA x25519 v_p araw) (pair_peerA x25519 v_p araw braw psk) (init_of None)
              (shim_clocks hs_shim0 b1 rs1 rn1) r1 idx1) as [[ok1 M1] HA1] eqn:HCI.
  cbn [fst snd]. change (d_itab (pair_devA x25519 v_p araw)) with (pair_ai v_p).
  forward_if.
  { (* A's initiation failed: return *)
    destruct ok1; [discriminate|]. forward.
    change (Tstruct HR._pair noattr) with t_pair.
    change (Tstruct HR._message_handshake_initiation noattr) with t_init.
    change (Tstruct HR._message_handshake_response noattr) with t_resp.
    change (@data_at_ Noise.CS Tsh t_resp v_response) with (resp_opt_rep Tsh v_response None).
    sep_apply (hri_ret v_p v_message v_response (pair_devA x25519 v_p araw) (pair_devB x25519 v_p braw) _ _
      (pair_ap v_p) (pair_bp v_p) (p_set_hs (pair_peerA x25519 v_p araw braw psk) HA1)
      (pair_peerB x25519 v_p araw braw psk) (opt_after false None M1) (@None resp_msg) H4
      (hri_table_pool Tsh (pair_ap v_p)) (hri_table_pool Tsh (pair_bp v_p))).
    cancel. }
  destruct ok1; [|discriminate]. cbn [opt_after init_opt_rep].
  (* B consumes it *)
  set (S2 := if id_has (d_id (pair_devA x25519 v_p araw))
             then shim_u32 (shim_draw (shim_clocks hs_shim0 b1 rs1 rn1) r1) idx1
             else shim_clocks hs_shim0 b1 rs1 rn1).
  set (PB0 := pair_peerB x25519 v_p araw braw psk).
  sep_apply (hri_peers1 (pair_bp v_p) Tsh PB0).
  forward_call (gv, S2, hs_w0, Int64.zero, Tsh, v_message, M1, Tsh, pair_b v_p, pair_devB x25519 v_p braw, Tsh,
    pair_bp v_p, [(pair_bp v_p, Tsh, PB0)]).
  { entailer!. unfold pair_b. rewrite field_compatible_field_address by auto with field_compatible.
    simpl. destruct v_p; try contradiction; simpl. f_equal. }
  { unfold peers_wf, peers_refs_ok, PB0. cbn.
    split; [constructor; [apply writable_share_top | constructor]|].
    split; [auto|]. split; (apply Forall_cons; [|apply Forall_nil]).
    - cbv [pair_peerB hs_peer0 prot_specs5.hs_initial prot_specs4.hs_initial p_hs hs_lic p_refs].
      rewrite Int64.signed_zero. rep_lia.
    - cbv [pair_peerB hs_peer0 prot_specs5.hs_initial prot_specs4.hs_initial p_hs hs_lic p_refs].
      rewrite Int.unsigned_one. rep_lia. }
  change (d_ptab (pair_devB x25519 v_p braw)) with (pair_bk v_p).
  destruct (cin_res x25519 aead_dec (pair_devB x25519 v_p braw) [(pair_bp v_p, Tsh, PB0)] M1 S2)
    as [[a PB1]|] eqn:HCN; cbn [peer_result peers_after].
  2:{ (* B rejected it: return *)
    forward_if.
    2:{ exfalso; apply H8; reflexivity. }
    forward. sep_apply (hri_peers1' (pair_bp v_p) Tsh PB0).
    change (Tstruct HR._pair noattr) with t_pair.
    change (Tstruct HR._message_handshake_initiation noattr) with t_init.
    change (Tstruct HR._message_handshake_response noattr) with t_resp.
    change (@data_at_ Noise.CS Tsh t_resp v_response) with (resp_opt_rep Tsh v_response None).
    change (init_rep5 Tsh v_message M1) with (init_opt_rep Tsh v_message (Some M1)).
    sep_apply (hri_ret v_p v_message v_response (pair_devA x25519 v_p araw) (pair_devB x25519 v_p braw)
      (t_insert (hs_table Tsh (pair_ap v_p)) (hs_addr (pair_ap v_p)) idx1) (hs_table Tsh (pair_bp v_p))
      (pair_ap v_p) (pair_bp v_p) (p_set_hs (pair_peerA x25519 v_p araw braw psk) HA1)
      PB0 (Some M1) (@None resp_msg) H4
      (hri_in_pool_insert _ _ _ _ _ (hri_table_pool Tsh (pair_ap v_p))) (hri_table_pool Tsh (pair_bp v_p))).
    cancel. }
  (* B accepted it: the accepted peer is B's peer for A, with a new handshake H1 *)
  assert (HCN' := HCN). unfold cin_res, prot_specs4.cin_res in HCN'.
  destruct (hri_accept_peer x25519 aead_dec _ _ _ _ _ _ HCN') as (sh1 & P1 & H1' & HIn & Hz & -> & Hrs & Hss & Hlic).
  destruct HIn as [HIn|[]]. inversion HIn; subst a sh1 P1; clear HIn.
  cbn [supd]. rewrite if_true by auto.
  sep_apply (hri_peers1' (pair_bp v_p) Tsh (p_set_hs (p_set_refs PB0 (rc_add1 (p_refs PB0))) H1')).
  forward_if.
  { eapply derives_trans; [|apply (hri_tc_peer Tsh (pair_bp v_p) (p_set_hs (p_set_refs PB0 (rc_add1 (p_refs PB0))) H1') TT); auto]. cancel. }
  { exfalso; exact (hri_pair_bp_nn v_p H4 H8). }
  set (PB1 := p_set_hs (p_set_refs PB0 (rc_add1 (p_refs PB0))) H1').
  (* B answers, or not *)
  forward_call tt. Intros b3.
  forward_if (EX b4: bool, EX PB2: peer, EX TB2: tstate, EX S3: shim, EX Mr: option resp_msg,
    PROP (hri_key (p_hs PB2) = hri_key H1'; hs_lic (p_hs PB2) = hs_lic H1'; p_refs PB2 = rc_add1 (p_refs PB0);
          p_device PB2 = pair_b v_p; p_cur PB2 = nullval; p_prev PB2 = nullval; p_next PB2 = nullval;
          p_pknext PB2 = nullval; hs_in_pool TB2 (pair_bp v_p); hri_in_pool TB2 (hs_addr (pair_bp v_p)) Tsh)
    LOCAL (temp HR._t'4 (Val.of_bool b4); lvar HR._response t_resp v_response; lvar HR._message t_init v_message;
           lvar HR._p t_pair v_p; gvars gv)
    SEP (peer_rep5 Tsh (pair_bp v_p) PB2; itable Tsh (pair_bi v_p) TB2; shim_state4 gv S3 hs_w0;
         resp_opt_rep Tsh v_response Mr; init_rep5 Tsh v_message M1;
         device_rep5 Tsh (pair_b v_p) (pair_devB x25519 v_p braw); ptable Tsh (pair_bk v_p) (pair_bp v_p);
         noise_globals gv Int64.zero; wg_consts5 gv;
         peer_rep5 Tsh (pair_ap v_p) (p_set_hs (pair_peerA x25519 v_p araw braw psk) HA1);
         device_rep5 Tsh (pair_a v_p) (pair_devA x25519 v_p araw);
         itable Tsh (pair_ai v_p) (t_insert (hs_table Tsh (pair_ap v_p)) (hs_addr (pair_ap v_p)) idx1);
         ptable Tsh (pair_ak v_p) (pair_ap v_p); mem_mgr gv; TT; has_ext tt)).
  { change (@data_at_ Noise.CS Tsh t_resp v_response) with (resp_opt_rep Tsh v_response None).
    forward_call (gv, S2, hs_w0, Tsh, v_response, @None resp_msg, Tsh, pair_bp v_p, PB1, Tsh, pair_b v_p,
      pair_devB x25519 v_p braw, Tsh, hs_table Tsh (pair_bp v_p)).
    { entailer!. unfold pair_bp, hs_addr. rewrite field_compatible_field_address by auto with field_compatible.
      simpl. destruct v_p; try contradiction; simpl. f_equal. }
    { apply hri_table_hs. }
    Intros vret. destruct vret as [r2 idx2]. cbn [fst snd].
    destruct (cr_res x25519 aead_enc PB1 (resp_of None) r2 idx2) as [[ok2 Mr2] HB2] eqn:HCR. cbn [fst snd].
    change (d_itab (pair_devB x25519 v_p braw)) with (pair_bi v_p).
    forward.
    assert (HK2 := hri_cr_keeps x25519 aead_enc (p_hs PB1) (resp_of None) r2 idx2).
    unfold cr_res, prot_specs4.cr_res in HCR. rewrite HCR in HK2. cbn [snd] in HK2. destruct HK2 as [HK2 HL2].
    Exists ok2 (p_set_hs PB1 HB2)
      (if ok2 then t_insert (hs_table Tsh (pair_bp v_p)) (hs_addr (pair_bp v_p)) idx2 else hs_table Tsh (pair_bp v_p))
      (if Int.eq (hs_state (p_hs PB1)) HS_CONSUMED_INITIATION
       then if ok2 then shim_u32 (shim_draw S2 r2) idx2 else shim_draw S2 r2 else S2)
      (opt_after ok2 None Mr2).
    entailer!.
    destruct ok2; (split; [|split]); auto using hri_hs_in_pool_insert, hri_in_pool_insert, hri_table_hs, hri_table_pool. }
  { forward. Exists false PB1 (hs_table Tsh (pair_bp v_p)) S2 (@None resp_msg).
    entailer!. split; [apply hri_table_hs | apply hri_table_pool]. }
  Intros b4 PB2 TB2 S3 Mr.
  forward_if (EX b6: bool,
    PROP () LOCAL (temp HR._t'6 (Val.of_bool b6); lvar HR._response t_resp v_response;
                   lvar HR._message t_init v_message; lvar HR._p t_pair v_p; gvars gv)
    SEP (peer_rep5 Tsh (pair_bp v_p) PB2; itable Tsh (pair_bi v_p) TB2; shim_state4 gv S3 hs_w0;
         resp_opt_rep Tsh v_response Mr; init_rep5 Tsh v_message M1;
         device_rep5 Tsh (pair_b v_p) (pair_devB x25519 v_p braw); ptable Tsh (pair_bk v_p) (pair_bp v_p);
         noise_globals gv Int64.zero; wg_consts5 gv;
         peer_rep5 Tsh (pair_ap v_p) (p_set_hs (pair_peerA x25519 v_p araw braw psk) HA1);
         device_rep5 Tsh (pair_a v_p) (pair_devA x25519 v_p araw);
         itable Tsh (pair_ai v_p) (t_insert (hs_table Tsh (pair_ap v_p)) (hs_addr (pair_ap v_p)) idx1);
         ptable Tsh (pair_ak v_p) (pair_ap v_p); mem_mgr gv; TT; has_ext tt)).
  { forward_call tt. Intros b7. forward.
    Exists (negb (Int.eq (Int.and (Int.repr b7) (Int.repr 1)) Int.zero)). entailer!.
    match goal with |- context [Int.eq ?x Int.zero] => destruct (Int.eq x Int.zero) end; reflexivity. }
  { forward. Exists false. entailer!. }
  Intros b6.
  forward_if (EX PB3: peer, EX TB3: tstate, EX S4: shim, EX w4: list int64, EX kc4: int64,
              EX KS: list (val * keypair),
    PROP (hri_key (p_hs PB3) = hri_key H1'; hs_lic (p_hs PB3) = hs_lic H1'; p_refs PB3 = rc_add1 (p_refs PB0);
          p_device PB3 = pair_b v_p; p_pknext PB3 = nullval; hri_in_pool TB3 (hs_addr (pair_bp v_p)) Tsh)
    LOCAL (lvar HR._response t_resp v_response; lvar HR._message t_init v_message; lvar HR._p t_pair v_p; gvars gv)
    SEP (peer_rep5 Tsh (pair_bp v_p) PB3; itable Tsh (pair_bi v_p) TB3; shim_state4 gv S4 w4;
         noise_globals gv kc4; keypairs_rep W_hs_replay_initiation KS;
         resp_opt_rep Tsh v_response Mr; init_rep5 Tsh v_message M1;
         device_rep5 Tsh (pair_b v_p) (pair_devB x25519 v_p braw); ptable Tsh (pair_bk v_p) (pair_bp v_p);
         wg_consts5 gv;
         peer_rep5 Tsh (pair_ap v_p) (p_set_hs (pair_peerA x25519 v_p araw braw psk) HA1);
         device_rep5 Tsh (pair_a v_p) (pair_devA x25519 v_p araw);
         itable Tsh (pair_ai v_p) (t_insert (hs_table Tsh (pair_ap v_p)) (hs_addr (pair_ap v_p)) idx1);
         ptable Tsh (pair_ak v_p) (pair_ap v_p); mem_mgr gv; TT; has_ext tt)).
  { (* B begins its session *)
    assert_PROP (@field_compatible Noise.CS t_peer [] (pair_bp v_p)) as Hfb.
    { go_lower. eapply derives_trans; [|apply (hri_peer_fc Tsh (pair_bp v_p) PB2 TT)]. cancel. }
    sep_apply (hri_kp_nil W_hs_replay_initiation).
    forward_call (gv, S3, hs_w0, Int64.zero, @nil (val * keypair), TB2, Tsh, pair_bp v_p, PB2, Tsh, pair_b v_p,
      pair_devB x25519 v_p braw, Tsh).
    { entailer!. unfold pair_bp, hs_addr, kps_addr.
      rewrite field_compatible_field_address by auto with field_compatible.
      simpl. destruct v_p; try contradiction; simpl. f_equal. }
    { split; [split; constructor|].
      unfold slots_ok. rewrite H14, H15, H16. split; [repeat constructor; left; reflexivity|].
      cbn. destruct (EqDec_val nullval nullval); [constructor | congruence]. }
    Intros k.
    change (d_itab (pair_devB x25519 v_p braw)) with (pair_bi v_p).
    pose proof (hri_bs_keeps PB2 (hs_addr (pair_bp v_p)) k Int64.zero (mkKW [] TB2 S3)) as HK3.
    cbv zeta in HK3. destruct HK3 as (K1 & K2 & K3 & K4 & K5).
    assert (HP3 := hri_in_pool_bs PB2 (hs_addr (pair_bp v_p)) k Int64.zero TB2 S3 (hs_addr (pair_bp v_p)) Tsh
                     H14 H15 H16 (fun Hk => proj1 (H22 Hk)) H19).
    unfold bs_res, prot_specs4.bs_res in *.
    Exists (snd (fst (fst (begin_session_model PB2 (hs_addr (pair_bp v_p)) k Int64.zero (mkKW [] TB2 S3)))))
      (kw_T (snd (fst (begin_session_model PB2 (hs_addr (pair_bp v_p)) k Int64.zero (mkKW [] TB2 S3)))))
      (kw_S (snd (fst (begin_session_model PB2 (hs_addr (pair_bp v_p)) k Int64.zero (mkKW [] TB2 S3)))))
      (begin_session_warn PB2 (hs_addr (pair_bp v_p)) k Int64.zero {| kw_KS := []; kw_T := TB2; kw_S := S3 |} hs_w0)
      (snd (begin_session_model PB2 (hs_addr (pair_bp v_p)) k Int64.zero (mkKW [] TB2 S3)))
      (kw_KS (snd (fst (begin_session_model PB2 (hs_addr (pair_bp v_p)) k Int64.zero (mkKW [] TB2 S3))))).
    entailer!.
    }
  { forward. Exists PB2 TB2 S3 hs_w0 Int64.zero (@nil (val * keypair)). entailer!.
    }
  Intros PB3 TB3 S4 w4 kc4 KS.
  (* the same message again, at any clocks *)
  forward_call (gv, S4, w4).
  Intros vc. destruct vc as [[b2 rs2] rn2]. cbn [fst snd].
  sep_apply (hri_peers1 (pair_bp v_p) Tsh PB3).
  forward_call (gv, shim_clocks S4 b2 rs2 rn2, w4, kc4, Tsh, v_message, M1, Tsh, pair_b v_p,
    pair_devB x25519 v_p braw, Tsh, pair_bp v_p, [(pair_bp v_p, Tsh, PB3)]).
  { entailer!. unfold pair_b. rewrite field_compatible_field_address by auto with field_compatible.
    simpl. destruct v_p; try contradiction; simpl. f_equal. }
  { unfold peers_wf, peers_refs_ok. cbn.
    split; [constructor; [apply writable_share_top | constructor]|].
    split; [split; [reflexivity | exact H24]|].
    split; (apply Forall_cons; [|apply Forall_nil]).
    - rewrite H21. assert (Hb: s_boot S2 = b1) by (unfold S2; destruct (id_has _); reflexivity).
      destruct Hlic as [-> | ->].
      + rewrite Hb, Int64.signed_eq_unsigned by rep_lia. rep_lia.
      + cbv [PB0 pair_peerB hs_peer0 prot_specs5.hs_initial prot_specs4.hs_initial p_hs hs_lic].
        rewrite Int64.signed_zero. rep_lia.
    - rewrite H22. vm_compute. split; reflexivity. }
  (* the replay is rejected *)
  assert (Hrep: cin_res x25519 aead_dec (pair_devB x25519 v_p braw) [(pair_bp v_p, Tsh, PB3)] M1
                (shim_clocks S4 b2 rs2 rn2) = None).
  { unfold cin_res, prot_specs4.cin_res. eapply hri_replay; [exact HCN'|]. rewrite H20. reflexivity. }
  rewrite Hrep. cbn [peer_result peers_after].
  forward_call (Int.one).
  forward.
  sep_apply (hri_peers1' (pair_bp v_p) Tsh PB3).
  change (Tstruct HR._pair noattr) with t_pair.
  change (Tstruct HR._message_handshake_initiation noattr) with t_init.
  change (Tstruct HR._message_handshake_response noattr) with t_resp.
  change (init_rep5 Tsh v_message M1) with (init_opt_rep Tsh v_message (Some M1)).
  change (d_ptab (pair_devB x25519 v_p braw)) with (pair_bk v_p).
  sep_apply (hri_ret v_p v_message v_response (pair_devA x25519 v_p araw) (pair_devB x25519 v_p braw)
    (t_insert (hs_table Tsh (pair_ap v_p)) (hs_addr (pair_ap v_p)) idx1) TB3
    (pair_ap v_p) (pair_bp v_p) (p_set_hs (pair_peerA x25519 v_p araw braw psk) HA1)
    PB3 (Some M1) Mr H4
    (hri_in_pool_insert _ _ _ _ _ (hri_table_pool Tsh (pair_ap v_p))) H25).
  cancel.
Qed.

End Main.
