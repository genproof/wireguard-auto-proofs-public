(* The law hs_session_erases: the body of main (harness/hs_session_erases.c).

   main builds the pair of devices (new_pair), sets any clocks, runs the four handshake steps and stops (returns 0)
   at the first that fails; then it runs begin_session on both sides and checks, for each side whose call
   returned true, that its handshake is erased (erased(), hse_statics.v).  By begin_session's specification
   (prot_specs5.v) the handshake after a successful call is hs_zero of the one before (hse_bs_erases), which is
   erased.  The facts begin_session's precondition asks for (the peer's handshake entry in its table, its device,
   its empty keypair slots) come from the shape of the pair after the four steps (hse_model.v).

   main is proved in the compspecs of its harness (HCS) against its specification in the law's program
   (hs_main_spec: from the initial globals, hs_globals.v), with only its callees in the context; the law's piece
   lifts it into the law's unit.  At each return the stack frame (struct pair, the two messages) is given back
   (hse_close). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import QuickProof.Env.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol5.prot_repr5.
Require Import WgNoise.proof.protocol5.prot_specs5.
Require Import WgNoise.proof.harness.hs_common.hs_specs.
Require Import WgNoise.proof.harness.hs_common.hs_worlds.
Require Import WgNoise.proof.harness.hs_common.hs_close.
Require Import WgNoise.proof.harness.hs_common.hs_globals.
Require Import WgNoise.proof.harness.hs_common.hs_asm.
Require Import WgNoise.proof.harness.hs_session_erases.hse_model.
Require Import WgNoise.proof.harness.hs_session_erases.hse_statics.
Require WgNoise.contracts.hs_session_erases.
Local Open Scope logic.

#[local] Existing Instance HCS.

#[local] Instance hse_cce_N : change_composite_env Noise.CS HCS.
Proof. make_cs_preserve Noise.CS HCS. Defined.
#[local] Instance hse_cce_H : change_composite_env CSh HCS.
Proof. make_cs_preserve CSh HCS. Defined.

(* main's stack frame, from main's compspecs to those of the specifications *)
Lemma hse_conv_pair sh p : @data_at_ HCS sh (Tstruct C._pair noattr) p = @data_at_ CSh sh t_pair p.
Proof. rewrite (@data_at__change_composite CSh HCS _ sh t_pair); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hse_conv_init sh p :
  @data_at_ HCS sh (Tstruct C._message_handshake_initiation noattr) p = @data_at_ Noise.CS sh t_init p.
Proof. rewrite (@data_at__change_composite Noise.CS HCS _ sh t_init); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hse_conv_resp sh p :
  @data_at_ HCS sh (Tstruct C._message_handshake_response noattr) p = @data_at_ Noise.CS sh t_resp p.
Proof. rewrite (@data_at__change_composite Noise.CS HCS _ sh t_resp); [reflexivity | prove_cs_preserve_type]. Qed.

(* the members of struct pair main passes to noise.c, as offsets *)
Lemma hse_addr_a p : @field_compatible CSh t_pair [] p -> pair_a p = offset_val 0 p.
Proof. intros. unfold pair_a. rewrite field_address_offset by auto with field_compatible. reflexivity. Qed.
Lemma hse_addr_b p : @field_compatible CSh t_pair [] p -> pair_b p = offset_val 216 p.
Proof. intros. unfold pair_b. rewrite field_address_offset by auto with field_compatible. reflexivity. Qed.
Lemma hse_addr_ap p : @field_compatible CSh t_pair [] p -> pair_ap p = offset_val 464 p.
Proof. intros. unfold pair_ap. rewrite field_address_offset by auto with field_compatible. reflexivity. Qed.
Lemma hse_addr_bp p : @field_compatible CSh t_pair [] p -> pair_bp p = offset_val 960 p.
Proof. intros. unfold pair_bp. rewrite field_address_offset by auto with field_compatible. reflexivity. Qed.

Lemma hse_table0_hs sh pa : hs_in_pool (hs_table sh pa) pa.
Proof.
  exists (mkEntry pa IDX_HANDSHAKE Int.zero). unfold t_entry, hs_table. simpl.
  destruct (EqDec_val (hs_addr pa) (hs_addr pa)) as [_ | n]; [auto | congruence].
Qed.

(* the address arguments of main's calls *)
Ltac hse_addr :=
  entailer!; simpl; unfold hs_addr, kps_addr;
  match goal with Hp: @field_compatible CSh t_pair [] ?p |- _ =>
    rewrite ?(hse_addr_ap _ Hp), ?(hse_addr_bp _ Hp), ?(hse_addr_a _ Hp), ?(hse_addr_b _ Hp) end;
  reflexivity.

(* ------------------------------------------------------------------------------------------------ *)
(* Giving back main's stack frame at its returns                                                    *)
(* ------------------------------------------------------------------------------------------------ *)

(* one entry of a pool, the others dropped *)
Lemma hse_pool_take l a sh E :
  In (a, sh, E) l -> iter_sepcon hs_pool_entry l |-- (EX n: val, EX h: bool, entry_at sh a E n h) * TT.
Proof.
  intros Hin. apply in_split in Hin. destruct Hin as [l1 [l2 ->]].
  rewrite iter_sepcon_app. simpl. unfold hs_pool_entry at 2. Intros n h. Exists n h. cancel.
Qed.

Lemma hse_sfind_In {A: Type} (l: list (val * share * A)) a sh v : sfind l a = Some (sh, v) -> In (a, sh, v) l.
Proof.
  induction l as [| [[x sh0] w] l IH]; simpl; [discriminate |].
  destruct (EqDec_val x a) as [-> |]; [intros E; inv E; left; reflexivity | intros E; right; auto].
Qed.

(* struct pair after any run of the handshake functions whose tables still hold their peers' handshake
   entries (with, possibly, more entries: the keypairs begin_session adds) *)
Lemma hse_close p DA DB TA TB ka kb PA PB EA EB :
  @field_compatible CSh t_pair [] p ->
  sfind (t_D TA) (hs_addr (pair_ap p)) = Some (Tsh, EA) -> sfind (t_D TB) (hs_addr (pair_bp p)) = Some (Tsh, EB) ->
  device_rep5 Tsh (pair_a p) DA * device_rep5 Tsh (pair_b p) DB *
  itable Tsh (pair_ai p) TA * itable Tsh (pair_bi p) TB *
  ptable Tsh (pair_ak p) ka * ptable Tsh (pair_bk p) kb *
  peer_rep5 Tsh (pair_ap p) PA * peer_rep5 Tsh (pair_bp p) PB
  |-- @data_at_ CSh Tsh t_pair p * TT.
Proof.
  intros Hfc HA HB. apply hse_sfind_In in HA. apply hse_sfind_In in HB.
  sep_apply (hs_close_dev Tsh (pair_a p) DA). sep_apply (hs_close_dev Tsh (pair_b p) DB).
  sep_apply (hs_close_itable Tsh (pair_ai p) TA). sep_apply (hs_close_itable Tsh (pair_bi p) TB).
  sep_apply (hse_pool_take _ _ _ _ HA). sep_apply (hse_pool_take _ _ _ _ HB).
  Intros nb hb na ha.
  sep_apply (hs_close_peer Tsh (pair_ap p) PA EA na ha). sep_apply (hs_close_peer Tsh (pair_bp p) PB EB nb hb).
  unfold ptable. sep_apply (@data_at_data_at_ Noise.CS Tsh t_ptab ka (pair_ak p)).
  sep_apply (@data_at_data_at_ Noise.CS Tsh t_ptab kb (pair_bk p)).
  sep_apply (hs_pair_join Tsh p Hfc). cancel.
Qed.

Lemma hse_close_init m Mo : init_opt_rep Tsh m Mo |-- @data_at_ Noise.CS Tsh t_init m.
Proof. destruct Mo as [M |]; simpl; [apply hs_close_init | apply derives_refl]. Qed.

Lemma hse_close_resp m Mo : resp_opt_rep Tsh m Mo |-- @data_at_ Noise.CS Tsh t_resp m.
Proof. destruct Mo as [M |]; simpl; [apply hs_close_resp | apply derives_refl]. Qed.

(* the table new_pair builds holds the peer's handshake entry *)
Lemma hse_table0_find sh pa : sfind (t_D (hs_table sh pa)) (hs_addr pa) = Some (sh, mkEntry pa IDX_HANDSHAKE Int.zero).
Proof. simpl. destruct (EqDec_val (hs_addr pa) (hs_addr pa)) as [_ | n]; [reflexivity | congruence]. Qed.

Lemma hse_peers1 a sh P : peers_rep5 [(a, sh, P)] = peer_rep5 sh a P.
Proof. unfold peers_rep5. simpl. apply sepcon_emp. Qed.

Lemma hse_insert0 sh pa idx : t_insert (hs_table sh pa) (hs_addr pa) idx = hse_table1 sh pa idx.
Proof. apply hse_insert. Qed.

Lemma hse_supd1 {A: Type} a sh (v v': A) : supd [(a, sh, v)] a v' = [(a, sh, v')].
Proof. simpl. destruct (EqDec_val a a) as [_ | n]; [reflexivity | congruence]. Qed.

Lemma hse_table1_find sh pa idx : sfind (t_D (hse_table1 sh pa idx)) (hs_addr pa) = Some (sh, mkEntry pa IDX_HANDSHAKE idx).
Proof. simpl. destruct (EqDec_val (hs_addr pa) (hs_addr pa)) as [_ | n]; [reflexivity | congruence]. Qed.

(* a peer's address is a valid pointer (main compares consume_initiation's result with NULL) *)
Lemma hse_peer_valid sh p P : sepalg.nonidentity sh -> peer_rep5 sh p P |-- valid_pointer p.
Proof.
  intros Hsh. unfold peer_rep5. Intros.
  repeat apply sepcon_valid_pointer1.
  rewrite (@field_at_data_at Noise.CS). rewrite field_address_offset by auto with field_compatible.
  simpl. pose proof H as [Hp _]. rewrite isptr_offset_val_zero by exact Hp.
  apply (@data_at_valid_ptr Noise.CS sh (tptr t_dev) (p_device P) p Hsh). simpl; lia.
Qed.

(* consume_initiation / consume_response returned a peer of the pair: main's test of NULL fails *)
Lemma hse_cmp_null q : isptr q -> sem_cmp_pp Ceq q (Vlong (Int64.repr 0)) = Some (Vint Int.zero).
Proof. destruct q; try contradiction. intros _. reflexivity. Qed.

Lemma hse_isptr_ap p : @field_compatible CSh t_pair [] p -> isptr (pair_ap p).
Proof. intros H. rewrite (hse_addr_ap p H). destruct H as [Hp _]. destruct p; try contradiction. exact I. Qed.
Lemma hse_isptr_bp p : @field_compatible CSh t_pair [] p -> isptr (pair_bp p).
Proof. intros H. rewrite (hse_addr_bp p H). destruct H as [Hp _]. destruct p; try contradiction. exact I. Qed.

(* a peer is its handshake (which erased() reads) and the rest *)
Section PeerSplit.
#[local] Existing Instance Noise.CS.

Definition hse_peer_rest (sh: share) (p: val) (P: peer) : mpred :=
  !! field_compatible t_peer [] p &&
  (field_at sh t_peer [StructField I._device] (p_device P) p *
   field_at sh t_peer [StructField I._is_dead] (Val.of_bool (p_dead P)) p *
   kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
   field_at_ sh t_peer [StructField I._last_sent_handshake] p *
   field_at_ sh t_peer [StructField I._latest_cookie] p *
   field_at sh t_peer [StructField I._refcount] (Vint (p_refs P)) p *
   field_at_ sh t_peer [StructField I._internal_id] p *
   field_at sh t_peer [StructField I._pubkey_next] (p_pknext P) p *
   spacer sh 9 16 p * spacer sh 476 480 p).

Lemma hse_peer_split sh p P : peer_rep5 sh p P = hs_rep sh (hs_addr p) (p_hs P) * hse_peer_rest sh p P.
Proof. unfold peer_rep5, hse_peer_rest. apply pred_ext; entailer!. Qed.

Lemma hse_peer_join sh p P : hs_rep sh (hs_addr p) (p_hs P) * hse_peer_rest sh p P |-- peer_rep5 sh p P.
Proof. rewrite hse_peer_split. apply derives_refl. Qed.

End PeerSplit.

Lemma hse_peer_fc sh p P : peer_rep5 sh p P |-- !! @field_compatible Noise.CS t_peer [] p.
Proof. unfold peer_rep5. entailer!. Qed.

Lemma hse_kps_nil (CSw: compspecs) : emp |-- @keypairs_rep CSw [].
Proof. unfold keypairs_rep. simpl. apply derives_refl. Qed.

(* a branch of main's tests that its temporaries rule out *)
Ltac hse_contra :=
  exfalso;
  match goal with
  | H: Int.repr 1 = Int.zero |- _ => apply Int.one_not_zero; exact H
  | H: Int.one = Int.zero |- _ => apply Int.one_not_zero; exact H
  | H: ?x <> ?x |- _ => apply H; reflexivity
  | H: typed_true _ Vfalse |- _ => compute in H; discriminate H
  | H: typed_false _ Vtrue |- _ => compute in H; discriminate H
  | H: true = false |- _ => discriminate H
  | H: false = true |- _ => discriminate H
  | H: typed_true _ _, Hp: @field_compatible CSh t_pair [] ?p |- _ =>
      rewrite hse_cmp_null in H by first [apply (hse_isptr_ap p Hp) | apply (hse_isptr_bp p Hp)];
      compute in H; congruence
  end.

(* main's return: give back its stack frame (HA, HB: the tables still hold the peers' handshake entries) *)
Ltac hse_ret HA HB :=
  try (Exists (Int.repr 0); rewrite prop_true_andp by reflexivity);
  repeat match goal with |- context [d_ptab ?D] =>
    let x := eval cbv [D pair_devA pair_devB hs_dev d_ptab] in (d_ptab D) in change (d_ptab D) with x end;
  repeat match goal with |- context [d_itab ?D] =>
    let x := eval cbv [D pair_devA pair_devB hs_dev d_itab] in (d_itab D) in change (d_itab D) with x end;
  match goal with
  | Hp: @field_compatible CSh t_pair [] ?p |- context [ptable Tsh (pair_ak ?p) ?ka] =>
    match goal with |- context [ptable Tsh (pair_bk p) ?kb] =>
    match goal with |- context [peer_rep5 Tsh (pair_ap p) ?PA] =>
    match goal with |- context [peer_rep5 Tsh (pair_bp p) ?PB] =>
    match goal with |- context [device_rep5 Tsh (pair_a p) ?DA] =>
    match goal with |- context [device_rep5 Tsh (pair_b p) ?DB] =>
      sep_apply (hse_close p DA DB _ _ ka kb PA PB _ _ Hp HA HB) end end end end end end;
  first [sep_apply hse_close_init | sep_apply hs_close_init];
  try first [sep_apply hse_close_resp | sep_apply hs_close_resp];
  rewrite hse_conv_pair, hse_conv_init, hse_conv_resp; cancel.

Section Main.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).

(* the functions main calls *)
Definition hse_Gmain : funspecs :=
  [new_pair_spec x25519; any_clocks_spec;
   wg_noise_handshake_create_initiation_spec x25519 aead_enc;
   wg_noise_handshake_consume_initiation_spec x25519 aead_dec;
   wg_noise_handshake_create_response_spec x25519 aead_enc;
   wg_noise_handshake_consume_response_spec x25519 aead_dec;
   wg_noise_handshake_begin_session_spec W_hs_session_erases;
   erased_spec; gp_assert_spec].

(* main's specification in the law's program: from the initial globals, any result *)
Definition hse_main_spec : ident * funspec := hs_main_spec WgNoise.contracts.hs_session_erases.whole_prog.

Lemma hse_main_body :
  semax_body hse_V hse_Gmain C.f_main hse_main_spec.
Proof.
  unfold hse_main_spec, hs_main_spec, QPmain_spec_ext', NDmk_funspec.
  split3; [reflexivity | reflexivity | ]. intros Espec DTL gv.
  eapply (main_pre_InitGpred (hs_globals0 gv));
    [apply hs_init_globals_session_erases | reflexivity
    | apply Forall_forall; intros x Hx; vm_compute in Hx; repeat destruct Hx as [Hx|Hx]; try contradiction; subst x; vm_compute; exact I | ].
  process_stackframe_of.
  Intros. unfold C.f_main; simpl fn_body. abbreviate_semax.
  (* main's postcondition TT, in canonical form *)
  unfold abbreviate in POSTCONDITION. subst POSTCONDITION. unfold hs_post.
  replace (fun _ : environ => @TT mpred _) with (PROP () LOCAL () SEP (TT))%assert
    by (extensionality rho; unfold PROPx, LOCALx, SEPx; simpl; normalize).
  abbreviate_semax.
  unfold hs_globals0. sep_apply (create_mem_mgr gv).
  set (S := hs_shim0). set (w := hs_w0). set (kc := Int64.zero).
  rewrite hse_conv_pair, hse_conv_init, hse_conv_resp.
  forward_call (gv, Tsh, v_p, zeros32, zeros32, kc).
  Intros vret. destruct vret as [[araw braw] psk]. simpl fst in *; simpl snd in *.
  forward_call (gv, S, w). Intros vret. destruct vret as [[b rs] rn]. simpl fst in *; simpl snd in *.
  unfold hs_pair. Intros.
  set (DA := pair_devA x25519 v_p araw). set (DB := pair_devB x25519 v_p braw).
  set (PA0 := pair_peerA x25519 v_p araw braw psk). set (PB0 := pair_peerB x25519 v_p araw braw psk).
  set (S1 := shim_clocks S b rs rn).
  forward_call (gv, S1, w, kc, Tsh, v_initiation, @None init_msg, Tsh, pair_ap v_p, PA0, Tsh, pair_a v_p, DA,
                Tsh, hs_table Tsh (pair_ap v_p)).
  { hse_addr. }
  { apply hse_table0_hs. }
  Intros vret. destruct vret as [r1 idx1]. simpl fst in *; simpl snd in *.
  destruct (ci_res x25519 aead_enc DA PA0 init_msg0 S1 r1 idx1) as [[ok1 M1] HS1] eqn:Eci.
  simpl fst in *; simpl snd in *.
  destruct ok1.
  2: {
    apply semax_if_seq. forward_if; [| hse_contra].
    forward.
    apply semax_if_seq. forward_if; [forward | hse_contra].
    apply semax_if_seq. forward_if; [forward | hse_contra].
    forward_if; [| hse_contra].
    forward.
    hse_ret (hse_table0_find Tsh (pair_ap v_p)) (hse_table0_find Tsh (pair_bp v_p)).
  }
  (* create_initiation succeeded *)
  rewrite hse_insert0.
  apply semax_if_seq. forward_if; [hse_contra |].
  rewrite <- (hse_peers1 (pair_bp v_p) Tsh PB0).
  change (init_opt_rep Tsh v_initiation (opt_after true None M1)) with (init_rep5 Tsh v_initiation M1).
  match goal with |- context [shim_state4 gv ?S2 w] => set (S2' := S2) end.
  forward_call (gv, S2', w, kc, Tsh, v_initiation, M1, Tsh, pair_b v_p, DB, Tsh, pair_bp v_p,
                [(pair_bp v_p, Tsh, PB0)]).
  { hse_addr. }
  { unfold PB0, pair_peerB, hs_peer0, hs_initial, prot_specs4.hs_initial. simpl.
    unfold peers_wf, peers_refs_ok.
    split; [apply Forall_cons; [auto with share | apply Forall_nil] |].
    split; [split; reflexivity |].
    split; (apply Forall_cons; [simpl | apply Forall_nil]).
    - rewrite Int64.signed_zero. rep_lia.
    - rewrite Int.unsigned_one. rep_lia. }
  destruct (cin_res x25519 aead_dec DB [(pair_bp v_p, Tsh, PB0)] M1 S2') as [[b' PB1] |] eqn:Ecin.
  2: {
    simpl peers_after; simpl peer_result. rewrite hse_peers1.
    forward.
    apply semax_if_seq. forward_if; [forward | hse_contra].
    apply semax_if_seq. forward_if; [forward | hse_contra].
    forward_if; [| hse_contra].
    forward.
    hse_ret (hse_table1_find Tsh (pair_ap v_p) idx1) (hse_table0_find Tsh (pair_bp v_p)).
  }
  (* consume_initiation accepted B's peer *)
  assert (Eb: b' = pair_bp v_p /\ exists H', PB1 = p_set_hs (p_set_refs PB0 (rc_add1 (p_refs PB0))) H')
    by (apply (hse_cin_one x25519 aead_dec _ _ _ _ _ _ _ _ Ecin)).
  destruct Eb as [-> [HB1 EPB1]].
  simpl peer_result. unfold peers_after. rewrite hse_supd1, hse_peers1.
  forward.
  { entailer!. sep_apply (hse_peer_valid Tsh (pair_bp v_p)); [auto with share |]. entailer!. }
  apply semax_if_seq. forward_if; [hse_contra |].
  forward_call (gv, S2', w, Tsh, v_response, @None resp_msg, Tsh, pair_bp v_p, PB1, Tsh, pair_b v_p, DB,
                Tsh, hs_table Tsh (pair_bp v_p)).
  { hse_addr. }
  { split; [subst PB1; reflexivity | apply hse_table0_hs]. }
  Intros vret. destruct vret as [r2 idx2]. simpl fst in *; simpl snd in *.
  destruct (cr_res x25519 aead_enc PB1 resp_msg0 r2 idx2) as [[ok2 M2] HS2] eqn:Ecr.
  simpl fst in *; simpl snd in *.
  destruct ok2.
  2: {
    forward.
    apply semax_if_seq. forward_if; [forward | hse_contra].
    forward_if; [| hse_contra].
    forward.
    hse_ret (hse_table1_find Tsh (pair_ap v_p) idx1) (hse_table0_find Tsh (pair_bp v_p)).
  }
  (* create_response succeeded *)
  rewrite hse_insert0.
  forward.
  apply semax_if_seq. forward_if; [hse_contra |].
  rewrite <- (hse_peers1 (pair_ap v_p) Tsh (p_set_hs PA0 HS1)).
  change (resp_opt_rep Tsh v_response (opt_after true None M2)) with (resp_rep5 Tsh v_response M2).
  match goal with |- context [shim_state4 gv ?S3 w] => set (S3' := S3) end.
  forward_call (gv, S3', w, Tsh, v_response, M2, Tsh, pair_a v_p, DA, Tsh, hse_table1 Tsh (pair_ap v_p) idx1,
                [(pair_ap v_p, Tsh, p_set_hs PA0 HS1)]).
  { hse_addr. }
  { unfold peers_wf, peers_refs_ok.
    split; [apply hse_table1_peers; simpl; apply Int.one_not_zero |].
    split; [apply Forall_cons; [auto with share | apply Forall_nil] |].
    apply Forall_cons; [simpl; rewrite Int.unsigned_one; rep_lia | apply Forall_nil]. }
  destruct (cre_res x25519 aead_dec DA (hse_table1 Tsh (pair_ap v_p) idx1) [(pair_ap v_p, Tsh, p_set_hs PA0 HS1)] M2)
    as [[a' PA2] |] eqn:Ecre.
  2: {
    simpl peers_after; simpl peer_result. rewrite hse_peers1.
    forward.
    forward_if; [| hse_contra].
    forward.
    hse_ret (hse_table1_find Tsh (pair_ap v_p) idx1) (hse_table1_find Tsh (pair_bp v_p) idx2).
  }
  (* consume_response accepted A's peer *)
  assert (Ea: a' = pair_ap v_p /\
              exists H', PA2 = p_set_hs (p_set_refs (p_set_hs PA0 HS1) (rc_add1 (p_refs (p_set_hs PA0 HS1)))) H')
    by (apply (hse_cre_one x25519 aead_dec _ _ _ _ _ _ _ _ Ecre)).
  destruct Ea as [-> [HA2 EPA2]].
  simpl peer_result. unfold peers_after. rewrite hse_supd1, hse_peers1.
  forward.
  { entailer!. sep_apply (hse_peer_valid Tsh (pair_ap v_p)); [auto with share |]. entailer!. }
  forward_if; [hse_contra |].
  (* begin_session on A's side *)
  assert_PROP (@field_compatible Noise.CS t_peer [] (pair_ap v_p)) as FCa
    by (sep_apply (hse_peer_fc Tsh (pair_ap v_p) PA2); entailer!).
  sep_apply (hse_kps_nil W_hs_session_erases).
  forward_call (gv, S3', w, kc, @nil (val * keypair), hse_table1 Tsh (pair_ap v_p) idx1, Tsh, pair_ap v_p, PA2,
                Tsh, pair_a v_p, DA, Tsh).
  { hse_addr. }
  { subst PA2. split; [reflexivity |]. split; [apply hse_table1_hs |]. split; [apply hse_table1_kps |].
    apply hse_slots_nil; reflexivity. }
  Intros ka.
  set (RA := bs_res PA2 (pair_ap v_p) ka kc [] (hse_table1 Tsh (pair_ap v_p) idx1) S3') in *.
  (* begin_session on B's side *)
  assert_PROP (@field_compatible Noise.CS t_peer [] (pair_bp v_p)) as FCb
    by (sep_apply (hse_peer_fc Tsh (pair_bp v_p) (p_set_hs PB1 HS2)); entailer!).
  sep_apply (hse_kps_nil W_hs_session_erases).
  match goal with |- context [shim_state4 gv ?S4 ?w4] =>
    forward_call (gv, S4, w4, snd RA, @nil (val * keypair), hse_table1 Tsh (pair_bp v_p) idx2, Tsh, pair_bp v_p,
                  p_set_hs PB1 HS2, Tsh, pair_b v_p, DB, Tsh) end.
  { hse_addr. }
  { subst PB1. split; [reflexivity |]. split; [apply hse_table1_hs |]. split; [apply hse_table1_kps |].
    apply hse_slots_nil; reflexivity. }
  Intros kb.
  set (RB := bs_res (p_set_hs PB1 HS2) (pair_bp v_p) kb (snd RA) [] (hse_table1 Tsh (pair_bp v_p) idx2)
               (kw_S (snd (fst RA)))) in *.
  (* the tables still hold the peers' handshake entries *)
  assert (FA: exists EA, sfind (t_D (kw_T (snd (fst RA)))) (hs_addr (pair_ap v_p)) = Some (Tsh, EA)).
  { subst RA PA2. unfold bs_res. eapply hse_bs_find; try reflexivity; [apply hse_table1_find |].
    intros Hn. apply H14. exact Hn. }
  assert (FB: exists EB, sfind (t_D (kw_T (snd (fst RB)))) (hs_addr (pair_bp v_p)) = Some (Tsh, EB)).
  { subst RB PB1. unfold bs_res. eapply hse_bs_find; try reflexivity; [apply hse_table1_find |].
    intros Hn. apply H16. exact Hn. }
  destruct FA as [EA FA]. destruct FB as [EB FB].
  (* the law: a begin_session that returned true erased its handshake *)
  assert (EB': fst (fst (fst RB)) = true -> hse_erasedb (p_hs (snd (fst (fst RB)))) = true)
    by (intros; subst RB; unfold bs_res, prot_specs4.bs_res in *; rewrite hse_bs_erases by assumption; reflexivity).
  apply -> seq_assoc. apply semax_if_seq. forward_if.
  - (* A's begin_session returned true: its handshake is erased *)
    assert (BA: fst (fst (fst RA)) = true) by (destruct (fst (fst (fst RA))); [reflexivity | hse_contra]).
    rewrite (hse_peer_split Tsh (pair_ap v_p) (snd (fst (fst RA)))). Intros.
    forward_call (Tsh, hs_addr (pair_ap v_p), p_hs (snd (fst (fst RA)))).
    { hse_addr. }
    assert (EA': hse_erasedb (p_hs (snd (fst (fst RA)))) = true)
      by (subst RA; unfold bs_res, prot_specs4.bs_res in *; rewrite hse_bs_erases by assumption; reflexivity).
    rewrite EA'.
    forward_call (Int.one).
    sep_apply (hse_peer_join Tsh (pair_ap v_p) (snd (fst (fst RA)))).
    apply -> seq_assoc. apply semax_if_seq. forward_if.
    + assert (BB: fst (fst (fst RB)) = true) by (destruct (fst (fst (fst RB))); [reflexivity | hse_contra]).
      rewrite (hse_peer_split Tsh (pair_bp v_p) (snd (fst (fst RB)))). Intros.
      forward_call (Tsh, hs_addr (pair_bp v_p), p_hs (snd (fst (fst RB)))).
      { hse_addr. }
      rewrite (EB' BB).
      forward_call (Int.one).
      sep_apply (hse_peer_join Tsh (pair_bp v_p) (snd (fst (fst RB)))).
      forward.
      hse_ret FA FB.
    + forward.
      hse_ret FA FB.
  - (* A's begin_session returned false: nothing to check on A's side *)
    apply -> seq_assoc. apply semax_if_seq. forward_if.
    + assert (BB: fst (fst (fst RB)) = true) by (destruct (fst (fst (fst RB))); [reflexivity | hse_contra]).
      rewrite (hse_peer_split Tsh (pair_bp v_p) (snd (fst (fst RB)))). Intros.
      forward_call (Tsh, hs_addr (pair_bp v_p), p_hs (snd (fst (fst RB)))).
      { hse_addr. }
      rewrite (EB' BB).
      forward_call (Int.one).
      sep_apply (hse_peer_join Tsh (pair_bp v_p) (snd (fst (fst RB)))).
      forward.
      hse_ret FA FB.
    + forward.
      hse_ret FA FB.
Qed.

End Main.
