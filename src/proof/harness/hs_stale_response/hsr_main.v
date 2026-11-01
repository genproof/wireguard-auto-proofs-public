(* The law hs_stale_response: the body of main (harness/hs_stale_response.c), in the law's world.

   main builds the pair of devices (new_pair), lets A initiate, B consume and respond, and A initiate again;
   gp_assume gives that the second initiation's sender index differs from the first's.  Then A's table lists
   its handshake entry with the second index only, while B's response is addressed to the first
   (hsr_model.v), so consume_response returns NULL and the gp_assert holds. *)
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
Require Import WgNoise.proof.harness.hs_common.hs_close.
Require Import WgNoise.proof.harness.hs_common.hs_worlds.
Require Import WgNoise.proof.harness.hs_common.hs_globals.
Require Import WgNoise.proof.harness.hs_common.hs_asm.
Require Import WgNoise.proof.harness.hs_stale_response.hsr_model.
Require WgNoise.contracts.hs_stale_response.
Require WgNoise.harness.hs_stale_response.code.
Local Open Scope logic.

Module C := WgNoise.harness.hs_stale_response.code.

Definition W : compspecs := W_hs_stale_response.
#[local] Existing Instance W.

#[local] Instance hsr_cce_N : change_composite_env Noise.CS W.
Proof. make_cs_preserve Noise.CS W. Defined.
#[local] Instance hsr_cce_H : change_composite_env CSh W.
Proof. make_cs_preserve CSh W. Defined.

(* main's stack frame, from the world's compspecs to those of the specifications *)
Lemma hsr_conv_pair sh p : @data_at_ W sh (Tstruct C._pair noattr) p = @data_at_ CSh sh t_pair p.
Proof. rewrite (@data_at__change_composite CSh W _ sh t_pair); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hsr_conv_init sh p : @data_at_ W sh (Tstruct C._message_handshake_initiation noattr) p = @data_at_ Noise.CS sh t_init p.
Proof. rewrite (@data_at__change_composite Noise.CS W _ sh t_init); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hsr_conv_resp sh p : @data_at_ W sh (Tstruct C._message_handshake_response noattr) p = @data_at_ Noise.CS sh t_resp p.
Proof. rewrite (@data_at__change_composite Noise.CS W _ sh t_resp); [reflexivity | prove_cs_preserve_type]. Qed.

(* an initiation message is its sender index, read by main in the world's compspecs, and the rest *)
Definition hsr_init_rest (sh: share) (m: val) (M: init_msg) : mpred :=
  !! im_ok5 M &&
  (@field_at Noise.CS sh t_init [StructField I._header] (Vint (im_type M)) m *
   @field_at Noise.CS sh t_init [StructField I._unencrypted_ephemeral] (bytes (im_eph M)) m *
   @field_at Noise.CS sh t_init [StructField I._encrypted_static] (bytes (im_encs M)) m *
   @field_at Noise.CS sh t_init [StructField I._encrypted_timestamp] (bytes (im_enct M)) m *
   @field_at_ Noise.CS sh t_init [StructField I._macs] m).

Lemma hsr_conv_sender sh (v: val) m :
  @field_at Noise.CS sh t_init [StructField I._sender_index] v m =
  @field_at W sh (Tstruct C._message_handshake_initiation noattr) [StructField C._sender_index] v m.
Proof.
  rewrite (@field_at_change_composite Noise.CS W _ sh t_init [StructField I._sender_index] v v (JMeq_refl v));
    [reflexivity | prove_cs_preserve_type].
Qed.

Lemma hsr_init_split sh m M :
  init_rep5 sh m M =
  @field_at W sh (Tstruct C._message_handshake_initiation noattr) [StructField C._sender_index] (Vint (im_sender M)) m *
  hsr_init_rest sh m M.
Proof.
  unfold init_rep5, hsr_init_rest. rewrite <- hsr_conv_sender.
  apply pred_ext; entailer!.
Qed.

Lemma hsr_init_join sh m M :
  @field_at W sh (Tstruct C._message_handshake_initiation noattr) [StructField C._sender_index] (Vint (im_sender M)) m *
  hsr_init_rest sh m M |-- init_rep5 sh m M.
Proof. rewrite hsr_init_split. apply derives_refl. Qed.

Definition hsr_main_spec : ident * funspec := hs_main_spec WgNoise.contracts.hs_stale_response.whole_prog.

(* the table of new_pair holds the peer's handshake entry *)
Lemma hsr_table_in_pool sh pa : hs_in_pool (hs_table sh pa) pa.
Proof. unfold hs_in_pool, hs_table, t_entry. simpl. rewrite if_true by reflexivity. eexists; split; reflexivity. Qed.

(* the arguments &p.a_peer.handshake etc. are the addresses of the specifications *)
Ltac hsr_addr :=
  entailer!; unfold hs_addr, kps_addr, pair_ap, pair_bp, pair_a, pair_b, field_address;
  rewrite ?if_true by auto with field_compatible; try reflexivity.

(* the projections of a call's result, in the goal and the hypotheses but not in the abbreviated POSTCONDITION *)
Ltac hsr_simpl :=
  cbn [fst snd]; repeat match goal with H: context [fst (_, _)] |- _ => cbn [fst snd] in H
                                      | H: context [snd (_, _)] |- _ => cbn [fst snd] in H end.

(* main's postcondition TT in Floyd's canonical form *)
Lemma hsr_post_canon gv : hs_post gv = PROP () LOCAL () SEP (TT).
Proof.
  extensionality rho. unfold hs_post, PROPx, LOCALx, SEPx. simpl.
  apply pred_ext; normalize.
Qed.

(* main's stack frame at a return: struct pair after any run in which each index table holds exactly its peer's
   handshake entry, and the three messages, are uninitialised memory of their types again *)
Lemma hsr_close_frame p m1 m2 r DA DB TA TB ka kb PA PB EA EB :
  @field_compatible CSh t_pair [] p ->
  t_D TA = [(hs_addr (pair_ap p), Tsh, EA)] -> t_D TB = [(hs_addr (pair_bp p), Tsh, EB)] ->
  @data_at_ Noise.CS Tsh t_init m1 * @data_at_ Noise.CS Tsh t_init m2 * @data_at_ Noise.CS Tsh t_resp r *
  device_rep5 Tsh (pair_a p) DA * device_rep5 Tsh (pair_b p) DB *
  itable Tsh (pair_ai p) TA * itable Tsh (pair_bi p) TB *
  ptable Tsh (pair_ak p) ka * ptable Tsh (pair_bk p) kb *
  peer_rep5 Tsh (pair_ap p) PA * peer_rep5 Tsh (pair_bp p) PB
  |-- @data_at_ W Tsh (Tstruct C._pair noattr) p *
      @data_at_ W Tsh (Tstruct C._message_handshake_initiation noattr) m1 *
      @data_at_ W Tsh (Tstruct C._message_handshake_initiation noattr) m2 *
      @data_at_ W Tsh (Tstruct C._message_handshake_response noattr) r.
Proof.
  intros Hfc HA HB. rewrite hsr_conv_pair, !hsr_conv_init, hsr_conv_resp.
  sep_apply (hs_pair_close Tsh p DA DB TA TB ka kb PA PB EA EB Hfc HA HB). cancel.
Qed.

(* a message buffer after a create step is uninitialised memory of its type *)
Lemma hsr_init_close sh m Mo : init_opt_rep sh m Mo |-- @data_at_ Noise.CS sh t_init m.
Proof. destruct Mo; simpl; [apply hs_close_init | apply derives_refl]. Qed.
Lemma hsr_resp_close sh m Mo : resp_opt_rep sh m Mo |-- @data_at_ Noise.CS sh t_resp m.
Proof. destruct Mo; simpl; [apply hs_close_resp | apply derives_refl]. Qed.

(* the closing of main's frame at a return (the tables' pools are computed by reflexivity) *)
Ltac hsr_tabs :=
  repeat match goal with
  | |- context [d_itab (pair_devA ?x ?p ?a)] => change (d_itab (pair_devA x p a)) with (pair_ai p)
  | |- context [d_itab (pair_devB ?x ?p ?a)] => change (d_itab (pair_devB x p a)) with (pair_bi p)
  | |- context [d_ptab (pair_devA ?x ?p ?a)] => change (d_ptab (pair_devA x p a)) with (pair_ak p)
  | |- context [d_ptab (pair_devB ?x ?p ?a)] => change (d_ptab (pair_devB x p a)) with (pair_bk p)
  end.

Ltac hsr_close :=
  hsr_tabs;
  repeat match goal with |- context [hsr_init_rest ?sh ?m ?M] => sep_apply (hsr_init_join sh m M) end;
  repeat sep_apply hsr_init_close; repeat sep_apply hsr_resp_close;
  repeat sep_apply hs_close_init; repeat sep_apply hs_close_resp;
  match goal with
  | |- context [device_rep5 Tsh (pair_a ?p) ?DA] =>
  match goal with
  | |- context [device_rep5 Tsh (pair_b p) ?DB] =>
  match goal with
  | |- context [itable Tsh ?ai ?TA] => unify ai (pair_ai p);
  match goal with
  | |- context [itable Tsh ?bi ?TB] => unify bi (pair_bi p);
  match goal with
  | |- context [ptable Tsh (pair_ak p) ?ka] =>
  match goal with
  | |- context [ptable Tsh (pair_bk p) ?kb] =>
  match goal with
  | |- context [peer_rep5 Tsh (pair_ap p) ?PA] =>
  match goal with
  | |- context [peer_rep5 Tsh (pair_bp p) ?PB] =>
  match goal with
  | |- _ |-- _ * data_at_ _ _ p * data_at_ _ _ ?m1 * data_at_ _ _ ?m2 * data_at_ _ _ ?r =>
    sep_apply (hsr_close_frame p m1 m2 r DA DB TA TB ka kb PA PB); try reflexivity; cancel
  end end end end end end end end end.

Lemma hsr_insert_table sh pa idx : t_insert (hs_table sh pa) (hs_addr pa) idx = hsr_tab sh pa idx.
Proof. apply hsr_insert0. Qed.

(* one peer is the peer list of one element *)
Lemma hsr_peers1 sh a P : peer_rep5 sh a P = peers_rep5 [(a, sh, P)].
Proof. unfold peers_rep5. simpl. rewrite sepcon_emp. reflexivity. Qed.

(* the pure preconditions on the one-peer lists of the pair (writable shares, small counters) *)
Ltac hsr_props :=
  repeat split; repeat constructor; cbn; auto with share; try apply writable_share_top; try rep_lia.

(* a peer is a valid pointer (its first field, the device pointer, is at offset 0): the test of
   consume_initiation's result against NULL is defined *)
Lemma hsr_peer_valid sh p P : sepalg.nonidentity sh -> peer_rep5 sh p P |-- valid_pointer p.
Proof.
  intros Hsh. unfold peer_rep5. Intros.
  rewrite !sepcon_assoc. apply sepcon_valid_pointer1.
  apply (@field_at_valid_ptr0 Noise.CS sh t_peer [StructField I._device] (p_device P) p Hsh);
    [simpl; lia | reflexivity].
Qed.

(* the two branches of `if (!ok) return 0;` after a step with result ok *)
Ltac hsr_fail ok := match goal with Ht: typed_true _ _ |- _ => destruct ok; [discriminate Ht |]; clear Ht end.
Ltac hsr_succ ok := match goal with Ht: typed_false _ _ |- _ => destruct ok; [| discriminate Ht]; clear Ht end.

Section Main.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).

(* the functions main calls *)
Definition hsr_Gmain : funspecs :=
  [new_pair_spec x25519; any_clocks_spec;
   wg_noise_handshake_create_initiation_spec x25519 aead_enc;
   wg_noise_handshake_consume_initiation_spec x25519 aead_dec;
   wg_noise_handshake_create_response_spec x25519 aead_enc;
   wg_noise_handshake_consume_response_spec x25519 aead_dec;
   gp_assume_spec; gp_assert_spec; hsr_main_spec].

Lemma hsr_main_body :
  semax_body (QPvarspecs WgNoise.contracts.hs_stale_response.whole_prog) hsr_Gmain C.f_main hsr_main_spec.
Proof.
  unfold hsr_main_spec, hs_main_spec, QPmain_spec_ext', NDmk_funspec.
  split3; [reflexivity | reflexivity | ]. intros Espec DTL gv.
  eapply (main_pre_InitGpred (hs_globals0 gv));
    [apply hs_init_globals_stale_response | reflexivity
    | apply Forall_forall; intros x Hx; vm_compute in Hx; repeat destruct Hx as [Hx|Hx]; try contradiction; subst x; vm_compute; exact I | ].
  process_stackframe_of.
  rewrite hsr_post_canon.
  Intros. unfold C.f_main; simpl fn_body. abbreviate_semax.
  unfold hs_globals0. Intros.
  rewrite hsr_conv_pair, !hsr_conv_init, hsr_conv_resp.
  forward_call (gv, Tsh, v_p, zeros32, zeros32, Int64.zero).
  Intros vret. destruct vret as [[araw braw] psk]. hsr_simpl.
  rename H into Ha, H0 into Hb, H1 into Hpsk.
  forward_call (gv, hs_shim0, hs_w0).
  Intros vret. destruct vret as [[b1 rs1] rn1]. hsr_simpl.
  rename H into Hb1, H0 into Hrn1.
  unfold hs_pair. Intros. rename H into Hfc.
  (* A's first initiation *)
  forward_call (gv, shim_clocks hs_shim0 b1 rs1 rn1, hs_w0, Int64.zero, Tsh, v_first, @None init_msg, Tsh,
                pair_ap v_p, pair_peerA x25519 v_p araw braw psk, Tsh, pair_a v_p, pair_devA x25519 v_p araw, Tsh,
                hs_table Tsh (pair_ap v_p)).
  { hsr_addr. }
  { apply hsr_table_in_pool. }
  Intros vret. destruct vret as [r1 idx1]. hsr_simpl.
  change (init_of None) with init_msg0 in *.
  destruct (ci_res x25519 aead_enc (pair_devA x25519 v_p araw) (pair_peerA x25519 v_p araw braw psk)
              init_msg0 (shim_clocks hs_shim0 b1 rs1 rn1) r1 idx1) as [[ok1 M1] HA1] eqn:Eci1.
  hsr_simpl.
  forward_if.
  { destruct ok1; [discriminate H1 |]. forward.
    hsr_close. }
  destruct ok1; [| discriminate H1]. clear H1.
  assert (HS1: im_sender M1 = idx1).
  { pose proof (hsr_ci_sender x25519 aead_enc (d_id (pair_devA x25519 v_p araw))
      (p_hs (pair_peerA x25519 v_p araw braw psk)) init_msg0 r1 (tai64n (s_rsec (shim_clocks hs_shim0 b1 rs1 rn1))
      (s_rnsec (shim_clocks hs_shim0 b1 rs1 rn1))) idx1) as X.
    unfold ci_res, prot_specs4.ci_res in Eci1. rewrite Eci1 in X. apply X; reflexivity. }
  assert (HSID1: hs_sid HA1 = id_addr (pair_a v_p)).
  { pose proof (hsr_ci_sid x25519 aead_enc (d_id (pair_devA x25519 v_p araw))
      (p_hs (pair_peerA x25519 v_p araw braw psk)) init_msg0 r1 (tai64n (s_rsec (shim_clocks hs_shim0 b1 rs1 rn1))
      (s_rnsec (shim_clocks hs_shim0 b1 rs1 rn1))) idx1) as X.
    unfold ci_res, prot_specs4.ci_res in Eci1. rewrite Eci1 in X. exact X. }
  rewrite hsr_insert_table. hsr_tabs.
  change (init_opt_rep Tsh v_first (opt_after true None M1)) with (init_rep5 Tsh v_first M1).
  match goal with |- context [shim_state4 gv ?S hs_w0] => set (S2 := S) end.
  (* B consumes the initiation *)
  rewrite (hsr_peers1 Tsh (pair_bp v_p)).
  forward_call (gv, S2, hs_w0, Int64.zero, Tsh, v_first, M1, Tsh, pair_b v_p, pair_devB x25519 v_p braw, Tsh,
                pair_bp v_p, [(pair_bp v_p, Tsh, pair_peerB x25519 v_p araw braw psk)]).
  { hsr_addr. }
  { hsr_props. }
  destruct (cin_res x25519 aead_dec (pair_devB x25519 v_p braw)
              [(pair_bp v_p, Tsh, pair_peerB x25519 v_p araw braw psk)] M1 S2) as [[b PB1]|] eqn:Ecin.
  2: { cbn [peer_result peers_after]. rewrite <- hsr_peers1.
       forward_if.
       { forward. hsr_close. }
       contradiction. }
  assert (Hpb: isptr (pair_bp v_p)) by (unfold pair_bp; apply field_address_isptr; auto with field_compatible).
  unfold cin_res, prot_specs4.cin_res in Ecin.
  destruct (hsr_cin_single _ _ _ _ _ _ _ _ _ _ Ecin) as [-> [HdB HrB]].
  cbn [peer_result peers_after supd]. rewrite if_true by reflexivity. rewrite <- hsr_peers1.
  forward_if.
  { sep_apply (hsr_peer_valid Tsh (pair_bp v_p) PB1); [auto with share |]. entailer!. }
  { rewrite H1 in Hpb. contradiction. }
  (* B's response *)
  hsr_tabs.
  change (data_at_ Tsh t_resp v_response) with (resp_opt_rep Tsh v_response None).
  forward_call (gv, S2, hs_w0, Tsh, v_response, @None resp_msg, Tsh, pair_bp v_p, PB1, Tsh, pair_b v_p,
                pair_devB x25519 v_p braw, Tsh, hs_table Tsh (pair_bp v_p)).
  { hsr_addr. }
  { repeat split; first [apply hsr_table_in_pool | rewrite HdB; reflexivity]. }
  Intros vret. destruct vret as [r2 idx2r]. hsr_simpl.
  change (resp_of None) with resp_msg0 in *.
  destruct (cr_res x25519 aead_enc PB1 resp_msg0 r2 idx2r) as [[ok3 MR] HB2] eqn:Ecr. hsr_simpl.
  forward_if.
  { hsr_fail ok3. forward. hsr_close. }
  hsr_succ ok3.
  assert (HR: rm_receiver MR = idx1).
  { pose proof (hsr_cr_receiver x25519 aead_enc (p_hs PB1) resp_msg0 r2 idx2r) as X.
    unfold cr_res, prot_specs4.cr_res in Ecr. rewrite Ecr in X. cbn [fst snd] in X. rewrite X by reflexivity. congruence. }
  rewrite hsr_insert_table. hsr_tabs.
  change (resp_opt_rep Tsh v_response (opt_after true None MR)) with (resp_rep5 Tsh v_response MR).
  match goal with |- context [shim_state4 gv ?S hs_w0] => set (S3 := S) end.
  (* any later clocks *)
  forward_call (gv, S3, hs_w0).
  Intros vret. destruct vret as [[b2 rs2] rn2]. hsr_simpl.
  (* A's second initiation *)
  change (data_at_ Tsh t_init v_second) with (init_opt_rep Tsh v_second None).
  forward_call (gv, shim_clocks S3 b2 rs2 rn2, hs_w0, Int64.zero, Tsh, v_second, @None init_msg, Tsh,
                pair_ap v_p, p_set_hs (pair_peerA x25519 v_p araw braw psk) HA1, Tsh, pair_a v_p,
                pair_devA x25519 v_p araw, Tsh, hsr_tab Tsh (pair_ap v_p) idx1).
  { hsr_addr. }
  { repeat split; first [apply hsr_in_pool | exact HSID1 | reflexivity]. }
  Intros vret. destruct vret as [r3 idx2]. hsr_simpl.
  change (init_of None) with init_msg0 in *.
  destruct (ci_res x25519 aead_enc (pair_devA x25519 v_p araw) (p_set_hs (pair_peerA x25519 v_p araw braw psk) HA1)
              init_msg0 (shim_clocks S3 b2 rs2 rn2) r3 idx2) as [[ok4 M2] HA2] eqn:Eci2. hsr_simpl.
  forward_if.
  { hsr_fail ok4. forward. hsr_close. }
  hsr_succ ok4.
  assert (HS2: im_sender M2 = idx2).
  { pose proof (hsr_ci_sender x25519 aead_enc (d_id (pair_devA x25519 v_p araw)) HA1 init_msg0 r3
      (tai64n (s_rsec (shim_clocks S3 b2 rs2 rn2)) (s_rnsec (shim_clocks S3 b2 rs2 rn2))) idx2) as X.
    unfold ci_res, prot_specs4.ci_res in Eci2. cbn [p_hs p_set_hs] in Eci2. rewrite Eci2 in X. apply X; reflexivity. }
  rewrite hsr_insert. hsr_tabs.
  change (init_opt_rep Tsh v_second (opt_after true None M2)) with (init_rep5 Tsh v_second M2).
  (* gp_assume: the two sender indices differ *)
  rewrite (hsr_init_split Tsh v_second M2), (hsr_init_split Tsh v_first M1). Intros.
  forward. forward.
  forward_call (if Int.eq (im_sender M2) (im_sender M1) then Int.zero else Int.one).
  { entailer!. destruct (Int.eq (im_sender M2) (im_sender M1)); reflexivity. }
  destruct (Int.eq (im_sender M2) (im_sender M1)) eqn:Eq; [contradiction |].
  subst idx1 idx2.
  (* A consumes the old response: no handshake has its index *)
  rewrite (hsr_peers1 Tsh (pair_ap v_p)).
  forward_call (gv, if id_has (d_id (pair_devA x25519 v_p araw))
                    then shim_u32 (shim_draw (shim_clocks S3 b2 rs2 rn2) r3) (im_sender M2)
                    else shim_clocks S3 b2 rs2 rn2, hs_w0, Tsh, v_response, MR, Tsh, pair_a v_p,
                pair_devA x25519 v_p araw, Tsh, hsr_tab Tsh (pair_ap v_p) (im_sender M2),
                [(pair_ap v_p, Tsh, p_set_hs (p_set_hs (pair_peerA x25519 v_p araw braw psk) HA1) HA2)]).
  { hsr_addr. }
  { split; [apply hsr_pool_peers_ok; apply Int.one_not_zero | hsr_props]. }
  unfold cre_res, prot_specs4.cre_res.
  rewrite hsr_cre_none by (rewrite HR; exact Eq).
  cbn [peer_result peers_after]. rewrite <- hsr_peers1.
  (* the check *)
  forward_call Int.one.
  forward.
  hsr_close.
Qed.

End Main.
