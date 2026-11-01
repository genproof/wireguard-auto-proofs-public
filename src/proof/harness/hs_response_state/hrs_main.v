(* The law hs_response_state: main's body.  After new_pair, any_clocks, A's create_initiation, B's
   consume_initiation and B's create_response, A's handshake state is set to any value other than
   HANDSHAKE_CREATED_INITIATION; consume_response then finds at most A's handshake entry (A's index table holds only
   it), whose peer is not waiting for a response, so it returns NULL (consume_response_model is None) and
   gp_assert holds. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol5.prot_prog5.
Require Import WgNoise.proof.harness.hs_common.hs_specs.
Require Import WgNoise.proof.harness.hs_common.hs_worlds.
Require Import WgNoise.proof.harness.hs_common.hs_globals.
Require Import WgNoise.proof.harness.hs_common.hs_asm.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol5.prot_repr5.
Require Import WgNoise.proof.protocol5.prot_specs5.
Require Import WgNoise.proof.harness.hs_response_state.hrs_spec.
Require Import WgNoise.proof.harness.hs_response_state.hrs_model.
Require Import WgNoise.proof.harness.hs_response_state.hrs_conv.
Require Import WgNoise.proof.harness.hs_response_state.hrs_close.
Local Open Scope logic.

#[local] Existing Instance W_hrs.

(* main's postcondition TT in Floyd's canonical form *)
Lemma hrs_post_canon gv : hs_post gv = PROP () LOCAL () SEP (TT).
Proof.
  extensionality rho. unfold hs_post, PROPx, LOCALx, SEPx. simpl.
  apply pred_ext; normalize.
Qed.

(* the arguments &p.a_peer.handshake etc. are the addresses of the specifications *)
Ltac hrs_addr :=
  entailer!; unfold hs_addr, kps_addr, pair_ap, pair_bp, pair_a, pair_b, field_address;
  rewrite ?if_true by auto with field_compatible; try reflexivity.

(* the projections of a call's result, in the goal and the hypotheses but not in the abbreviated POSTCONDITION *)
Ltac hrs_simpl :=
  cbn [fst snd]; repeat match goal with H: context [fst (_, _)] |- _ => cbn [fst snd] in H
                                      | H: context [snd (_, _)] |- _ => cbn [fst snd] in H end.

(* the tables of the devices of new_pair are the members of struct pair *)
Ltac hrs_tabs :=
  repeat match goal with
  | |- context [d_itab (pair_devA ?x ?p ?a)] => change (d_itab (pair_devA x p a)) with (pair_ai p)
  | |- context [d_itab (pair_devB ?x ?p ?a)] => change (d_itab (pair_devB x p a)) with (pair_bi p)
  | |- context [d_ptab (pair_devA ?x ?p ?a)] => change (d_ptab (pair_devA x p a)) with (pair_ak p)
  | |- context [d_ptab (pair_devB ?x ?p ?a)] => change (d_ptab (pair_devB x p a)) with (pair_bk p)
  end.

(* one peer is the peer list of one element *)
Lemma hrs_peers1 sh a P : peer_rep5 sh a P = peers_rep5 [(a, sh, P)].
Proof. unfold peers_rep5. simpl. rewrite sepcon_emp. reflexivity. Qed.

(* the pure preconditions on the one-peer lists of the pair (writable shares, small counters) *)
Ltac hrs_props :=
  repeat split; repeat constructor; cbn; auto with share; try apply writable_share_top; try rep_lia.

(* a peer is a valid pointer (its first field, the device pointer, is at offset 0): the test of
   consume_initiation's result against NULL is defined *)
Lemma hrs_peer_valid sh p P : sepalg.nonidentity sh -> peer_rep5 sh p P |-- valid_pointer p.
Proof.
  intros Hsh. unfold peer_rep5. Intros.
  rewrite !sepcon_assoc. apply sepcon_valid_pointer1.
  apply (@field_at_valid_ptr0 Noise.CS sh t_peer [StructField I._device] (p_device P) p Hsh);
    [simpl; lia | reflexivity].
Qed.

(* the two branches of `if (!ok) return 0;` after a step with result ok *)
Ltac hrs_fail ok := match goal with Ht: typed_true _ _ |- _ => destruct ok; [discriminate Ht |]; clear Ht end.
Ltac hrs_succ ok := match goal with Ht: typed_false _ _ |- _ => destruct ok; [| discriminate Ht]; clear Ht end.

Lemma hrs_insert_table sh pa idx : t_insert (hs_table sh pa) (hs_addr pa) idx = hrs_tab sh pa idx.
Proof. apply hrs_insert0. Qed.

(* main's stack frame at a return, by hrs_close_frame (the tables' pools are computed by reflexivity) *)
Ltac hrs_close :=
  hrs_tabs;
  repeat match goal with
  | |- context [@data_at_ Noise.CS Tsh t_init ?m] => change (@data_at_ Noise.CS Tsh t_init m) with (init_opt_rep Tsh m None)
  | |- context [@data_at_ Noise.CS Tsh t_resp ?m] => change (@data_at_ Noise.CS Tsh t_resp m) with (resp_opt_rep Tsh m None)
  | |- context [init_rep5 Tsh ?m ?M] => change (init_rep5 Tsh m M) with (init_opt_rep Tsh m (Some M))
  | |- context [resp_rep5 Tsh ?m ?M] => change (resp_rep5 Tsh m M) with (resp_opt_rep Tsh m (Some M))
  end;
  match goal with
  | |- context [init_opt_rep Tsh ?m ?Mo] =>
  match goal with
  | |- context [resp_opt_rep Tsh ?r ?Ro] =>
  match goal with
  | |- context [device_rep5 Tsh (pair_a ?p) ?DA] =>
  match goal with
  | |- context [device_rep5 Tsh (pair_b p) ?DB] =>
  match goal with
  | |- context [itable Tsh (pair_ai p) ?TA] =>
  match goal with
  | |- context [itable Tsh (pair_bi p) ?TB] =>
  match goal with
  | |- context [ptable Tsh (pair_ak p) ?ka] =>
  match goal with
  | |- context [ptable Tsh (pair_bk p) ?kb] =>
  match goal with
  | |- context [peer_rep5 Tsh (pair_ap p) ?PA] =>
  match goal with
  | |- context [peer_rep5 Tsh (pair_bp p) ?PB] =>
    sep_apply (hrs_close_frame p m r Mo Ro DA DB TA TB ka kb PA PB); try reflexivity; cancel
  end end end end end end end end end end.

(* A's peer again, after main's store of its handshake's state *)
Ltac hrs_rejoin Hfc :=
  match goal with |- context [@field_at _ ?sh (Tstruct HRS._pair noattr)
                     [StructField HRS._state; StructField HRS._handshake; StructField HRS._a_peer] (Vint ?s) ?p] =>
    match goal with |- context [hrs_peer_rest sh (pair_ap p) ?P] =>
      fold (hrs_state_at sh (Vint s) p); sep_apply (hrs_peer_join sh p P s Hfc)
    end
  end.

Lemma hrs_main_body x25519 aead_enc aead_dec :
  x25519_props x25519 -> aead_props aead_enc aead_dec ->
  @semax_body (QPvarspecs hrs_prog) (hrs_Gmain x25519 aead_enc aead_dec) W_hrs HRS.f_main (hs_main_spec hrs_prog).
Proof.
  intros Hx Ha.
  unfold hs_main_spec, QPmain_spec_ext', NDmk_funspec.
  split3; [reflexivity | reflexivity | ]. intros Espec DTL gv.
  eapply (main_pre_InitGpred (hs_globals0 gv));
    [apply hs_init_globals_response_state | reflexivity
    | apply Forall_forall; intros x Hx'; vm_compute in Hx'; repeat destruct Hx' as [Hx'|Hx']; try contradiction; subst x; vm_compute; exact I | ].
  process_stackframe_of.
  rewrite hrs_post_canon.
  Intros. unfold HRS.f_main; simpl fn_body. abbreviate_semax.
  unfold hs_globals0. Intros.
  rewrite hrs_conv_pair, hrs_conv_init, hrs_conv_resp.
  forward_call (gv, Tsh, v_p, zeros32, zeros32, Int64.zero).
  Intros vret. destruct vret as [[araw braw] psk]. hrs_simpl.
  rename H into Hara, H0 into Hbra, H1 into Hpsk.
  forward_call (gv, hs_shim0, hs_w0).
  Intros vret. destruct vret as [[b1 rs1] rn1]. hrs_simpl.
  rename H into Hb1, H0 into Hrn1.
  unfold hs_pair. Intros. rename H into Hfc.
  (* A's initiation *)
  change (@data_at_ Noise.CS Tsh t_init v_initiation) with (init_opt_rep Tsh v_initiation None).
  forward_call (gv, shim_clocks hs_shim0 b1 rs1 rn1, hs_w0, Int64.zero, Tsh, v_initiation, @None init_msg, Tsh,
                pair_ap v_p, pair_peerA x25519 v_p araw braw psk, Tsh, pair_a v_p, pair_devA x25519 v_p araw, Tsh,
                hs_table Tsh (pair_ap v_p)).
  { hrs_addr. }
  { apply hrs_table0_in_pool. }
  Intros vret. destruct vret as [r1 idx1]. hrs_simpl.
  change (init_of None) with init_msg0 in *.
  destruct (ci_res x25519 aead_enc (pair_devA x25519 v_p araw) (pair_peerA x25519 v_p araw braw psk)
              init_msg0 (shim_clocks hs_shim0 b1 rs1 rn1) r1 idx1) as [[ok1 M1] HA1] eqn:Eci1.
  hrs_simpl.
  forward_if.
  { hrs_fail ok1. forward. hrs_close. }
  hrs_succ ok1.
  rewrite hrs_insert_table. hrs_tabs.
  change (init_opt_rep Tsh v_initiation (opt_after true None M1)) with (init_rep5 Tsh v_initiation M1).
  match goal with |- context [shim_state4 gv ?S hs_w0] => set (S2 := S) end.
  (* B consumes the initiation *)
  rewrite (hrs_peers1 Tsh (pair_bp v_p)).
  forward_call (gv, S2, hs_w0, Int64.zero, Tsh, v_initiation, M1, Tsh, pair_b v_p, pair_devB x25519 v_p braw, Tsh,
                pair_bp v_p, [(pair_bp v_p, Tsh, pair_peerB x25519 v_p araw braw psk)]).
  { hrs_addr. }
  { hrs_props. }
  destruct (cin_res x25519 aead_dec (pair_devB x25519 v_p braw)
              [(pair_bp v_p, Tsh, pair_peerB x25519 v_p araw braw psk)] M1 S2) as [[b PB1]|] eqn:Ecin.
  2: { cbn [peer_result peers_after]. rewrite <- hrs_peers1.
       forward_if.
       { forward. hrs_close. }
       contradiction. }
  assert (Hpb: isptr (pair_bp v_p)) by (unfold pair_bp; apply field_address_isptr; auto with field_compatible).
  unfold cin_res, prot_specs4.cin_res in Ecin.
  destruct (hrs_cin_single x25519 aead_dec _ _ _ _ _ _ _ _ Ecin) as [-> HdB].
  cbn [peer_result peers_after supd]. rewrite if_true by reflexivity. rewrite <- hrs_peers1.
  forward_if.
  { sep_apply (hrs_peer_valid Tsh (pair_bp v_p) PB1); [auto with share |]. entailer!. }
  { match goal with E: pair_bp v_p = nullval |- _ => rewrite E in Hpb; contradiction end. }
  (* B's response *)
  hrs_tabs.
  change (@data_at_ Noise.CS Tsh t_resp v_response) with (resp_opt_rep Tsh v_response None).
  forward_call (gv, S2, hs_w0, Tsh, v_response, @None resp_msg, Tsh, pair_bp v_p, PB1, Tsh, pair_b v_p,
                pair_devB x25519 v_p braw, Tsh, hs_table Tsh (pair_bp v_p)).
  { hrs_addr. }
  { repeat split; first [apply hrs_table0_in_pool | rewrite HdB; reflexivity]. }
  Intros vret. destruct vret as [r2 idx2]. hrs_simpl.
  change (resp_of None) with resp_msg0 in *.
  destruct (cr_res x25519 aead_enc PB1 resp_msg0 r2 idx2) as [[ok3 MR] HB2] eqn:Ecr. hrs_simpl.
  forward_if.
  { hrs_fail ok3. forward. hrs_close. }
  hrs_succ ok3.
  rewrite hrs_insert_table. hrs_tabs.
  change (resp_opt_rep Tsh v_response (opt_after true None MR)) with (resp_rep5 Tsh v_response MR).
  match goal with |- context [shim_state4 gv ?S hs_w0] => set (S3 := S) end.
  (* A's handshake in any state *)
  forward_call tt. Intros st.
  set (PA1 := p_set_hs (pair_peerA x25519 v_p araw braw psk) HA1).
  rewrite (hrs_peer_split Tsh v_p PA1 Hfc). Intros. unfold hrs_state_at.
  forward.
  forward.
  forward_if.
  { forward.
    hrs_rejoin Hfc. hrs_close. }
  (* A consumes B's response: its handshake is not waiting for one *)
  hrs_rejoin Hfc. subst PA1.
  rewrite (hrs_peers1 Tsh (pair_ap v_p)).
  forward_call (gv, S3, hs_w0, Tsh, v_response, MR, Tsh, pair_a v_p, pair_devA x25519 v_p araw, Tsh,
                hrs_tab Tsh (pair_ap v_p) idx1,
                [(pair_ap v_p, Tsh, p_set_hs (p_set_hs (pair_peerA x25519 v_p araw braw psk) HA1)
                                      (hs_set_state (p_hs (p_set_hs (pair_peerA x25519 v_p araw braw psk) HA1))
                                                    (Int.repr st)))]).
  { hrs_addr. }
  { split; [apply hrs_pool_peers_ok; apply Int.one_not_zero | hrs_props]. }
  unfold cre_res, prot_specs4.cre_res.
  rewrite hrs_cre_none.
  2: { cbn. unfold HS_CREATED_INITIATION. apply Int.eq_false. intros E. apply H5.
       apply repr_inj_unsigned in E; rep_lia. }
  cbn [peer_result peers_after]. rewrite <- hrs_peers1.
  (* the check *)
  forward_call Int.one.
  forward.
  hrs_close.
Qed.
