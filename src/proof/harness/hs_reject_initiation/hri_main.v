(* Law hs_reject_initiation: main's body. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise.
Require WgNoise.proof.assembly.asm_env.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol5.prot_repr5.
Require Import WgNoise.proof.protocol5.prot_specs5.
Require Import WgNoise.proof.harness.hs_common.hs_specs.
Require Import WgNoise.proof.harness.hs_common.hs_itable1.
Require Import WgNoise.proof.harness.hs_common.hs_close.
Require Import WgNoise.proof.harness.hs_common.hs_close_snap.
Require Import WgNoise.proof.harness.hs_reject_initiation.hri_spec.
Require Import WgNoise.proof.harness.hs_reject_initiation.hri_lemmas.
Require WgNoise.contracts.hs_reject_initiation.

#[local] Existing Instance CSh.
Local Open Scope Z_scope.

(* a field of a struct with its default value is uninitialised memory of the field's type *)
Ltac hri_open f := match goal with |- context [field_at ?sh ?t (DOT f) ?v ?p] =>
  change (field_at sh t (DOT f) v p) with (field_at_ sh t (DOT f) p); rewrite (field_at__data_at_ sh t (DOT f) p) end.

Section Main.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variables (S0: shim) (w0: list int64) (h0 ck0: list byte) (kc0: int64).

(* the initial globals hold the shim's state, noise.c's globals (before wg_noise_init) and the primitives'
   constants *)
Hypothesis HG: forall gv, globals_ok gv ->
  InitGPred (Vardefs WgNoise.contracts.hs_reject_initiation.whole_prog) gv |--
  (shim_state4 gv S0 w0 * noise_globals_raw gv h0 ck0 kc0 * wg_consts5 gv * TT)%logic.

Lemma hri_main_body :
  @semax_body hri_V (hri_G x25519 aead_enc aead_dec) CSh H.f_main hri_main_spec.
Proof.
  unfold hri_main_spec, QPmain_spec_ext', NDmk_funspec.
  split3; [reflexivity | reflexivity | ]. intros Espec DTL gv.
  eapply (main_pre_InitGpred (shim_state4 gv S0 w0 * noise_globals_raw gv h0 ck0 kc0 * wg_consts5 gv * TT)%logic);
    [apply HG | reflexivity
    | apply Forall_forall; intros x Hx; vm_compute in Hx; repeat destruct Hx as [Hx|Hx]; try contradiction; subst x; vm_compute; exact I | ].
  process_stackframe_of.
  Intros. unfold H.f_main; simpl fn_body. abbreviate_semax.
  forward_call (gv, Tsh, v_p, h0, ck0, kc0).
  Intros vret. destruct vret as [[araw braw] psk]. simpl fst in *; simpl snd in *.
  forward_call (gv, S0, w0).
  Intros vret. destruct vret as [[b rs] rn]. simpl fst in *; simpl snd in *.
  (* the message: any bytes *)
  unfold_data_at (data_at_ Tsh (Tstruct H._message_handshake_initiation noattr) v_message).
  forward_call. Intros t1. forward.
  forward_call. Intros t2. forward.
  hri_open H._unencrypted_ephemeral.
  forward_call (field_address (Tstruct H._message_handshake_initiation noattr) (DOT H._unencrypted_ephemeral) v_message, 32, Tsh).
  Intros eph.
  hri_open H._encrypted_static.
  forward_call (field_address (Tstruct H._message_handshake_initiation noattr) (DOT H._encrypted_static) v_message, 48, Tsh).
  Intros encs.
  hri_open H._encrypted_timestamp.
  forward_call (field_address (Tstruct H._message_handshake_initiation noattr) (DOT H._encrypted_timestamp) v_message, 28, Tsh).
  Intros enct.
  hri_open H._macs.
  unfold_data_at (data_at_ Tsh (nested_field_type (Tstruct H._message_handshake_initiation noattr) (DOT H._macs)) _).
  hri_open H._mac1.
  forward_call (field_address (Tstruct H._message_handshake_initiation noattr) (DOT H._macs DOT H._mac1) v_message, 16, Tsh).
  { change [StructField H._mac1; StructField H._macs] with ([StructField H._mac1] ++ [StructField H._macs]).
    rewrite field_address_app. simpl nested_field_type. cancel. }
  Intros mac1.
  hri_open H._mac2.
  forward_call (field_address (Tstruct H._message_handshake_initiation noattr) (DOT H._macs DOT H._mac2) v_message, 16, Tsh).
  { change [StructField H._mac2; StructField H._macs] with ([StructField H._mac2] ++ [StructField H._macs]).
    rewrite field_address_app. simpl nested_field_type. cancel. }
  Intros mac2.
  sep_apply (hri_msg_fold Tsh v_message t1 t2 eph encs enct (map (fun b => Vint (Int.repr b)) mac1)
               (map (fun b => Vint (Int.repr b)) mac2)); auto.
  set (M := hri_msg t1 t2 eph encs enct).
  (* the devices, tables and peers of the pair *)
  unfold hs_pair. Intros.
  (* A's initiation, or not: afterwards the message is some message, A's peer and table some state *)
  forward_call. Intros t3.
  forward_if (PROP () LOCAL (lvar H._before (Tstruct H._wg_peer noattr) v_before;
      lvar H._message (Tstruct H._message_handshake_initiation noattr) v_message;
      lvar H._p (Tstruct H._pair noattr) v_p; gvars gv)
    SEP (EX M2: init_msg, EX PA: peer, EX TA: tstate, EX S1: shim,
           !!(exists EA, t_D TA = [(hs_addr (pair_ap v_p), Tsh, EA)]) &&
           (init_rep5 Tsh v_message M2 * peer_rep5 Tsh (pair_ap v_p) PA * itable Tsh (pair_ai v_p) TA *
            shim_state4 gv S1 w0);
         device_rep5 Tsh (pair_a v_p) (pair_devA x25519 v_p araw);
         device_rep5 Tsh (pair_b v_p) (pair_devB x25519 v_p braw);
         itable Tsh (pair_bi v_p) (hs_table Tsh (pair_bp v_p));
         ptable Tsh (pair_ak v_p) (pair_ap v_p); ptable Tsh (pair_bk v_p) (pair_bp v_p);
         peer_rep5 Tsh (pair_bp v_p) (pair_peerB x25519 v_p araw braw psk);
         noise_globals gv kc0; wg_consts5 gv; data_at_ Tsh (Tstruct H._wg_peer noattr) v_before; TT; has_ext tt)).
  - forward_call (gv, shim_clocks S0 b rs rn, w0, kc0, Tsh, v_message, Some M, Tsh, pair_ap v_p,
                  pair_peerA x25519 v_p araw braw psk, Tsh, pair_a v_p, pair_devA x25519 v_p araw, Tsh,
                  hs_table Tsh (pair_ap v_p)).
    + entailer!. unfold hs_addr, pair_ap. rewrite field_address_offset by auto with field_compatible.
      simpl. reflexivity.
    + exists (mkEntry (pair_ap v_p) IDX_HANDSHAKE Int.zero). unfold t_entry, hs_table; simpl.
      rewrite if_true by reflexivity. auto.
    + Intros vret. destruct vret as [r idx]. simpl fst in *; simpl snd in *.
      destruct (ci_res x25519 aead_enc (pair_devA x25519 v_p araw) (pair_peerA x25519 v_p araw braw psk)
                  (init_of (Some M)) (shim_clocks S0 b rs rn) r idx) as [[ok M'] H'] eqn:Eci.
      simpl fst in *; simpl snd in *.
      Exists M' (p_set_hs (pair_peerA x25519 v_p araw braw psk) H')
        (if ok then t_insert (hs_table Tsh (pair_ap v_p)) (hs_addr (pair_ap v_p)) idx else hs_table Tsh (pair_ap v_p))
        (if id_has (d_id (pair_devA x25519 v_p araw))
         then if ok then shim_u32 (shim_draw (shim_clocks S0 b rs rn) r) idx else shim_draw (shim_clocks S0 b rs rn) r
         else shim_clocks S0 b rs rn).
      change (d_itab (pair_devA x25519 v_p araw)) with (pair_ai v_p).
      entailer!.
      * destruct ok; [apply hri_tD_insert | eexists; reflexivity].
      * change (init_of (Some M)) with M in Eci. rewrite Eci. destruct ok; simpl; cancel.
  - forward.
    Exists M (pair_peerA x25519 v_p araw braw psk) (hs_table Tsh (pair_ap v_p)) (shim_clocks S0 b rs rn).
    entailer!. eexists; reflexivity.
  - Intros M2 PA TA S1.
    (* any state of B's handshake with A *)
    forward.
    match goal with |- context [temp H._h ?v] => replace v with (hs_addr (pair_bp v_p))
      by (unfold hs_addr, pair_bp; rewrite field_address_offset by auto with field_compatible; simpl; reflexivity) end.
    rewrite (hri_peer_split Tsh (pair_bp v_p)).
    unfold hs_rep. Intros lk.
    repeat match goal with |- context [@field_at Noise.CS ?sh t_hs ?gfs ?v ?p] =>
      erewrite (@field_at_change_composite Noise.CS CSh _ sh t_hs gfs v v) by (first [apply JMeq_refl | reflexivity]) end.
    assert_PROP (field_compatible t_hs [] (hs_addr (pair_bp v_p))) as FCh.
    { entailer!. match goal with Hf: field_compatible t_hs (DOT I._state) _ |- _ => destruct Hf as (? & ? & ? & ? & ? & ?) end.
      split3; auto; split3; auto; exact I. }
    forward_call. Intros t4. forward.
    forward_call. Intros t5. forward.
    forward_call. Intros t6. forward.
    rewrite (field_at_data_at Tsh t_hs (DOT I._ephemeral_private)).
    forward_call (field_address t_hs (DOT I._ephemeral_private) (hs_addr (pair_bp v_p)), 32, Tsh).
    Intros eph_b.
    rewrite (field_at_data_at Tsh t_hs (DOT I._remote_ephemeral)).
    forward_call (field_address t_hs (DOT I._remote_ephemeral) (hs_addr (pair_bp v_p)), 32, Tsh).
    Intros reph_b.
    rewrite (field_at_data_at Tsh t_hs (DOT I._hash)).
    forward_call (field_address t_hs (DOT I._hash) (hs_addr (pair_bp v_p)), 32, Tsh).
    Intros hash_b.
    rewrite (field_at_data_at Tsh t_hs (DOT I._chaining_key)).
    forward_call (field_address t_hs (DOT I._chaining_key) (hs_addr (pair_bp v_p)), 32, Tsh).
    Intros ck_b.
    rewrite (field_at_data_at Tsh t_hs (DOT I._latest_timestamp)).
    forward_call (field_address t_hs (DOT I._latest_timestamp) (hs_addr (pair_bp v_p)), 12, Tsh).
    Intros ts_b.
    set (H0B := p_hs (pair_peerB x25519 v_p araw braw psk)) in *.
    set (HB := mkHS (Int.repr t4) (Int64.shru t6 (Int64.repr (Int.unsigned (Int.repr 2)))) (hs_sid H0B)
                 (map Byte.repr eph_b) (hs_rstatic H0B) (map Byte.repr reph_b) (hs_ss H0B) (hs_psk H0B)
                 (map Byte.repr hash_b) (map Byte.repr ck_b) (map Byte.repr ts_b) (Int.repr t5)).
    rewrite !hri_bytes by auto.
    sep_apply (hri_hs_fold Tsh (hs_addr (pair_bp v_p)) HB lk).
    { destruct H19 as (? & ? & ? & ? & ? & ? & ? & ?). unfold hs_ok; simpl; rewrite !Zlength_map; auto 10. }
    sep_apply (hri_peer_join Tsh (pair_bp v_p) (pair_peerB x25519 v_p araw braw psk) HB).
    set (PB := p_set_hs (pair_peerB x25519 v_p araw braw psk) HB).
    (* the copy *)
    unfold hs_table.
    set (EB := mkEntry (pair_bp v_p) IDX_HANDSHAKE Int.zero).
    rewrite (hs_itable1_unhashed Tsh (pair_bi v_p) (hs_addr (pair_bp v_p)) Tsh EB). Intros.
    rewrite <- (@data_at__change_composite Noise.CS CSh _ Tsh (Tstruct H._wg_peer noattr)) by reflexivity.
    assert (Pvp: isptr v_p) by (destruct H16; auto).
    forward_call (Tsh, v_before, Tsh, pair_bp v_p, PB, Tsh, EB, nullval, false).
    { entailer!. unfold pair_bp. rewrite field_address_offset by auto with field_compatible. simpl. reflexivity. }
    { subst PB HB H0B; simpl. unfold id_addr, pair_b. rewrite field_address_offset by auto with field_compatible.
      destruct v_p; try contradiction; exact I. }
    (* B consumes the message *)
    rewrite <- (hri_peers1 (pair_bp v_p) Tsh PB).
    forward_call (gv, S1, w0, kc0, Tsh, v_message, M2, Tsh, pair_b v_p, pair_devB x25519 v_p braw, Tsh, pair_bp v_p,
                  [(pair_bp v_p, Tsh, PB)]).
    { entailer!. unfold pair_b. rewrite field_address_offset by auto with field_compatible. simpl. reflexivity. }
    { unfold peers_wf, peers_refs_ok. split; [| split; [| split]].
      - constructor; [apply writable_share_top | constructor].
      - simpl; split; reflexivity.
      - constructor; [simpl; apply hri_lic_ok | constructor].
      - constructor; [simpl; rewrite Int.unsigned_one; lia | constructor]. }
    change (d_ptab (pair_devB x25519 v_p braw)) with (pair_bk v_p).
    assert (Pbp: isptr (pair_bp v_p)).
    { unfold pair_bp. rewrite field_address_offset by auto with field_compatible. destruct v_p; try contradiction; exact I. }
    (* the check: on rejection (NULL), B's peer is as copied *)
    forward_if (PROP () LOCAL (lvar H._before (Tstruct H._wg_peer noattr) v_before;
        lvar H._message (Tstruct H._message_handshake_initiation noattr) v_message;
        lvar H._p (Tstruct H._pair noattr) v_p; gvars gv)
      SEP (EX PB2: peer, peer_rep5 Tsh (pair_bp v_p) PB2;
           init_rep5 Tsh v_message M2; device_rep5 Tsh (pair_b v_p) (pair_devB x25519 v_p braw);
           ptable Tsh (pair_bk v_p) (pair_bp v_p); shim_state4 gv S1 w0; noise_globals gv kc0; wg_consts5 gv;
           snap_rep Tsh v_before PB EB nullval false; entry_at Tsh (hs_addr (pair_bp v_p)) EB nullval false;
           peer_rep5 Tsh (pair_ap v_p) PA; itable Tsh (pair_ai v_p) TA;
           device_rep5 Tsh (pair_a v_p) (pair_devA x25519 v_p araw);
           data_at Tsh t_itab nullval (pair_bi v_p); ptable Tsh (pair_ak v_p) (pair_ap v_p); TT; has_ext tt)).
    + (* comparing the result with NULL is defined: NULL or B's peer *)
      destruct (cin_res x25519 aead_dec (pair_devB x25519 v_p braw) [(pair_bp v_p, Tsh, PB)] M2 S1) as [[a P'] |] eqn:ER.
      2: { simpl. apply denote_tc_test_eq_split; apply valid_pointer_null. }
      pose proof (hri_cin_some _ _ _ _ _ _ _ _ _ _ ER) as Ea. subst a.
      simpl peers_after. simpl peer_result. rewrite if_true by reflexivity. rewrite hri_peers1.
      unfold peer_rep5 at 1. Intros.
      apply denote_tc_test_eq_split; [| apply valid_pointer_null].
      sep_apply (field_at_valid_ptr0 Tsh t_peer (DOT I._device) (p_device P') (pair_bp v_p)); auto; [entailer! ..].
    + (* rejected: B's peer is as before, so same_peer says so *)
      destruct (cin_res x25519 aead_dec (pair_devB x25519 v_p braw) [(pair_bp v_p, Tsh, PB)] M2 S1) as [[a P'] |] eqn:ER.
      { pose proof (hri_cin_some _ _ _ _ _ _ _ _ _ _ ER) as Ea. subst a. simpl in H33. rewrite H33 in Pbp. contradiction. }
      simpl peers_after. rewrite hri_peers1.
      rewrite (hri_dev_split Tsh (pair_b v_p)).
      change (id_addr (pair_b v_p)) with (hs_sid (p_hs PB)).
      forward_call (Tsh, pair_bp v_p, PB, Tsh, EB, false, Tsh, v_before, Tsh, d_id (pair_devB x25519 v_p braw)).
      { entailer!. unfold pair_bp. rewrite field_address_offset by auto with field_compatible. simpl. reflexivity. }
      { cancel. }
      Intros r.
      forward_call (Int.one).
      { entailer!. simpl. rewrite Int.eq_false by auto. reflexivity. }
      change (hs_sid (p_hs PB)) with (id_addr (pair_b v_p)).
      Exists PB. rewrite (hri_dev_split Tsh (pair_b v_p)). entailer!.
    + (* accepted: nothing to check *)
      forward.
      destruct (cin_res x25519 aead_dec (pair_devB x25519 v_p braw) [(pair_bp v_p, Tsh, PB)] M2 S1) as [[a P'] |] eqn:ER.
      2: { simpl in H33. contradiction. }
      pose proof (hri_cin_some _ _ _ _ _ _ _ _ _ _ ER) as Ea. subst a.
      simpl peers_after. rewrite if_true by reflexivity. rewrite hri_peers1.
      Exists P'. entailer!.
    + (* return: the stack frame is freed (struct pair, the message, the copy) *)
      Intros PB2.
      unfold abbreviate in POSTCONDITION. subst POSTCONDITION. unfold hri_post.
      replace (fun _ : environ => @TT mpred _) with (PROP () LOCAL () SEP (TT))%assert
        by (extensionality rho; unfold PROPx, LOCALx, SEPx; simpl; normalize).
      abbreviate_semax.
      forward.
      sep_apply (hs_close_snap Tsh v_before PB EB nullval false).
      sep_apply (hs_close_init Tsh v_message M2).
      assert (Hit: data_at Tsh t_itab nullval (pair_bi v_p) * entry_at Tsh (hs_addr (pair_bp v_p)) EB nullval false |--
                   itable Tsh (pair_bi v_p) (mkT [(hs_addr (pair_bp v_p), Tsh, EB)] [])).
      { rewrite hs_itable1_unhashed. entailer!. }
      sep_apply Hit.
      destruct H18 as [EA HEA].
      sep_apply (hs_pair_close Tsh v_p (pair_devA x25519 v_p araw) (pair_devB x25519 v_p braw) TA
                   (mkT [(hs_addr (pair_bp v_p), Tsh, EB)] []) (pair_ap v_p) (pair_bp v_p) PA PB2 EA EB
                   H16 HEA eq_refl).
      rewrite <- (@data_at__change_composite Noise.CS CSh _ Tsh (Tstruct H._wg_peer noattr)) by reflexivity.
      rewrite <- (@data_at__change_composite Noise.CS CSh _ Tsh (Tstruct H._message_handshake_initiation noattr))
        by reflexivity.
      cancel.
Qed.

End Main.
