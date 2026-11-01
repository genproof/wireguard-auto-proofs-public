(* The law hs_reject_response (harness/hs_reject_response.c): main's body. *)
Require WgNoise.proof.assembly.asm_env.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol5.prot_repr5.
Require Import WgNoise.proof.protocol5.prot_specs5.
Require Import WgNoise.proof.harness.hs_common.hs_specs.
Require Import WgNoise.proof.harness.hs_common.hs_worlds.
Require Import WgNoise.proof.harness.hs_common.hs_globals.
Require Import WgNoise.proof.harness.hs_common.hs_asm.
Require Import WgNoise.proof.harness.hs_common.hs_itable1.
Require Import WgNoise.proof.harness.hs_common.hs_close.
Require Import WgNoise.proof.harness.hs_common.hs_close_snap.
Require Import WgNoise.proof.harness.hs_reject_response.hrr_model.
Require Import WgNoise.proof.harness.hs_reject_response.hrr_spec.
Require Import WgNoise.proof.harness.hs_reject_response.hrr_conv.
Require Import WgNoise.proof.harness.hs_reject_response.hrr_msg.
Local Open Scope logic.

#[local] Existing Instance W_hs_reject_response.

Section Main.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).

Lemma hrr_main_body :
  semax_body (QPvarspecs p_rr) (hrr_G x25519 aead_enc aead_dec) R.f_main (hs_main_spec p_rr).
Proof.
  unfold hs_main_spec, QPmain_spec_ext', NDmk_funspec.
  split3; [reflexivity | reflexivity | ]. intros Espec DTL gv.
  eapply (main_pre_InitGpred (hs_globals0 gv));
    [apply hs_init_globals_reject_response | reflexivity
    | apply Forall_forall; intros x Hx; vm_compute in Hx; repeat destruct Hx as [Hx|Hx]; try contradiction; subst x; vm_compute; exact I | ].
  unfold hs_globals0.
  process_stackframe_of.
  replace (data_at_ Tsh (Tstruct R._pair noattr) v_p) with (@data_at_ CSh Tsh t_pair v_p)
    by (rewrite hrr_conv_pair; reflexivity).
  replace (data_at_ Tsh (Tstruct R._message_handshake_initiation noattr) v_initiation)
    with (@data_at_ Noise.CS Tsh t_init v_initiation) by (rewrite hrr_conv_init; reflexivity).
  Intros. unfold fn_body, R.f_main, fn_return. abbreviate_semax.
  (* new_pair, any_clocks *)
  forward_call (gv, Tsh, v_p, zeros32, zeros32, Int64.zero).
  Intros vret. destruct vret as [[araw braw] psk]. cbn [fst snd] in *.
  forward_call (gv, hs_shim0, hs_w0).
  Intros vret. destruct vret as [[b rs] rn]. cbn [fst snd] in *.
  unfold hs_pair. Intros.
  match goal with Hf: field_compatible t_pair [] v_p |- _ => rename Hf into Hfp end.
  pose proof (hrr_pair_addrs v_p Hfp) as Eaddr.
  set (DA := pair_devA x25519 v_p araw). set (DB := pair_devB x25519 v_p braw).
  set (PA0 := pair_peerA x25519 v_p araw braw psk). set (PB0 := pair_peerB x25519 v_p araw braw psk).
  set (S1 := shim_clocks hs_shim0 b rs rn).
  (* A's initiation *)
  forward_call (gv, S1, hs_w0, Int64.zero, Tsh, v_initiation, @None init_msg, Tsh, pair_ap v_p, PA0,
                Tsh, pair_a v_p, DA, Tsh, hs_table Tsh (pair_ap v_p)).
  { entailer!. destruct Eaddr as (_&_&_&_&_&_&Eap&_). rewrite Eap. unfold hs_addr, OFS_PEER_HANDSHAKE. simpl.
    rewrite offset_offset_val. reflexivity. }
  { exists (mkEntry (pair_ap v_p) IDX_HANDSHAKE Int.zero). unfold hs_table, t_entry. cbn [t_D sfind].
    rewrite if_true by reflexivity. split; reflexivity. }
  Intros vret. destruct vret as [r idx]. cbn [fst snd] in *.
  set (CI := ci_res x25519 aead_enc DA PA0 (init_of None) S1 r idx) in *.
  set (ok := fst (fst CI)) in *.
  (* the initiation keeps A's static identity pointer *)
  assert (Hsid: hs_sid (snd CI) = hs_sid (p_hs PA0)) by (subst CI; apply hrr_ci_sid).
  clearbody ok CI.
  (* any message *)
  sep_apply (hrr_resp_split Tsh v_message). Intros.
  forward_call tt. Intros n1. forward.
  forward_call tt. Intros n2. forward.
  forward_call tt. Intros n3. forward.
  forward_call (offset_val 12 v_message, 32, Tsh). Intros e.
  forward_call (offset_val 44 v_message, 16, Tsh). Intros en.
  forward_call (offset_val 60 v_message, 16, Tsh). Intros mac1.
  forward_call (offset_val 76 v_message, 16, Tsh). Intros mac2.
  match goal with He: Forall _ e, Hn: Forall _ en |- _ => rewrite (hrr_nd_bytes e He), (hrr_nd_bytes en Hn) end.
  (* t'5 := initiated && (nondet_u8() & 1) *)
  freeze [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15;16;17;18;19;20;21] FR1.
  forward_if (EX c: bool, PROP (c = true -> ok = true)
     LOCAL (temp R._t'5 (Val.of_bool c); temp R._initiated (Val.of_bool ok);
            lvar R._before (Tstruct R._wg_peer noattr) v_before;
            lvar R._message (Tstruct R._message_handshake_response noattr) v_message;
            lvar R._initiation (Tstruct R._message_handshake_initiation noattr) v_initiation;
            lvar R._p (Tstruct R._pair noattr) v_p; gvars gv)
     SEP (FRZL FR1)).
  { match goal with Ht: typed_true _ _ |- _ =>
      assert (Hok: ok = true) by (destruct ok; [reflexivity | inv Ht]) end.
    forward_call tt. Intros u. forward.
    Exists (negb (Int.eq (Int.and (Int.repr u) (Int.repr 1)) Int.zero)).
    entailer!. destruct (Int.eq _ _); reflexivity. }
  { forward. Exists false. entailer!. }
  Intros c5. thaw FR1.
  (* if (t'5) message.receiver_index = initiation.sender_index *)
  freeze [0;1;2;3;4;5;8;9;10;11;12;13;14;15;16;17;18;19;20;21] FR2.
  forward_if (EX rcv: int, PROP ()
     LOCAL (temp R._initiated (Val.of_bool ok);
            lvar R._before (Tstruct R._wg_peer noattr) v_before;
            lvar R._message (Tstruct R._message_handshake_response noattr) v_message;
            lvar R._initiation (Tstruct R._message_handshake_initiation noattr) v_initiation;
            lvar R._p (Tstruct R._pair noattr) v_p; gvars gv)
     SEP (FRZL FR2; init_opt_rep Tsh v_initiation (opt_after ok None (snd (fst CI)));
          field_at Tsh t_resp (DOT I._receiver_index) (Vint rcv) v_message))%assert.
  { assert (Hok: ok = true) by (destruct c5; [auto | match goal with Ht: typed_true _ _ |- _ => inv Ht end]).
    subst ok. cbn [opt_after init_opt_rep]. unfold init_rep5. Intros.
    rewrite (@field_at_change_composite Noise.CS W_hs_reject_response _ Tsh t_init (DOT I._sender_index)
               _ _ (JMeq_refl (Vint (im_sender (snd (fst CI)))))) by reflexivity.
    forward. forward. Exists (im_sender (snd (fst CI))).
    rewrite <- (@field_at_change_composite Noise.CS W_hs_reject_response _ Tsh t_init (DOT I._sender_index)
               _ _ (JMeq_refl (Vint (im_sender (snd (fst CI)))))) by reflexivity.
    entailer!. cbn [opt_after init_opt_rep]. unfold init_rep5. entailer!. }
  { forward. Exists (Int.repr n3). entailer!. }
  Intros rcv. thaw FR2.
  sep_apply (hrr_resp_fold Tsh v_message (Int.repr n1) (Int.repr n2) rcv (map Byte.repr e) (map Byte.repr en)
               (map (fun b0 => Vint (Int.repr b0)) mac1) (map (fun b0 => Vint (Int.repr b0)) mac2)
               ltac:(assumption) ltac:(rewrite Zlength_map; assumption) ltac:(rewrite Zlength_map; assumption)).
  set (M0 := mkRM (Int.repr n1) (Int.repr n2) rcv (map Byte.repr e) (map Byte.repr en) (zeros 16) (zeros 16)).
  match goal with |- context [shim_state4 gv ?S hs_w0] => set (S2 := S) end.
  (* A's state rides along *)
  freeze [1;2;3;9;12;13;14] FRA.
  (* t'7 := initiated && (nondet_u8() & 1) *)
  freeze [0;1;2;3;4;5;6;7;8;9] FR1.
  forward_if (EX c: bool, PROP (c = true -> ok = true)
     LOCAL (temp R._t'7 (Val.of_bool c); temp R._initiated (Val.of_bool ok);
            lvar R._before (Tstruct R._wg_peer noattr) v_before;
            lvar R._message (Tstruct R._message_handshake_response noattr) v_message;
            lvar R._initiation (Tstruct R._message_handshake_initiation noattr) v_initiation;
            lvar R._p (Tstruct R._pair noattr) v_p; gvars gv)
     SEP (FRZL FR1)).
  { match goal with Ht: typed_true _ _ |- _ =>
      assert (Hok: ok = true) by (destruct ok; [reflexivity | inv Ht]) end.
    forward_call tt. Intros u. forward.
    Exists (negb (Int.eq (Int.and (Int.repr u) (Int.repr 1)) Int.zero)).
    entailer!. destruct (Int.eq _ _); reflexivity. }
  { forward. Exists false. entailer!. }
  Intros c7. thaw FR1.
  (* t'9 := t'7 && consume_initiation(&initiation, &p.b) != NULL: B consumes A's initiation *)
  freeze [0;1;6] FR3.
  forward_if ((EX c: bool, EX PB1: peer, PROP (p_device PB1 = pair_b v_p)
     LOCAL (temp R._t'9 (Val.of_bool c); temp R._initiated (Val.of_bool ok);
            lvar R._before (Tstruct R._wg_peer noattr) v_before;
            lvar R._message (Tstruct R._message_handshake_response noattr) v_message;
            lvar R._initiation (Tstruct R._message_handshake_initiation noattr) v_initiation;
            lvar R._p (Tstruct R._pair noattr) v_p; gvars gv)
     SEP (FRZL FR3; init_opt_rep Tsh v_initiation (opt_after ok None (snd (fst CI)));
          device_rep5 Tsh (pair_b v_p) DB; ptable Tsh (pair_bk v_p) (pair_bp v_p);
          peer_rep5 Tsh (pair_bp v_p) PB1; shim_state4 gv S2 hs_w0; noise_globals gv Int64.zero;
          wg_consts5 gv))%assert).
  { assert (Hok: ok = true) by (destruct c7; [auto | match goal with Ht: typed_true _ _ |- _ => inv Ht end]).
    subst ok. cbn [opt_after init_opt_rep].
    replace (peer_rep5 Tsh (pair_bp v_p) PB0) with (peers_rep5 [(pair_bp v_p, Tsh, PB0)])
      by (unfold peers_rep5; simpl; apply sepcon_emp).
    forward_call (gv, S2, hs_w0, Int64.zero, Tsh, v_initiation, snd (fst CI), Tsh, pair_b v_p, DB, Tsh,
                  pair_bp v_p, [(pair_bp v_p, Tsh, PB0)]).
    { entailer!. destruct Eaddr as (_&Ebv&_). rewrite Ebv. simpl. reflexivity. }
    { split; [constructor; [apply writable_share_top | constructor] |]. split; [split; reflexivity |].
      split; (constructor; [| constructor]); cbn; [rep_lia | rewrite Int.unsigned_one; lia]. }
    destruct (cin_res x25519 aead_dec DB [(pair_bp v_p, Tsh, PB0)] (snd (fst CI)) S2) as [[a P']|] eqn:ER;
      cbn [peer_result peers_after supd].
    - unfold cin_res, prot_specs4.cin_res in ER. destruct (hrr_cin_single x25519 aead_dec _ _ _ _ _ _ _ _ ER) as [-> Hd].
      rewrite if_true by reflexivity. unfold peers_rep5, peer_item_rep5. cbn [iter_sepcon]. rewrite sepcon_emp.
      assert (Hbp: isptr (pair_bp v_p))
        by (destruct Eaddr as (_&_&_&_&_&_&_&->); destruct Hfp as [Hp _]; destruct v_p; try contradiction; exact I).
      forward.
      Exists true P'. entailer!.
      { destruct (pair_bp v_p); try contradiction; reflexivity. }
      cbn [opt_after init_opt_rep]. entailer!. all: apply derives_refl.
    - unfold peers_rep5, peer_item_rep5. cbn [iter_sepcon]. rewrite sepcon_emp. forward. Exists false PB0. entailer!. cbn [opt_after init_opt_rep]. entailer!. all: apply derives_refl. }
  { forward. Exists false PB0. entailer!. }
  Intros c9 PB1. thaw FR3.
  (* if (t'9) create_response(&message, &p.b_peer.handshake): B's response, written into the message *)
  freeze [0;3;5;8] FR4.
  forward_if ((EX M1: resp_msg, EX PB2: peer, EX TB: tstate, EX S3: shim,
     PROP (exists EB, t_D TB = [(hs_addr (pair_bp v_p), Tsh, EB)])
     LOCAL (temp R._initiated (Val.of_bool ok);
            lvar R._before (Tstruct R._wg_peer noattr) v_before;
            lvar R._message (Tstruct R._message_handshake_response noattr) v_message;
            lvar R._initiation (Tstruct R._message_handshake_initiation noattr) v_initiation;
            lvar R._p (Tstruct R._pair noattr) v_p; gvars gv)
     SEP (FRZL FR4; resp_rep5 Tsh v_message M1; peer_rep5 Tsh (pair_bp v_p) PB2;
          device_rep5 Tsh (pair_b v_p) DB; itable Tsh (pair_bi v_p) TB; shim_state4 gv S3 hs_w0;
          wg_consts5 gv))%assert).
  { replace (resp_rep5 Tsh v_message M0) with (resp_opt_rep Tsh v_message (Some M0)) by reflexivity.
    forward_call (gv, S2, hs_w0, Tsh, v_message, Some M0, Tsh, pair_bp v_p, PB1, Tsh, pair_b v_p, DB, Tsh,
                  hs_table Tsh (pair_bp v_p)).
    { entailer!. destruct Eaddr as (_&_&_&_&_&_&_&Ebp). rewrite Ebp. unfold hs_addr, OFS_PEER_HANDSHAKE. simpl.
      try rewrite offset_offset_val. reflexivity. }
    {
      exists (mkEntry (pair_bp v_p) IDX_HANDSHAKE Int.zero). unfold hs_table, t_entry. cbn [t_D sfind].
      rewrite if_true by reflexivity. split; reflexivity. }
    Intros vret. destruct vret as [r2 idx2]. cbn [fst snd] in *.
    set (CR := cr_res x25519 aead_enc PB1 (resp_of (Some M0)) r2 idx2) in *.
    assert (HTB: exists EB, t_D (if fst (fst CR) then t_insert (hs_table Tsh (pair_bp v_p)) (hs_addr (pair_bp v_p)) idx2
                                 else hs_table Tsh (pair_bp v_p)) = [(hs_addr (pair_bp v_p), Tsh, EB)]).
    { destruct (fst (fst CR)); [| eexists; reflexivity].
      destruct (hrr_insert_single (hs_addr (pair_bp v_p)) Tsh (mkEntry (pair_bp v_p) IDX_HANDSHAKE Int.zero) []
                  (hs_addr (pair_bp v_p)) idx2) as (EB & HEB & _). exists EB. exact HEB. }
    Exists (snd (fst CR)) (p_set_hs PB1 (snd CR))
      (if fst (fst CR) then t_insert (hs_table Tsh (pair_bp v_p)) (hs_addr (pair_bp v_p)) idx2
       else hs_table Tsh (pair_bp v_p))
      (if Int.eq (hs_state (p_hs PB1)) HS_CONSUMED_INITIATION
       then if fst (fst CR) then shim_u32 (shim_draw S2 r2) idx2 else shim_draw S2 r2 else S2).
    entailer!. destruct (fst (fst CR)); cbn [opt_after resp_opt_rep]; cancel; apply derives_refl. }
  { forward. Exists M0 PB1 (hs_table Tsh (pair_bp v_p)) S2. entailer!.
    exists (mkEntry (pair_bp v_p) IDX_HANDSHAKE Int.zero). reflexivity. }
  Intros M1 PB2 TB S3. thaw FR4. thaw FRA.
  match goal with HB: exists EB, t_D TB = _ |- _ => destruct HB as (EB & HDB) end.
  (* if (nondet_u8() & 1) p.a_peer.handshake.state = any: A's handshake state any value or as it is *)
  assert (HPA0: p_cur PA0 = nullval /\ p_prev PA0 = nullval /\ p_next PA0 = nullval /\ p_refs PA0 = Int.one /\
                p_device PA0 = pair_a v_p) by (repeat split; reflexivity).
  forward_call tt. Intros u12.
  freeze [1;2;3;4;5;6;7;8;9;10;11;12;13;14;15] FR5.
  forward_if ((EX PA2: peer,
     PROP (hs_sid (p_hs PA2) = hs_sid (p_hs PA0); p_cur PA2 = nullval; p_prev PA2 = nullval;
           p_next PA2 = nullval; p_refs PA2 = Int.one; p_device PA2 = pair_a v_p)
     LOCAL (temp R._initiated (Val.of_bool ok);
            lvar R._before (Tstruct R._wg_peer noattr) v_before;
            lvar R._message (Tstruct R._message_handshake_response noattr) v_message;
            lvar R._initiation (Tstruct R._message_handshake_initiation noattr) v_initiation;
            lvar R._p (Tstruct R._pair noattr) v_p; gvars gv)
     SEP (FRZL FR5; peer_rep5 Tsh (pair_ap v_p) PA2))%assert).
  { forward_call tt. Intros s11.
    unfold peer_rep5 at 1. Intros. unfold hs_rep at 1. Intros lk.
    cbn [p_hs p_set_hs].
    rewrite (hrr_state_conv Tsh v_p _ Hfp).
    forward.
    rewrite <- (hrr_state_conv Tsh v_p _ Hfp).
    Exists (p_set_hs PA0 (hs_set_state (snd CI) (Int.repr s11))).
    unfold peer_rep5, hs_rep. cbn [p_hs p_set_hs hs_set_state hs_state hs_lic hs_sid hs_eph hs_rstatic hs_reph
      hs_ss hs_psk hs_hash hs_ck hs_ts hs_rindex p_device p_dead p_cur p_prev p_next p_refs p_pknext].
    Exists lk. entailer!. }
  { forward. Exists (p_set_hs PA0 (snd CI)). entailer!. }
  Intros PA2. thaw FR5.
  (* copy_peer(&before, &p.a_peer): A's handshake entry out of its table *)
  assert (HTA: exists EA, t_D (if ok then t_insert (hs_table Tsh (pair_ap v_p)) (hs_addr (pair_ap v_p)) idx
                               else hs_table Tsh (pair_ap v_p)) = [(hs_addr (pair_ap v_p), Tsh, EA)] /\
                          e_peer EA = pair_ap v_p /\ e_type EA = IDX_HANDSHAKE).
  { destruct ok; [| eexists; split; [reflexivity | split; reflexivity]].
    destruct (hrr_insert_single (hs_addr (pair_ap v_p)) Tsh (mkEntry (pair_ap v_p) IDX_HANDSHAKE Int.zero) []
                (hs_addr (pair_ap v_p)) idx) as (EA & HEA & HE1 & HE2).
    exists EA. auto. }
  set (TA := if ok then t_insert (hs_table Tsh (pair_ap v_p)) (hs_addr (pair_ap v_p)) idx
             else hs_table Tsh (pair_ap v_p)) in *.
  destruct HTA as (EA & HDA & HEp & HEt). clearbody TA.
  rewrite (hs_itable1 Tsh (d_itab DA) TA _ _ _ HDA). Intros.
  match goal with Hw: itable_wf TA |- _ => rename Hw into HwA end.
  assert (Hnext: succ_in (t_L TA) (hs_addr (pair_ap v_p)) = nullval).
  { destruct HwA as (HN & HI & _). apply hrr_succ_single; [exact HN |]. rewrite HDA in HI. exact HI. }
  replace (data_at_ Tsh (Tstruct R._wg_peer noattr) v_before) with (@data_at_ Noise.CS Tsh t_peer v_before)
    by (rewrite hrr_conv_peer; reflexivity).
  assert (Hap: isptr (pair_ap v_p))
    by (destruct Eaddr as (_&_&_&_&_&_&->&_); destruct Hfp as [Hp _]; destruct v_p; try contradiction; exact I).
  assert (Haa: isptr (pair_a v_p))
    by (destruct Eaddr as (->&_); destruct Hfp as [Hp _]; exact Hp).
  forward_call (Tsh, v_before, Tsh, pair_ap v_p, PA2, Tsh, EA, succ_in (t_L TA) (hs_addr (pair_ap v_p)),
                vin (hs_addr (pair_ap v_p)) (t_L TA)).
  { entailer!. destruct Eaddr as (_&_&_&_&_&_&Eap&_). rewrite Eap. simpl. reflexivity. }
  (* the pointers copy_peer loads are pointers or NULL (a goal only if its specification asks for them) *)
  match goal with
  | |- semax _ _ _ _ => idtac
  | |- _ =>
    rewrite ?HEp, ?Hnext;
    match goal with Hs: hs_sid (p_hs PA2) = _, Hc: p_cur PA2 = _, Hp: p_prev PA2 = _, Hn: p_next PA2 = _ |- _ =>
      rewrite ?Hs, ?Hc, ?Hp, ?Hn end;
    change (hs_sid (p_hs PA0)) with (id_addr (pair_a v_p)); unfold id_addr;
    destruct (pair_a v_p); try contradiction; destruct (pair_ap v_p); try contradiction;
    repeat split; simpl; auto
  end.
  sep_apply (hrr_itable_fold Tsh (d_itab DA) TA _ _ _ HDA HwA).
  (* found = consume_response(&message, &p.a) *)
  replace (peer_rep5 Tsh (pair_ap v_p) PA2) with (peers_rep5 [(pair_ap v_p, Tsh, PA2)])
    by (unfold peers_rep5; simpl; apply sepcon_emp).
  forward_call (gv, S3, hs_w0, Tsh, v_message, M1, Tsh, pair_a v_p, DA, Tsh, TA, [(pair_ap v_p, Tsh, PA2)]).
  { entailer!. destruct Eaddr as (Ea&_). rewrite Ea. simpl. rewrite isptr_offset_val_zero by assumption. reflexivity. }
  { match goal with Hr: p_refs PA2 = _ |- _ => rename Hr into HrA end.
    split; [| split].
    - unfold pool_peers_ok. rewrite HDA. constructor; [| constructor]. split.
      + exists Tsh, PA2. rewrite HEp. cbn [sfind]. rewrite if_true by reflexivity.
        split; [reflexivity | rewrite HrA; discriminate].
      + left. split; [exact HEt | rewrite HEp; reflexivity].
    - constructor; [apply writable_share_top | constructor].
    - constructor; [| constructor]. cbn. rewrite HrA, Int.unsigned_one. lia. }
  destruct (cre_res x25519 aead_dec DA TA [(pair_ap v_p, Tsh, PA2)] M1) as [[a P']|] eqn:EC;
    cbn [peer_result peers_after].
  - (* accepted: found is A's peer, not NULL *)
    unfold cre_res, prot_specs4.cre_res in EC. pose proof (hrr_cre_single x25519 aead_dec _ _ _ _ _ _ _ _ EC); subst a.
    cbn [supd]. rewrite if_true by reflexivity. unfold peers_rep5, peer_item_rep5. cbn [iter_sepcon]. rewrite sepcon_emp.
    freeze [0;1;2;4;5;6;7;8;9;10;11;12;13;14;15] FR6.
    forward_if (PROP () LOCAL (lvar R._before (Tstruct R._wg_peer noattr) v_before;
            lvar R._message (Tstruct R._message_handshake_response noattr) v_message;
            lvar R._initiation (Tstruct R._message_handshake_initiation noattr) v_initiation;
            lvar R._p (Tstruct R._pair noattr) v_p; gvars gv) SEP (FRZL FR6; peer_rep5 Tsh (pair_ap v_p) P')).
    { match goal with H: pair_ap v_p = _ |- _ => rewrite H in Hap; contradiction end. }
    { forward. entailer!. }
    (* return: the locals are given back *)
    thaw FR6.
    sep_apply (hs_close_snap Tsh v_before PA2 EA (succ_in (t_L TA) (hs_addr (pair_ap v_p)))
                 (vin (hs_addr (pair_ap v_p)) (t_L TA))).
    rewrite hrr_conv_peer.
    sep_apply (hs_close_resp Tsh v_message M1). rewrite hrr_conv_resp.
    sep_apply (hrr_close_init_opt Tsh v_initiation (opt_after ok None (snd (fst CI)))). rewrite hrr_conv_init.
    change (d_itab DA) with (pair_ai v_p).
    sep_apply (hs_pair_close Tsh v_p DA DB TA TB (pair_ap v_p) (pair_bp v_p) P' PB2 EA EB Hfp HDA HDB).
    rewrite hrr_conv_pair.
    unfold abbreviate in POSTCONDITION. subst POSTCONDITION. unfold hs_post.
    replace (fun _ : environ => @TT mpred _) with (PROP () LOCAL () SEP (TT))%assert
      by (extensionality rho; unfold PROPx, LOCALx, SEPx; simpl; normalize).
    abbreviate_semax.
    forward.
    change (Tstruct R._pair noattr) with t_pair. change (Tstruct R._wg_peer noattr) with t_peer.
    change (Tstruct R._message_handshake_response noattr) with t_resp.
    change (Tstruct R._message_handshake_initiation noattr) with t_init.
    cancel.
  - (* rejected: A's peer is as copy_peer saw it *)
    unfold peers_rep5, peer_item_rep5. cbn [iter_sepcon]. rewrite sepcon_emp.
    rewrite (hs_itable1 Tsh (d_itab DA) TA _ _ _ HDA). Intros. rewrite Hnext.
    unfold device_rep5 at 1. Intros.
    match goal with Hs: hs_sid (p_hs PA2) = _ |- _ => rename Hs into HsA end.
    replace (identity_rep Tsh (id_addr (pair_a v_p)) (d_id DA))
      with (identity_rep Tsh (hs_sid (p_hs PA2)) (d_id DA)) by (rewrite HsA; reflexivity).
    freeze [0;1;3;4;5;6;9;10;12;13;14;15;16;17;18;19;20] FR6.
    forward_if (PROP () LOCAL (lvar R._before (Tstruct R._wg_peer noattr) v_before;
            lvar R._message (Tstruct R._message_handshake_response noattr) v_message;
            lvar R._initiation (Tstruct R._message_handshake_initiation noattr) v_initiation;
            lvar R._p (Tstruct R._pair noattr) v_p; gvars gv)
      SEP (FRZL FR6; identity_rep Tsh (hs_sid (p_hs PA2)) (d_id DA);
           entry_at Tsh (hs_addr (pair_ap v_p)) EA nullval (vin (hs_addr (pair_ap v_p)) (t_L TA));
           peer_rep5 Tsh (pair_ap v_p) PA2;
           snap_rep Tsh v_before PA2 EA nullval (vin (hs_addr (pair_ap v_p)) (t_L TA)))).
    { (* the check: same_peer(&p.a_peer, &before) != 0 *)
      forward_call (Tsh, pair_ap v_p, PA2, Tsh, EA, vin (hs_addr (pair_ap v_p)) (t_L TA), Tsh, v_before,
                    Tsh, d_id DA).
      { entailer!. destruct Eaddr as (_&_&_&_&_&_&Eap&_). rewrite Eap. simpl. reflexivity. }
      Intros r14.
      forward_call (Int.one).
      { entailer!. destruct (Int.eq r14 (Int.repr 0)) eqn:E14; [| reflexivity]. apply Int.same_if_eq in E14. subst r14. match goal with Hr: _ <> _ |- _ => elim Hr; reflexivity end. }
      entailer!. }
    { forward. entailer!. }
    (* return: the locals are given back *)
    thaw FR6.
    sep_apply (hs_close_snap Tsh v_before PA2 EA nullval (vin (hs_addr (pair_ap v_p)) (t_L TA))).
    rewrite hrr_conv_peer.
    sep_apply (hs_close_resp Tsh v_message M1). rewrite hrr_conv_resp.
    sep_apply (hrr_close_init_opt Tsh v_initiation (opt_after ok None (snd (fst CI)))). rewrite hrr_conv_init.
    rewrite HsA. change (hs_sid (p_hs PA0)) with (id_addr (pair_a v_p)).
    sep_apply (hrr_itable_fold' Tsh (d_itab DA) TA _ _ _ _ HDA HwA Hnext).
    match goal with Hfa: @field_compatible Noise.CS t_dev [] (pair_a v_p) |- _ =>
      sep_apply (hrr_dev_fold Tsh (pair_a v_p) DA Hfa) end.
    change (d_itab DA) with (pair_ai v_p).
    sep_apply (hs_pair_close Tsh v_p DA DB TA TB (pair_ap v_p) (pair_bp v_p) PA2 PB2 EA EB Hfp HDA HDB).
    rewrite hrr_conv_pair.
    unfold abbreviate in POSTCONDITION. subst POSTCONDITION. unfold hs_post.
    replace (fun _ : environ => @TT mpred _) with (PROP () LOCAL () SEP (TT))%assert
      by (extensionality rho; unfold PROPx, LOCALx, SEPx; simpl; normalize).
    abbreviate_semax.
    forward.
    change (Tstruct R._pair noattr) with t_pair. change (Tstruct R._wg_peer noattr) with t_peer.
    change (Tstruct R._message_handshake_response noattr) with t_resp.
    change (Tstruct R._message_handshake_initiation noattr) with t_init.
    cancel.
Qed.

End Main.
