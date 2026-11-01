(* The law hs_matching_keys: the body of main (harness/hs_matching_keys.c). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import QuickProof.Env.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.common.wg3_iface3.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol5.prot_repr5.
Require Import WgNoise.proof.protocol5.prot_specs5.
Require Import WgNoise.proof.harness.hs_common.hs_specs.
Require Import WgNoise.proof.harness.hs_common.hs_worlds.
Require Import WgNoise.proof.harness.hs_common.hs_close.
Require Import WgNoise.proof.harness.hs_matching_keys.hmk_model.
Require Import WgNoise.proof.harness.hs_matching_keys.hmk_kp.
Require Import WgNoise.proof.harness.hs_common.hs_globals.
Require Import WgNoise.proof.harness.hs_common.hs_asm.
Require Import WgNoise.proof.harness.hs_matching_keys.hmk_spec.
Require WgNoise.proof.harness.handshake.hhs3_p6_model.
Require WgNoise.contracts.hs_matching_keys.
Require WgNoise.harness.hs_matching_keys.code.
Local Open Scope logic.

#[local] Existing Instance W_hs_matching_keys.

#[local] Instance hmk_cce_N : change_composite_env Noise.CS W.
Proof. make_cs_preserve Noise.CS W. Defined.
#[local] Instance hmk_cce_H : change_composite_env CSh W.
Proof. make_cs_preserve CSh W. Defined.

(* main's stack frame, from main's compspecs to those of the specifications *)
Lemma hmk_conv_pair sh p : @data_at_ W sh (Tstruct C._pair noattr) p = @data_at_ CSh sh t_pair p.
Proof. rewrite (@data_at__change_composite CSh W _ sh t_pair); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hmk_conv_init sh p : @data_at_ W sh (Tstruct C._message_handshake_initiation noattr) p = @data_at_ Noise.CS sh t_init p.
Proof. rewrite (@data_at__change_composite Noise.CS W _ sh t_init); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hmk_conv_resp sh p : @data_at_ W sh (Tstruct C._message_handshake_response noattr) p = @data_at_ Noise.CS sh t_resp p.
Proof. rewrite (@data_at__change_composite Noise.CS W _ sh t_resp); [reflexivity | prove_cs_preserve_type]. Qed.

(* the table of new_pair holds the peer's handshake entry *)
Lemma hmk_table_in_pool sh pa : hs_in_pool (hs_table sh pa) pa.
Proof. unfold hs_in_pool, hs_table, t_entry. simpl. if_tac; [| contradiction]. eexists; split; reflexivity. Qed.

(* the arguments &p.a_peer.handshake etc. are the addresses of the specifications *)
Ltac hmk_addr :=
  entailer!; unfold hs_addr, kps_addr, pair_ap, pair_bp, pair_a, pair_b, field_address;
  rewrite ?if_true by auto with field_compatible; try reflexivity.

(* the message buffers back to uninitialised memory (main's frame at a return) *)
Lemma hmk_init_close sh m Mo : init_opt_rep sh m Mo |-- @data_at_ W sh (Tstruct C._message_handshake_initiation noattr) m.
Proof.
  rewrite hmk_conv_init. destruct Mo; simpl; [apply hs_close_init | apply derives_refl].
Qed.
Lemma hmk_resp_close sh m Mo : resp_opt_rep sh m Mo |-- @data_at_ W sh (Tstruct C._message_handshake_response noattr) m.
Proof.
  rewrite hmk_conv_resp. destruct Mo; simpl; [apply hs_close_resp | apply derives_refl].
Qed.

Lemma hmk_init_close5 sh m M : init_rep5 sh m M |-- @data_at_ W sh (Tstruct C._message_handshake_initiation noattr) m.
Proof. rewrite hmk_conv_init. apply hs_close_init. Qed.
Lemma hmk_resp_close5 sh m M : resp_rep5 sh m M |-- @data_at_ W sh (Tstruct C._message_handshake_response noattr) m.
Proof. rewrite hmk_conv_resp. apply hs_close_resp. Qed.

(* the pool entry at a, out of a pool (the others are dropped) *)
Lemma hmk_pool_take L a sh E :
  sfind L a = Some (sh, E) -> iter_sepcon hs_pool_entry L |-- (EX n: val, EX h: bool, entry_at sh a E n h) * TT.
Proof.
  induction L as [| [[a' sh'] E'] L IH]; simpl; intros HF; [discriminate |].
  destruct (EqDec_val a' a) as [<- | Hne].
  - inversion HF; subst. cancel.
  - specialize (IH HF). sep_apply IH. cancel.
Qed.

(* struct pair back to uninitialised memory: the two devices, their tables (whose pools hold the peers'
   handshake entries, with the peers' share; the other entries live in keypairs and are dropped) and the two
   peers *)
Lemma hmk_pair_close p DA DB TA TB ha hb PA PB :
  @field_compatible CSh t_pair [] p ->
  (exists EA, sfind (t_D TA) (hs_addr (pair_ap p)) = Some (Tsh, EA)) ->
  (exists EB, sfind (t_D TB) (hs_addr (pair_bp p)) = Some (Tsh, EB)) ->
  device_rep5 Tsh (pair_a p) DA * device_rep5 Tsh (pair_b p) DB *
  itable Tsh (pair_ai p) TA * itable Tsh (pair_bi p) TB *
  ptable Tsh (pair_ak p) ha * ptable Tsh (pair_bk p) hb *
  peer_rep5 Tsh (pair_ap p) PA * peer_rep5 Tsh (pair_bp p) PB
  |-- @data_at_ W Tsh (Tstruct C._pair noattr) p * TT.
Proof.
  intros Hfc [EA HA] [EB HB].
  sep_apply (hs_close_itable Tsh (pair_ai p) TA). sep_apply (hs_close_itable Tsh (pair_bi p) TB).
  sep_apply (hmk_pool_take _ _ _ _ HA). sep_apply (hmk_pool_take _ _ _ _ HB). Intros n1 h1 n2 h2.
  sep_apply (hs_close_peer Tsh (pair_ap p) PA EA). sep_apply (hs_close_peer Tsh (pair_bp p) PB EB).
  sep_apply (hs_close_dev Tsh (pair_a p) DA). sep_apply (hs_close_dev Tsh (pair_b p) DB).
  unfold ptable. rewrite hmk_conv_pair.
  sep_apply (hs_pair_join Tsh p Hfc). cancel.
Qed.

(* a pool keeps the peer's handshake entry *)
Ltac hmk_sfind :=
  repeat match goal with |- context [if ?c then _ else _] => destruct c end;
  eexists; unfold t_insert, t_set_index, t_upd, t_entry, t_add, hs_table; simpl;
  repeat first [rewrite if_true by reflexivity | rewrite if_false by (first [intro; discriminate | congruence])
               | progress simpl];
  try reflexivity.

(* main's frame at a return *)
Ltac hmk_close :=
  repeat first [sep_apply hmk_init_close5 | sep_apply hmk_resp_close5 | sep_apply hmk_init_close
               | sep_apply hmk_resp_close];
  unfold pair_devA, pair_devB, hs_dev; cbn [d_itab d_ptab];
  sep_apply hmk_pair_close; [hmk_sfind | hmk_sfind | cancel].

(* the peers' addresses are pointers *)
Lemma hmk_pair_ptr p : @field_compatible CSh t_pair [] p -> isptr (pair_ap p) /\ isptr (pair_bp p).
Proof.
  intros Hfc. unfold pair_ap, pair_bp, field_address. rewrite !if_true by auto with field_compatible.
  pose proof (field_compatible_isptr _ _ _ Hfc) as Hp. destruct p; try contradiction; split; exact I.
Qed.

(* new_pair's table after create_initiation's insert: its one entry, hashed *)
Lemma hmk_TA1 sh pa idx :
  t_insert (hs_table sh pa) (hs_addr pa) idx = mkT [(hs_addr pa, sh, mkEntry pa IDX_HANDSHAKE idx)] [hs_addr pa].
Proof. unfold t_insert, t_set_index, t_upd, t_entry, hs_table. simpl. rewrite !if_true by reflexivity. reflexivity. Qed.

(* begin_session's precondition on a peer with empty slots and its one hashed handshake entry *)
Ltac hmk_bs_pre EP Hc Hp Hn :=
  split; [subst; reflexivity |];
  try (split; [assumption |]);
  split; [unfold hs_in_pool, t_entry; simpl; rewrite if_true by reflexivity; eexists; split; reflexivity |];
  split; [split; simpl; constructor |];
  unfold slots_ok; simpl p_cur; simpl p_prev; simpl p_next; rewrite Hc, Hp, Hn; split;
    [repeat constructor; left; reflexivity | simpl; constructor].

(* begin_session's model (the x_handshake law's lemmas, on the same model function begin_session_model):
   with a failed allocation, and with a fresh keypair k on an alive peer with empty slots *)
Lemma hmk_bs_null P p kc KS T S :
  orb (Int.eq (hs_state (p_hs P)) HS_CREATED_RESPONSE) (Int.eq (hs_state (p_hs P)) HS_CONSUMED_RESPONSE) = true ->
  bs_res P p nullval kc KS T S = (false, P, mkKW KS T (shim_alloc_fail S), kc).
Proof. exact (WgNoise.proof.harness.handshake.hhs3_p6_model.hhs3_p6_model_bs_null P p kc KS T S). Qed.

Lemma hmk_bs_ok P p k kc S sh E :
  orb (Int.eq (hs_state (p_hs P)) HS_CREATED_RESPONSE) (Int.eq (hs_state (p_hs P)) HS_CONSUMED_RESPONSE) = true ->
  p_dead P = false -> p_cur P = nullval -> p_prev P = nullval -> p_next P = nullval ->
  k <> nullval -> k <> hs_addr p ->
  bs_res P p k kc [] (mkT [(hs_addr p, sh, E)] [hs_addr p]) S =
  (true,
   p_set_slots (p_set_hs P (hs_zero (p_hs P)))
     (if Int.eq (hs_state (p_hs P)) HS_CONSUMED_RESPONSE then k else nullval) nullval
     (if Int.eq (hs_state (p_hs P)) HS_CONSUMED_RESPONSE then nullval else k),
   mkKW [(k, kp_new (p_hs P) (Int64.add kc Int64.one) (s_boot S))]
        (mkT [(k, Ews, mkEntry (e_peer E) IDX_KEYPAIR (e_index E)); (hs_addr p, sh, E)] [k]) (shim_alloc_ok S),
   Int64.add kc Int64.one).
Proof. exact (WgNoise.proof.harness.handshake.hhs3_p6_model.hhs3_p6_model_bs_ok P p k kc S sh E). Qed.

Lemma hmk_kps_nil cs : keypairs_rep cs [] = emp.
Proof. reflexivity. Qed.

Lemma hmk_peers1 sh a P : peers_rep5 [(a, sh, P)] = peer_rep5 sh a P.
Proof. unfold peers_rep5. simpl. rewrite sepcon_emp. reflexivity. Qed.

(* a peer's address is a valid pointer (main compares the peers returned by the consume functions with NULL) *)
Lemma hmk_peer_vp p P : peer_rep5 Tsh p P |-- valid_pointer p.
Proof.
  unfold peer_rep5. apply andp_left2. repeat apply sepcon_valid_pointer1.
  apply field_at_valid_ptr0; auto; reflexivity.
Qed.
#[local] Hint Resolve hmk_peer_vp hmk_itable_vp : valid_pointer.

(* the numeric facts of a new peer *)
Ltac hmk_num :=
  unfold pair_peerA, pair_peerB, hs_peer0, hs_initial, prot_specs4.hs_initial, p_set_hs; simpl;
  try rewrite Int64.signed_zero; try rewrite Int.unsigned_one; rep_lia.

Section Main.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).

(* the consume functions on a one-peer list accept that peer *)
Lemma hmk_cin_addr D a sh P M S a' P' :
  cin_res x25519 aead_dec D [(a, sh, P)] M S = Some (a', P') ->
  a' = a /\ exists r H, P' = p_set_hs (p_set_refs P r) H.
Proof.
  intros E. unfold cin_res, prot_specs4.cin_res, consume_initiation_model in E. simpl pk_find in E.
  repeat match goal with
         | Hh: context [match ?e with _ => _ end] |- _ => destruct e eqn:?; try discriminate
         end.
  all: repeat match goal with Hh: Some _ = Some _ |- _ => inversion Hh; clear Hh; subst end.
  all: unfold peer_get in *; destruct (Int.eq (p_refs _) Int.zero); try discriminate;
       repeat match goal with Hh: Some _ = Some _ |- _ => inversion Hh; clear Hh; subst end;
       split; [reflexivity | do 2 eexists; reflexivity].
Qed.

Lemma hmk_cre_addr D T a sh P M a' P' :
  cre_res x25519 aead_dec D T [(a, sh, P)] M = Some (a', P') ->
  a' = a /\ exists r H, P' = p_set_hs (p_set_refs P r) H.
Proof.
  intros E. unfold cre_res, prot_specs4.cre_res, consume_response_model in E. simpl sfind in E.
  repeat match goal with
         | Hh: context [match ?e with _ => _ end] |- _ => destruct e eqn:?; try discriminate
         end.
  all: repeat match goal with Hh: Some _ = Some _ |- _ => inversion Hh; clear Hh; subst end.
  all: unfold peer_get in *; destruct (Int.eq (p_refs _) Int.zero); try discriminate;
       repeat match goal with Hh: Some _ = Some _ |- _ => inversion Hh; clear Hh; subst end;
       split; [auto | do 2 eexists; reflexivity].
Qed.

(* main's postcondition in the canonical form VST's tactics need (it implies hs_post) *)
Definition hmk_post : (ident -> val) -> environ -> mpred := fun _ => EX r: int, PROP () RETURN (Vint r) SEP (TT).

(* main's body, from its initial globals (hs_globals.v) *)
Lemma hmk_main_body0 :
  x25519_props x25519 -> x25519_clamp_inv x25519 -> x25519_dh_agree x25519 ->
  @semax_body (QPvarspecs hmk_prog) (hmk_Gmain x25519 aead_enc aead_dec) W HMK.f_main
    (QP.prog_main hmk_prog, QPmain_spec_ext' hmk_prog tt hmk_post).
Proof.
  intros Hx Hcl Hdh.
  unfold QPmain_spec_ext', NDmk_funspec.
  split3; [reflexivity | reflexivity | ]. intros Espec DTL gv.
  eapply (main_pre_InitGpred (hs_globals0 gv));
    [apply hs_init_globals_matching_keys | reflexivity
    | apply Forall_forall; intros x Hx'; vm_compute in Hx'; repeat destruct Hx' as [Hx'|Hx']; try contradiction;
      subst x; vm_compute; exact I | ].
  process_stackframe_of.
  unfold hs_globals0. sep_apply (create_mem_mgr gv). Intros.
  unfold hmk_post. simpl fn_body. simpl fn_return. abbreviate_semax.
  forget hs_shim0 as S. forget hs_w0 as w. forget Int64.zero as kc.
  rewrite hmk_conv_pair, hmk_conv_init, hmk_conv_resp.
  forward_call (gv, Tsh, v_p, zeros32, zeros32, kc).
  Intros vret. destruct vret as [[araw braw] psk]. simpl fst in *; simpl snd in *.
  rename H into Ha, H0 into Hb, H1 into Hpsk.
  forward_call (gv, S, w).
  Intros vret. destruct vret as [[b rs] rn]. simpl fst in *; simpl snd in *.
  rename H into Hbt, H0 into Hrn.
  unfold hs_pair. Intros. rename H into Hfc.
  (* A: create_initiation *)
  forward_call (gv, shim_clocks S b rs rn, w, kc, Tsh, v_initiation, @None init_msg, Tsh, pair_ap v_p,
                pair_peerA x25519 v_p araw braw psk, Tsh, pair_a v_p, pair_devA x25519 v_p araw, Tsh,
                hs_table Tsh (pair_ap v_p)).
  { hmk_addr. }
  { apply hmk_table_in_pool. }
  Intros vret. destruct vret as [r1 idx1]. simpl fst in *; simpl snd in *.
  change (init_of None) with init_msg0 in *.
  destruct (ci_res x25519 aead_enc (pair_devA x25519 v_p araw) (pair_peerA x25519 v_p araw braw psk)
              init_msg0 (shim_clocks S b rs rn) r1 idx1) as [[ok1 M1] HA1] eqn:Eci.
  simpl fst in *; simpl snd in *.
  forward_if.
  { forward. Exists Int.zero. entailer!.
    hmk_close. }
  destruct ok1; [| discriminate].
  (* B: consume_initiation *)
  simpl opt_after. unfold init_opt_rep.
  match goal with |- context [shim_state4 gv ?X w] => set (S1 := X) end.
  rewrite <- (hmk_peers1 Tsh (pair_bp v_p)).
  forward_call (gv, S1, w, kc, Tsh, v_initiation, M1, Tsh, pair_b v_p, pair_devB x25519 v_p braw, Tsh, pair_bp v_p,
                [(pair_bp v_p, Tsh, pair_peerB x25519 v_p araw braw psk)]).
  { hmk_addr. }
  { unfold peers_wf, peers_refs_ok. simpl. repeat split; repeat (apply Forall_cons || apply Forall_nil);
      first [apply writable_share_top | hmk_num]. }
  destruct (cin_res x25519 aead_dec (pair_devB x25519 v_p braw)
              [(pair_bp v_p, Tsh, pair_peerB x25519 v_p araw braw psk)] M1 S1) as [[b' PB1] |] eqn:Ecin.
  2: { forward_if.
       { forward. Exists Int.zero. entailer!. simpl peers_after. rewrite hmk_peers1.
         hmk_close. }
       simpl in *. contradiction. }
  destruct (hmk_cin_addr _ _ _ _ _ _ _ _ Ecin) as [-> (rB & HB0 & EPB1)].
  simpl peer_result; simpl peers_after. rewrite if_true by reflexivity. rewrite hmk_peers1.
  forward_if.
  { exfalso. destruct (hmk_pair_ptr _ Hfc) as [_ Hp]. rewrite H2 in Hp. exact Hp. }
  (* B: create_response *)
  forward_call (gv, S1, w, Tsh, v_response, @None resp_msg, Tsh, pair_bp v_p, PB1, Tsh, pair_b v_p,
                pair_devB x25519 v_p braw, Tsh, hs_table Tsh (pair_bp v_p)).
  { hmk_addr. }
  { split; [subst PB1; reflexivity | apply hmk_table_in_pool]. }
  Intros vret. destruct vret as [r2 idx2]. simpl fst in *; simpl snd in *. rename H2 into Hr2, H3 into Hfr2.
  change (resp_of None) with resp_msg0 in *.
  destruct (cr_res x25519 aead_enc PB1 resp_msg0 r2 idx2) as [[ok2 M2] HB2] eqn:Ecr.
  simpl fst in *; simpl snd in *.
  forward_if.
  { forward. Exists Int.zero. entailer!. hmk_close. }
  destruct ok2; [| discriminate].
  simpl opt_after. unfold resp_opt_rep.
  match goal with |- context [shim_state4 gv ?X w] => set (S2 := X) end.
  (* A: consume_response *)
  rewrite <- (hmk_peers1 Tsh (pair_ap v_p)).
  forward_call (gv, S2, w, Tsh, v_response, M2, Tsh, pair_a v_p, pair_devA x25519 v_p araw, Tsh,
                t_insert (hs_table Tsh (pair_ap v_p)) (hs_addr (pair_ap v_p)) idx1,
                [(pair_ap v_p, Tsh, p_set_hs (pair_peerA x25519 v_p araw braw psk) HA1)]).
  { hmk_addr. }
  { unfold pool_peers_ok, peers_wf, peers_refs_ok, t_insert, t_set_index, t_upd, t_entry, hs_table. simpl.
    rewrite !if_true by reflexivity. simpl.
    repeat split; repeat (apply Forall_cons || apply Forall_nil); first [apply writable_share_top | hmk_num | idtac].
    split; [| left; split; reflexivity].
    do 2 eexists. rewrite if_true by reflexivity. split; [reflexivity | apply Int.one_not_zero]. }
  destruct (cre_res x25519 aead_dec (pair_devA x25519 v_p araw)
              (t_insert (hs_table Tsh (pair_ap v_p)) (hs_addr (pair_ap v_p)) idx1)
              [(pair_ap v_p, Tsh, p_set_hs (pair_peerA x25519 v_p araw braw psk) HA1)] M2) as [[a' PA2] |] eqn:Ecre.
  2: { forward_if.
       { forward. Exists Int.zero. entailer!. simpl peers_after. rewrite hmk_peers1. hmk_close. }
       simpl in *. contradiction. }
  destruct (hmk_cre_addr _ _ _ _ _ _ _ _ Ecre) as [-> (rA & HA2 & EPA2)].
  simpl peer_result; simpl peers_after. rewrite if_true by reflexivity. rewrite hmk_peers1.
  forward_if.
  { exfalso. destruct (hmk_pair_ptr _ Hfc) as [Hp _]. rewrite H3 in Hp. exact Hp. }
  destruct (hmk_model x25519 aead_enc aead_dec Hx Hcl Hdh v_p Tsh araw braw psk _ r1 idx1 M1 HA1 S1 _ PB1 r2 idx2
              M2 HB2 _ _ PA2 Ha Hb Hpsk H Hfr2 Eci Ecin Ecr Ecre)
    as (_ & _ & HstA & HstB & Hck & HdA & HcA & HpA & HnA & HdB & HcB & HpB & HnB).
  (* A: begin_session *)
  rewrite hmk_TA1.
  assert_PROP (@field_compatible Noise.CS t_peer [] (pair_ap v_p)) as FCa by (unfold peer_rep5; entailer!).
  assert_PROP (@field_compatible Noise.CS t_peer [] (pair_bp v_p)) as FCb by (unfold peer_rep5; entailer!).
  forward_call (gv, S2, w, kc, @nil (val * keypair),
                mkT [(hs_addr (pair_ap v_p), Tsh, mkEntry (pair_ap v_p) IDX_HANDSHAKE idx1)] [hs_addr (pair_ap v_p)],
                Tsh, pair_ap v_p, PA2, Tsh, pair_a v_p, pair_devA x25519 v_p araw, Tsh).
  { hmk_addr. }
  { unfold keypairs_rep. simpl iter_sepcon. rewrite emp_sepcon. cancel. }
  { hmk_bs_pre EPA2 HcA HpA HnA. }
  Intros kA.
  match goal with Hh: kA <> nullval -> _ |- _ => rename Hh into HkA end.
  destruct (eq_dec kA nullval) as [-> | HkAn].
  { rewrite hmk_bs_null by (rewrite HstA; reflexivity). cbn [fst snd kw_KS kw_T kw_S].
    forward_if.
    { forward. Exists Int.zero. entailer!. try rewrite hmk_kps_nil. hmk_close. }
    simpl in *. contradiction. }
  assert (HkAh: kA <> hs_addr (pair_ap v_p)) by (intro X; apply (proj1 (HkA HkAn)); simpl; left; auto).
  rewrite hmk_bs_ok by (first [rewrite HstA; reflexivity | assumption]).
  rewrite HstA, Int.eq_true. cbn [fst snd kw_KS kw_T kw_S].
  forward_if.
  { exfalso. apply Int.one_not_zero. assumption. }
  set (KA := kp_new (p_hs PA2) (Int64.add kc Int64.one) (s_boot S2)).
  (* B: begin_session *)
  rewrite hmk_TA1.
  forward_call (gv, shim_alloc_ok S2, prot_model4.begin_session_warn PA2 (hs_addr (pair_ap v_p)) kA kc
                  (mkKW [] (mkT [(hs_addr (pair_ap v_p), Tsh, mkEntry (pair_ap v_p) IDX_HANDSHAKE idx1)]
                               [hs_addr (pair_ap v_p)]) S2) w,
                Int64.add kc Int64.one, @nil (val * keypair),
                mkT [(hs_addr (pair_bp v_p), Tsh, mkEntry (pair_bp v_p) IDX_HANDSHAKE idx2)] [hs_addr (pair_bp v_p)],
                Tsh, pair_bp v_p, p_set_hs PB1 HB2, Tsh, pair_b v_p, pair_devB x25519 v_p braw, Tsh).
  { hmk_addr. }
  { rewrite hmk_kps_nil, emp_sepcon. cancel. }
  { hmk_bs_pre EPB1 HcB HpB HnB. }
  Intros kB.
  match goal with Hh: kB <> nullval -> _ |- _ => rename Hh into HkB end.
  change (p_hs (p_set_hs PB1 HB2)) with HB2.
  destruct (eq_dec kB nullval) as [-> | HkBn].
  { rewrite hmk_bs_null by (simpl; rewrite HstB; reflexivity). cbn [fst snd kw_KS kw_T kw_S].
    forward_if.
    { forward. Exists Int.zero. entailer!. try rewrite hmk_kps_nil. hmk_close. }
    simpl in *. contradiction. }
  assert (HkBh: kB <> hs_addr (pair_bp v_p)) by (intro X; apply (proj1 (HkB HkBn)); simpl; left; auto).
  rewrite hmk_bs_ok by (first [simpl; rewrite HstB; reflexivity | assumption | simpl; assumption]).
  change (p_hs (p_set_hs PB1 HB2)) with HB2.
  rewrite HstB. change (Int.eq HS_CREATED_RESPONSE HS_CONSUMED_RESPONSE) with false. cbn [fst snd kw_KS kw_T kw_S].
  forward_if.
  { exfalso. apply Int.one_not_zero. assumption. }
  set (KB := kp_new HB2 (Int64.add (Int64.add kc Int64.one) Int64.one) (s_boot (shim_alloc_ok S2))).
  (* the checks *)
  clear Eci Ecin Ecr Ecre H0 H4 HkA HkB EPA2 EPB1 HdA HcA HpA HnA HdB HcB HpB HnB.
  repeat match goal with Hh: typed_false _ _ |- _ => clear Hh end.
  repeat match goal with Hh: s_failnext _ = true -> _ |- _ => clear Hh end.
  set (PA3 := p_set_slots (p_set_hs PA2 (hs_zero (p_hs PA2))) kA nullval nullval).
  set (PB3 := p_set_slots (p_set_hs (p_set_hs PB1 HB2) (hs_zero HB2)) nullval nullval kB).
  rewrite (hmk_peer_split Tsh (pair_ap v_p) PA3), (hmk_peer_split Tsh (pair_bp v_p) PB3).
  change (p_cur PA3) with kA; change (p_prev PA3) with nullval; change (p_next PA3) with nullval.
  change (p_cur PB3) with nullval; change (p_prev PB3) with nullval; change (p_next PB3) with kB.
  rewrite (hmk_kps_a Tsh v_p _ _ _ Hfc), (hmk_kps_b Tsh v_p _ _ _ Hfc). Intros lkA lkB.
  rewrite (hmk_kp_open kA KA), (hmk_kp_open kB KB). Intros.
  match goal with Hh: field_compatible t_kp [] kA |- _ => rename Hh into FKA end.
  match goal with Hh: field_compatible t_kp [] kB |- _ => rename Hh into FKB end.
  match goal with Hh: kp_ok KA |- _ => destruct Hh as (LA1 & LA2 & _) end.
  match goal with Hh: kp_ok KB |- _ => destruct Hh as (LB1 & LB2 & _) end.
  (* the model: the keys cross over, A is the initiator, B is not *)
  assert (EK1: sk_key (kp_send KA) = sk_key (kp_recv KB)).
  { unfold KA, KB, kp_new. cbn [kp_send kp_recv sk_key]. rewrite HstA, HstB, Int.eq_true, Hck. reflexivity. }
  assert (EK2: sk_key (kp_recv KA) = sk_key (kp_send KB)).
  { unfold KA, KB, kp_new. cbn [kp_send kp_recv sk_key]. rewrite HstA, HstB, Int.eq_true, Hck. reflexivity. }
  assert (IA: kp_init KA = true) by (unfold KA, kp_new; cbn [kp_init]; rewrite HstA; apply Int.eq_true).
  assert (IB: kp_init KB = false) by (unfold KB, kp_new; cbn [kp_init]; rewrite HstB; reflexivity).
  rewrite IA, IB.
  forward. forward.
  freeze FR1 := (mem_mgr gv) (shim_state4 _ _ _) (noise_globals _ _) (wg_consts5 _) (hmk_kprest _ _)
    (hmk_kprest _ _) (hmk_prest _ _ _) (hmk_prest _ _ _).
  freeze FR2 := (field_at _ (Tstruct C._pair noattr) _ _ _) (field_at _ (Tstruct C._pair noattr) _ _ _)
    (device_rep5 _ _ _) (device_rep5 _ _ _) (resp_rep5 _ _ _) (init_rep5 _ _ _) (ptable _ _ _) (ptable _ _ _)
    (has_ext _).
  forward_if (temp C._t'7 (Vint Int.one)).
  { forward. entailer!. pose proof (field_compatible_isptr _ _ _ FKB). destruct kB; try contradiction; reflexivity. }
  { contradiction. }
  forward_call (Int.one).
  (* bytes_eq(a->sending.key, b->receiving.key, 32) *)
  forward_call (Ews, offset_val 32 kA, sk_key (kp_send KA), Ews, offset_val 88 kB, sk_key (kp_recv KB)).
  { eapply derives_trans; [apply TT_right | apply prop_right].
    pose proof (field_compatible_isptr _ _ _ FKA). pose proof (field_compatible_isptr _ _ _ FKB).
    destruct kA; try contradiction; destruct kB; try contradiction. rewrite LA1. simpl.
    rewrite !Ptrofs.add_zero. reflexivity. }
  rewrite EK1, hmk_bytes_eqb_refl.
  forward_call (Int.one).
  (* bytes_eq(a->receiving.key, b->sending.key, 32) *)
  forward_call (Ews, offset_val 88 kA, sk_key (kp_recv KA), Ews, offset_val 32 kB, sk_key (kp_send KB)).
  { eapply derives_trans; [apply TT_right | apply prop_right].
    pose proof (field_compatible_isptr _ _ _ FKA). pose proof (field_compatible_isptr _ _ _ FKB).
    destruct kA; try contradiction; destruct kB; try contradiction. rewrite LA2. simpl.
    rewrite !Ptrofs.add_zero. reflexivity. }
  rewrite EK2, hmk_bytes_eqb_refl.
  forward_call (Int.one).
  (* a->i_am_the_initiator && !b->i_am_the_initiator *)
  forward.
  forward_if (temp C._t'10 (Vint Int.one)).
  { forward. forward. entailer!. }
  { exfalso. simpl in *. discriminate. }
  forward_call (Int.one).
  thaw FR2. thaw FR1.
  sep_apply (hmk_kps_a_fold Tsh v_p kA nullval nullval lkB Hfc).
  sep_apply (hmk_kps_b_fold Tsh v_p nullval nullval kB lkA Hfc).
  sep_apply (hmk_peer_fold Tsh (pair_ap v_p) PA3 kA nullval nullval eq_refl eq_refl eq_refl).
  sep_apply (hmk_peer_fold Tsh (pair_bp v_p) PB3 nullval nullval kB eq_refl eq_refl eq_refl).
  sep_apply (hmk_init_close5 Tsh v_initiation M1). sep_apply (hmk_resp_close5 Tsh v_response M2).
  unfold pair_devA, pair_devB, hs_dev; cbn [d_itab d_ptab].
  sep_apply (hmk_pair_close v_p); [hmk_sfind | hmk_sfind |].
  forward. Exists Int.zero. entailer!.
Qed.

Lemma hmk_main_body :
  x25519_props x25519 -> x25519_clamp_inv x25519 -> x25519_dh_agree x25519 ->
  @semax_body (QPvarspecs hmk_prog) (hmk_Gmain x25519 aead_enc aead_dec) W HMK.f_main (hs_main_spec hmk_prog).
Proof.
  intros Hx Hcl Hdh.
  eapply semax_body_funspec_sub; [apply hmk_main_body0; assumption | | ].
  - unfold QPmain_spec_ext'. do_funspec_sub. Exists w emp. rewrite emp_sepcon.
    apply andp_right; [apply derives_refl | apply prop_right; intros; unfold hs_post; apply TT_right].
  - repeat constructor; simpl; intuition discriminate.
Qed.

End Main.
