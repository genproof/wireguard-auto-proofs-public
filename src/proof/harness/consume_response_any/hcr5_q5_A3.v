(* law consume_response_any, phase Q5, segment A3: CHECK(state); CHECK(remote_ephemeral); CHECK(hash && chaining_key); CHECK(remote_index).
   States and statements: hcr5_q5_defs.v; pure facts: hcr5_q5_pure.v (its statement is a hypothesis here,
   proved separately); (section Q5);
   src/proof/harness/consume_response_any/hcr3_q5_A3*.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
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
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_cut.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_model.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_spec.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_defs.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_conv.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_q5_defs.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_q5_pure.
Require WgNoise.harness.x_consume_response_any.code.

#[local] Existing Instance W_consume_response_any.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* Helpers                                                                 *)
(* ---------------------------------------------------------------------- *)

#[local] Instance hcr5_q5_A3_cce_N : change_composite_env Noise.CS W_consume_response_any.
Proof. make_cs_preserve Noise.CS W_consume_response_any. Defined.
#[local] Instance hcr5_q5_A3_cce_H : change_composite_env HCS W_consume_response_any.
Proof. make_cs_preserve HCS W_consume_response_any. Defined.

Lemma hcr5_q5_A3_cs_eq {cs1 cs2} {CCE: change_composite_env cs1 cs2} (sh: share) (t: type) (v1: @reptype cs1 t)
  (v2: @reptype cs2 t) (p: val) :
  JMeq v1 v2 -> cs_preserve_type cs1 cs2 (coeq _ _) t = true ->
  @data_at cs1 sh t v1 p = @data_at cs2 sh t v2 p.
Proof. intros. exact (f_equal (fun f => f p) (@data_at_change_composite cs1 cs2 CCE sh t v1 v2 H H0)). Qed.

Lemma hcr5_q5_A3_hb_W sh bs p :
  hbytes sh bs p = @data_at W_consume_response_any sh (tarray tuchar (Zlength bs)) (bytes bs) p.
Proof. unfold hbytes. apply (@hcr5_q5_A3_cs_eq HCS W_consume_response_any _); [apply JMeq_refl | prove_cs_preserve_type]. Qed.

Lemma hcr5_q5_A3_bytes_eqb_refl A : bytes_eqb A A = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec A A); congruence. Qed.

(* byte fields of the handshake as hbytes, scalar fields at the world's compspecs *)
Ltac hcr5_q5_A3_hsf_tac :=
  intros Hl; match goal with |- @field_at _ ?sh ?t ?gfs ?v ?h = _ =>
    rewrite (@field_at_change_composite Noise.CS W_consume_response_any _ sh t gfs v v (JMeq_refl v)) by reflexivity end;
  rewrite field_at_data_at; rewrite hcr5_q5_A3_hb_W, Hl; reflexivity.

Lemma hcr5_q5_A3_hs_reph sh H h : Zlength (hs_reph H) = 32 ->
  @field_at Noise.CS sh t_hs (DOT prot_repr3.I._remote_ephemeral) (bytes (hs_reph H)) h =
  hbytes sh (hs_reph H) (@field_address W_consume_response_any t_hs (DOT HR5._remote_ephemeral) h).
Proof. hcr5_q5_A3_hsf_tac. Qed.
Lemma hcr5_q5_A3_hs_hash sh H h : Zlength (hs_hash H) = 32 ->
  @field_at Noise.CS sh t_hs (DOT prot_repr3.I._hash) (bytes (hs_hash H)) h =
  hbytes sh (hs_hash H) (@field_address W_consume_response_any t_hs (DOT HR5._hash) h).
Proof. hcr5_q5_A3_hsf_tac. Qed.
Lemma hcr5_q5_A3_hs_ck sh H h : Zlength (hs_ck H) = 32 ->
  @field_at Noise.CS sh t_hs (DOT prot_repr3.I._chaining_key) (bytes (hs_ck H)) h =
  hbytes sh (hs_ck H) (@field_address W_consume_response_any t_hs (DOT HR5._chaining_key) h).
Proof. hcr5_q5_A3_hsf_tac. Qed.

Lemma hcr5_q5_A3_hs_state sh x h :
  @field_at Noise.CS sh t_hs (DOT prot_repr3.I._state) (Vint x) h =
  @field_at W_consume_response_any sh t_hs (DOT HR5._state) (Vint x) h.
Proof.
  match goal with |- @field_at _ ?sh ?t ?gfs ?v ?h = _ =>
    rewrite (@field_at_change_composite Noise.CS W_consume_response_any _ sh t gfs v v (JMeq_refl v)) by reflexivity end.
  reflexivity.
Qed.
Lemma hcr5_q5_A3_hs_rindex sh x h :
  @field_at Noise.CS sh t_hs (DOT prot_repr3.I._remote_index) (Vint x) h =
  @field_at W_consume_response_any sh t_hs (DOT HR5._remote_index) (Vint x) h.
Proof.
  match goal with |- @field_at _ ?sh ?t ?gfs ?v ?h = _ =>
    rewrite (@field_at_change_composite Noise.CS W_consume_response_any _ sh t gfs v v (JMeq_refl v)) by reflexivity end.
  reflexivity.
Qed.

(* field_compatible of a field from that of another field of the same struct *)
Ltac hcr5_q5_A3_fc_tac :=
  match goal with |- field_compatible ?t (DOT ?f) ?p =>
    match goal with Hf: field_compatible t (DOT _) p |- _ =>
      apply field_compatible_cons in Hf; destruct Hf as [_ Hf];
      apply field_compatible_cons; split; [unfold in_members; simpl; tauto | exact Hf] end end.

(* the peer at a in the list after an update *)
Lemma hcr5_q5_A3_peers PS a sh P Q : sfind PS a = Some (sh, P) ->
  peers_rep (supd PS a Q) = (peer_rep sh a Q * peers_rep (sdel PS a))%logic.
Proof.
  induction PS as [| [[x sh0] w] PS IH]; simpl; intros Hf; [discriminate |].
  unfold peers_rep in *. destruct (EqDec_val x a) as [Ex | Hne]; [subst x |].
  - inversion Hf; subst. simpl. reflexivity.
  - simpl. rewrite IH by exact Hf. unfold peer_item_rep.
    rewrite <- !sepcon_assoc, (sepcon_comm (peer_rep sh0 x w)). reflexivity.
Qed.

(* a peer, opened at the five handshake fields A3 reads (the rest kept in one predicate) *)
Definition hcr5_q5_A3_rest (p: val) (P: peer) : mpred :=
  let H := p_hs P in let h := hs_addr p in
  (@field_at Noise.CS Ews t_peer [StructField prot_repr3.I._device] (p_device P) p *
   @field_at Noise.CS Ews t_peer [StructField prot_repr3.I._is_dead] (Val.of_bool (p_dead P)) p *
   kps_rep Ews (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
   @field_at Noise.CS Ews t_hs [StructField prot_repr3.I._last_initiation_consumption] (Vlong (hs_lic H)) h *
   @field_at Noise.CS Ews t_hs [StructField prot_repr3.I._static_identity] (hs_sid H) h *
   @field_at Noise.CS Ews t_hs [StructField prot_repr3.I._ephemeral_private] (bytes (hs_eph H)) h *
   @field_at Noise.CS Ews t_hs [StructField prot_repr3.I._remote_static] (bytes (hs_rstatic H)) h *
   @field_at Noise.CS Ews t_hs [StructField prot_repr3.I._precomputed_static_static] (bytes (hs_ss H)) h *
   @field_at Noise.CS Ews t_hs [StructField prot_repr3.I._preshared_key] (bytes (hs_psk H)) h *
   @field_at Noise.CS Ews t_hs [StructField prot_repr3.I._latest_timestamp] (bytes (hs_ts H)) h *
   (EX lk: val, @field_at Noise.CS Ews t_hs [StructField prot_repr3.I._lock] lk h) *
   spacer Ews 36 40 h * spacer Ews 300 304 h *
   @field_at Noise.CS Ews t_peer [StructField prot_repr3.I._last_sent_handshake] (Vlong (p_lsh P)) p *
   cookie_rep Ews (cookie_addr p) (p_cookie P) *
   @field_at Noise.CS Ews t_peer [StructField prot_repr3.I._refcount] (Vint (p_refs P)) p *
   @field_at Noise.CS Ews t_peer [StructField prot_repr3.I._internal_id] (Vlong (p_id P)) p *
   @field_at Noise.CS Ews t_peer [StructField prot_repr3.I._pubkey_next] (p_pknext P) p *
   spacer Ews 9 16 p * spacer Ews 476 480 p)%logic.

Definition hcr5_q5_A3_five (p: val) (P: peer) : mpred :=
  let H := p_hs P in let h := hs_addr p in
  (@field_at W_consume_response_any Ews t_hs (DOT HR5._state) (Vint (hs_state H)) h *
   hbytes Ews (hs_reph H) (@field_address W_consume_response_any t_hs (DOT HR5._remote_ephemeral) h) *
   hbytes Ews (hs_hash H) (@field_address W_consume_response_any t_hs (DOT HR5._hash) h) *
   hbytes Ews (hs_ck H) (@field_address W_consume_response_any t_hs (DOT HR5._chaining_key) h) *
   @field_at W_consume_response_any Ews t_hs (DOT HR5._remote_index) (Vint (hs_rindex H)) h)%logic.

Lemma hcr5_q5_A3_open p P :
  peer_rep Ews p P =
  (!! (@field_compatible Noise.CS t_peer [] p /\ hs_ok (p_hs P)) &&
   (hcr5_q5_A3_five p P * hcr5_q5_A3_rest p P))%logic.
Proof.
  apply pred_ext.
  - unfold peer_rep, hs_rep. Intros.
    assert (Hok := H0). destruct H0 as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
    rewrite (hcr5_q5_A3_hs_reph Ews (p_hs P) (hs_addr p) L3), (hcr5_q5_A3_hs_hash Ews (p_hs P) (hs_addr p) L6),
      (hcr5_q5_A3_hs_ck Ews (p_hs P) (hs_addr p) L7), hcr5_q5_A3_hs_state, hcr5_q5_A3_hs_rindex.
    unfold hcr5_q5_A3_five, hcr5_q5_A3_rest. Intros lk.
    apply andp_right; [apply prop_right; auto | Exists lk; cancel].
  - Intros. destruct H0 as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
    unfold peer_rep, hs_rep, hcr5_q5_A3_five, hcr5_q5_A3_rest.
    rewrite (hcr5_q5_A3_hs_reph Ews (p_hs P) (hs_addr p) L3), (hcr5_q5_A3_hs_hash Ews (p_hs P) (hs_addr p) L6),
      (hcr5_q5_A3_hs_ck Ews (p_hs P) (hs_addr p) L7), hcr5_q5_A3_hs_state, hcr5_q5_A3_hs_rindex.
    Intros lk. Exists lk. entailer!. unfold hs_ok; auto 10.
Qed.

(* the message, opened at the two fields A3 reads *)
Definition hcr5_q5_A3_mrest (sh: share) (m: val) (M: resp_msg) : mpred :=
  (@field_at W_consume_response_any sh t_resp [StructField HR5._header] (Vint (rm_type M)) m *
   @field_at W_consume_response_any sh t_resp [StructField HR5._receiver_index] (Vint (rm_receiver M)) m *
   hbytes sh (rm_encn M) (@field_address W_consume_response_any t_resp [StructField HR5._encrypted_nothing] m) *
   @field_at W_consume_response_any sh t_resp [StructField HR5._macs] (bytes (rm_mac1 M), bytes (rm_mac2 M)) m)%logic.

Lemma hcr5_q5_A3_resp_open sh M m : rm_ok M ->
  resp_rep sh m M =
  (hbytes sh (rm_eph M) (@field_address W_consume_response_any t_resp [StructField HR5._unencrypted_ephemeral] m) *
   @field_at W_consume_response_any sh t_resp [StructField HR5._sender_index] (Vint (rm_sender M)) m *
   hcr5_q5_A3_mrest sh m M)%logic.
Proof.
  intros Hok. assert (Hok' := Hok). destruct Hok' as (H1 & H2 & _).
  unfold resp_rep, hcr5_q5_A3_mrest. rewrite prop_true_andp by exact Hok.
  rewrite (@hcr5_q5_A3_cs_eq Noise.CS W_consume_response_any _ sh t_resp (resp_val M) (resp_val M) m)
    by (apply JMeq_refl || prove_cs_preserve_type).
  rewrite !hcr5_q5_A3_hb_W, H1, H2. unfold resp_val. unfold_data_at (data_at _ _ _ m).
  rewrite (field_at_data_at sh t_resp [StructField HR5._unencrypted_ephemeral]).
  rewrite (field_at_data_at sh t_resp [StructField HR5._encrypted_nothing]). apply pred_ext; cancel.
Qed.

(* the model's state st, opened at its two fields *)
Lemma hcr5_q5_A3_mstate sh ck h p : Zlength ck = 32 -> Zlength h = 32 ->
  @data_at HCS sh t_mstate (mstate_val ck h) p =
  (hbytes sh ck (@field_address W_consume_response_any t_mstate [StructField HR5._ck] p) *
   hbytes sh h (@field_address W_consume_response_any t_mstate [StructField HR5._h] p))%logic.
Proof.
  intros H1 H2. rewrite !hcr5_q5_A3_hb_W, H1, H2.
  rewrite (@hcr5_q5_A3_cs_eq HCS W_consume_response_any _ sh t_mstate (mstate_val ck h) (mstate_val ck h) p)
    by (apply JMeq_refl || prove_cs_preserve_type).
  unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at sh t_mstate [StructField HR5._ck]), (field_at_data_at sh t_mstate [StructField HR5._h]).
  reflexivity.
Qed.

(* folding back: the accepted peer (its five fields at their known values), the message, st, the list *)
Lemma hcr5_q5_A3_fold a P M ck h :
  @field_compatible Noise.CS t_peer [] a -> hs_ok (p_hs (hcr5_q5_put P M ck h)) ->
  (@field_at W_consume_response_any Ews t_hs (DOT HR5._state) (Vint (Int.repr 4)) (hs_addr a) *
   hbytes Ews (rm_eph M) (@field_address W_consume_response_any t_hs (DOT HR5._remote_ephemeral) (hs_addr a)) *
   hbytes Ews h (@field_address W_consume_response_any t_hs (DOT HR5._hash) (hs_addr a)) *
   hbytes Ews ck (@field_address W_consume_response_any t_hs (DOT HR5._chaining_key) (hs_addr a)) *
   @field_at W_consume_response_any Ews t_hs (DOT HR5._remote_index) (Vint (rm_sender M)) (hs_addr a) *
   hcr5_q5_A3_rest a (hcr5_q5_put P M ck h)
   |-- peer_rep Ews a (hcr5_q5_put P M ck h))%logic.
Proof.
  intros H1 H2. rewrite (hcr5_q5_A3_open a (hcr5_q5_put P M ck h)).
  apply andp_right; [apply prop_right; auto |]. unfold hcr5_q5_A3_five. apply derives_refl.
Qed.

Lemma hcr5_q5_A3_resp_fold sh M m : rm_ok M ->
  (hbytes sh (rm_eph M) (@field_address W_consume_response_any t_resp [StructField HR5._unencrypted_ephemeral] m) *
   @field_at W_consume_response_any sh t_resp [StructField HR5._sender_index] (Vint (rm_sender M)) m *
   hcr5_q5_A3_mrest sh m M |-- resp_rep sh m M)%logic.
Proof. intros Hok. rewrite (hcr5_q5_A3_resp_open sh M m Hok). apply derives_refl. Qed.

Lemma hcr5_q5_A3_mstate_fold sh ck h p : Zlength ck = 32 -> Zlength h = 32 ->
  (hbytes sh ck (@field_address W_consume_response_any t_mstate [StructField HR5._ck] p) *
   hbytes sh h (@field_address W_consume_response_any t_mstate [StructField HR5._h] p)
   |-- @data_at HCS sh t_mstate (mstate_val ck h) p)%logic.
Proof. intros H1 H2. rewrite (hcr5_q5_A3_mstate sh ck h p H1 H2). apply derives_refl. Qed.

Lemma hcr5_q5_A3_peers_fold PS a sh P Q : sfind PS a = Some (sh, P) ->
  (peer_rep sh a Q * peers_rep (sdel PS a) |-- peers_rep (supd PS a Q))%logic.
Proof. intros Hf. rewrite (hcr5_q5_A3_peers PS a sh P Q Hf). apply derives_refl. Qed.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hcr5_q5_A3_ok {Espec: OracleKind} gv L FR :
  hcr5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec -> hcr5_q5_pure_stmt x25519 aead_dec ->
  semax (hcr5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hcr5_q5_QA1 x25519 aead_dec gv L FR) hcr5_q5_A3 (overridePost (hcr5_q5_QA1 x25519 aead_dec gv L FR) (hcr5_R gv)).
Proof.
  intros HH HP. unfold hcr5_q5_QA1, hcr5_Delta, hcr5_R, hcr5_q5_A3. simplify_func_tycontext.
  Intros R S NS PS head nb T. Intros KE m M a P ck h.
  unfold hcr5_lvars, hcr5_q5_scr, hcr5_world, hcr5_globs, hcr5_snaps; cbn [app].
  abbreviate_semax.
  assert_PROP (itable_wf T) as Hwf by (unfold itable; entailer!).
  destruct HP as (_ & _ & _ & HP4 & _).
  destruct (HP4 R L NS PS head nb KE T M a P ck h H0 H1 Hwf H4)
    as (NS1 & N & NS2 & PS1 & PS2 & E & _ & Hsf & _).
  rewrite (hcr5_q5_A3_peers PS a Ews P (hcr5_q5_put P M ck h) Hsf), hcr5_q5_A3_open. Intros.
  match goal with Hx: hs_ok _ |- _ => rename Hx into Hok end.
  match goal with Hx: @field_compatible Noise.CS t_peer [] a |- _ => rename Hx into Hfc end.
  rewrite (hcr5_q5_A3_resp_open Ews M m H3).
  assert (Hok' := Hok). unfold hcr5_q5_put, hcr5_new, p_set_refs, p_set_hs in Hok'. cbn [p_hs] in Hok'.
  destruct Hok' as (_ & _ & Lre & _ & _ & Lh & Lck & _). cbn [hs_reph hs_hash hs_ck] in Lre, Lh, Lck.
  rewrite (hcr5_q5_A3_mstate Tsh ck h (l_st L) Lck Lh).
  unfold hcr5_q5_A3_five. repeat flatten_sepcon_in_SEP.
  replace (hs_state (p_hs (hcr5_q5_put P M ck h))) with (Int.repr 4) by reflexivity.
  replace (hs_reph (p_hs (hcr5_q5_put P M ck h))) with (rm_eph M) by reflexivity.
  replace (hs_hash (p_hs (hcr5_q5_put P M ck h))) with h by reflexivity.
  replace (hs_ck (p_hs (hcr5_q5_put P M ck h))) with ck by reflexivity.
  replace (hs_rindex (p_hs (hcr5_q5_put P M ck h))) with (rm_sender M) by reflexivity.
  assert_PROP (isptr (field_address t_mstate (DOT HR5._h) (l_st L)) /\
               isptr (field_address t_mstate (DOT HR5._ck) (l_st L))) as Hst by (unfold hbytes; entailer!).
  destruct Hst as [Hsth Hstck]. rewrite isptr_field_address_lemma in Hsth, Hstck.
  freeze FR1 := - (@field_at W_consume_response_any Ews t_hs (DOT HR5._state) _ _)
    (hbytes Ews _ (@field_address W_consume_response_any t_hs (DOT HR5._remote_ephemeral) _))
    (hbytes Ews _ (@field_address W_consume_response_any t_hs (DOT HR5._hash) _))
    (hbytes Ews _ (@field_address W_consume_response_any t_hs (DOT HR5._chaining_key) _))
    (@field_at W_consume_response_any Ews t_hs (DOT HR5._remote_index) _ _)
    (hbytes Ews _ (@field_address W_consume_response_any t_resp _ _))
    (@field_at W_consume_response_any Ews t_resp (DOT HR5._sender_index) _ _)
    (hbytes Tsh _ (@field_address W_consume_response_any t_mstate (DOT HR5._ck) _))
    (hbytes Tsh _ (@field_address W_consume_response_any t_mstate (DOT HR5._h) _)).
  (* CHECK(h->state == HANDSHAKE_CONSUMED_RESPONSE) *)
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  { apply ENTAIL_refl. }
  { forward. forward_if.
    { exfalso. match goal with Hc: _ = Int.zero |- _ => rewrite Int.eq_true in Hc; exact (Int.one_not_zero Hc) end. }
    forward. entailer!. }
  { forward. apply ENTAIL_refl. }
  (* CHECK(bytes_eq(h->remote_ephemeral, msg->unencrypted_ephemeral, 32)) *)
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  { apply ENTAIL_refl. }
  { forward_call (Ews, field_address t_hs (DOT HR5._remote_ephemeral) (hs_addr a), rm_eph M,
                  Ews, field_address t_resp (DOT HR5._unencrypted_ephemeral) m, rm_eph M).
    { entailer!. rewrite Lre. unfold field_address. rewrite !if_true. reflexivity.
      all: hcr5_q5_A3_fc_tac. }
    rewrite hcr5_q5_A3_bytes_eqb_refl.
    forward_if.
    { exfalso; match goal with Hc: _ = Int.zero |- _ => exact (Int.one_not_zero Hc) end. }
    forward. entailer!. }
  { forward. apply ENTAIL_refl. }
  (* CHECK(bytes_eq(h->hash, st.h, 32) && bytes_eq(h->chaining_key, st.ck, 32)) *)
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  { apply ENTAIL_refl. }
  { forward_call (Ews, field_address t_hs (DOT HR5._hash) (hs_addr a), h,
                  Tsh, field_address t_mstate (DOT HR5._h) (l_st L), h).
    { entailer!. rewrite Lh. unfold field_address. rewrite !if_true by (auto; hcr5_q5_A3_fc_tac). reflexivity. }
    rewrite hcr5_q5_A3_bytes_eqb_refl.
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
          forward_if (PROPx P (LOCALx (temp HR5._t'36 (Vint Int.one) :: Q) (SEPx R))) end.
    { forward_call (Ews, field_address t_hs (DOT HR5._chaining_key) (hs_addr a), ck,
                    Tsh, field_address t_mstate (DOT HR5._ck) (l_st L), ck).
      { entailer!. rewrite Lck. unfold field_address. rewrite !if_true by (auto; hcr5_q5_A3_fc_tac). reflexivity. }
      rewrite hcr5_q5_A3_bytes_eqb_refl.
      forward. entailer!. }
    { exfalso; match goal with Hc: Int.one = Int.zero |- _ => exact (Int.one_not_zero Hc) end. }
    forward_if.
    { exfalso; match goal with Hc: _ = Int.zero |- _ => exact (Int.one_not_zero Hc) end. }
    forward. entailer!. }
  { forward. apply ENTAIL_refl. }
  (* CHECK(h->remote_index == msg->sender_index) *)
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  { apply ENTAIL_refl. }
  { forward. forward. forward_if.
    { exfalso. match goal with Hc: _ = Int.zero |- _ => rewrite Int.eq_true in Hc; exact (Int.one_not_zero Hc) end. }
    forward. entailer!. }
  { forward. apply ENTAIL_refl. }
  thaw FR1.
  sep_apply (hcr5_q5_A3_fold a P M ck h Hfc Hok).
  sep_apply (hcr5_q5_A3_resp_fold Ews M m H3).
  sep_apply (hcr5_q5_A3_mstate_fold Tsh ck h (l_st L) Lck Lh).
  sep_apply (hcr5_q5_A3_peers_fold PS a Ews P (hcr5_q5_put P M ck h) Hsf).
  unfold POSTCONDITION, abbreviate. simpl_ret_assert.
  Exists R S NS PS head nb T. Exists KE m M a P ck h. entailer!.
Qed.

End Seg.
