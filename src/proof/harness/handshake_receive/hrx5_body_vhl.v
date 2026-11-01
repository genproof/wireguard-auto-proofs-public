(* law handshake_receive: body proofs of local
   functions of the harness unit (hrx5_spec.v), at the unit's compspecs HRX.  receive.c's validate_header_len and the harness's dispatch.
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.libc.libc_bytes.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_model.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_spec.
Local Open Scope logic.

#[local] Existing Instance HRX.

(* ---- helpers ---- *)
#[local] Instance hrx5_vhl_CCE_c2h : change_composite_env Cookie.CS HRX.
Proof. make_cs_preserve Cookie.CS HRX. Defined.
#[local] Instance hrx5_vhl_CCE_h2c : change_composite_env HRX Cookie.CS.
Proof. make_cs_preserve HRX Cookie.CS. Defined.

Lemma hrx5_vhl_skb_cs sh s p :
  @data_at Cookie.CS sh t_skb (skb_val s) p = @data_at HRX sh t_skb (skb_val s) p.
Proof.
  apply (f_equal (fun f => f p)). apply (@data_at_change_composite Cookie.CS HRX _); [apply JMeq_refl | reflexivity].
Qed.

Lemma hrx5_vhl_le32_inv l : Zlength l = 4 -> le32 (le32_val l) = l.
Proof.
  intros Hl. assert (Hn: length l = 4%nat) by (rewrite Zlength_correct in Hl; lia).
  destruct l as [|a [|b [|c [|d [|e l]]]]]; simpl in Hn; try discriminate.
  rewrite prot_rep3_le32_encode. unfold le32_val.
  pose proof (Byte.unsigned_range a). pose proof (Byte.unsigned_range b).
  pose proof (Byte.unsigned_range c). pose proof (Byte.unsigned_range d).
  change Byte.modulus with 256 in *.
  replace (Byte.unsigned (Znth 0 [a;b;c;d]) + Byte.unsigned (Znth 1 [a;b;c;d]) * 2 ^ 8 +
           Byte.unsigned (Znth 2 [a;b;c;d]) * 2 ^ 16 + Byte.unsigned (Znth 3 [a;b;c;d]) * 2 ^ 24)
    with (int_of_bytes [a;b;c;d]) by (cbn [int_of_bytes]; cbv [Znth]; simpl; lia).
  rewrite Int.unsigned_repr by (cbn [int_of_bytes]; rep_lia).
  unfold encode_int, rev_if_be. change Archi.big_endian with false. cbv iota.
  exact (prot_rep3_bytes_of_int_of_bytes [a;b;c;d]).
Qed.

Lemma hrx5_vhl_hdr_u32 sh v p : @field_compatible HRX (Tstruct HRC._message_header noattr) [] p ->
  @data_at HRX sh (Tstruct HRC._message_header noattr) v p = @data_at HRX sh tuint v p.
Proof.
  intros FC. unfold_data_at (data_at _ _ _ p).
  rewrite field_at_data_at, field_compatible_field_address by auto with field_compatible.
  replace (nested_field_offset _ _) with 0 by reflexivity.
  rewrite isptr_offset_val_zero by (destruct FC; auto). reflexivity.
Qed.

Lemma hrx5_vhl_mc_hdr n p : 4 <= n -> malloc_compatible n p ->
  @field_compatible HRX (Tstruct HRC._message_header noattr) [] p.
Proof.
  intros Hn Hm. apply malloc_compatible_field_compatible; [| reflexivity | reflexivity].
  destruct p; try contradiction. destruct Hm as [Ha Hs]. split; auto.
  replace (sizeof _) with 4 by reflexivity. lia.
Qed.

Lemma hrx5_vhl_split sh msg p : 4 <= Zlength msg -> malloc_compatible (Zlength msg) p ->
  bytes_at sh msg p =
  @data_at HRX sh (Tstruct HRC._message_header noattr) (Vint (hrx5_tw msg)) p *
  bytes_at sh (sublist 4 (Zlength msg) msg) (offset_val 4 p).
Proof.
  intros Hn Hm.
  assert (FCh := hrx5_vhl_mc_hdr _ _ Hn Hm).
  assert (FCu: @field_compatible HRX tuint [] p).
  { apply malloc_compatible_field_compatible; [| reflexivity | reflexivity].
    destruct p; try contradiction. destruct Hm as [Ha Hs]. split; auto. simpl. lia. }
  assert (FCa: @field_compatible Noise.CS (tarray tuchar (Zlength msg)) [] p).
  { destruct p; try contradiction. destruct Hm as [Ha Hs].
    repeat split; auto.
    - simpl. rewrite Z.max_r by lia. lia.
    - apply align_compatible_rec_Tarray. intros.
      eapply align_compatible_rec_by_value; [reflexivity | apply Z.divide_1_l]. }
  rewrite <- (sublist_same 0 (Zlength msg) msg) at 1 by auto.
  rewrite (sublist_split 0 4 (Zlength msg)) by lia.
  rewrite prot_rep3_bytes_app
    by (rewrite !Zlength_sublist by lia; replace (4 - 0 + (Zlength msg - 4)) with (Zlength msg) by lia; exact FCa).
  rewrite Zlength_sublist by lia. replace (4 - 0) with 4 by lia.
  f_equal.
  rewrite hrx5_vhl_hdr_u32 by auto. unfold hrx5_tw.
  rewrite (prot_rep3_u32_le sh _ p FCu). rewrite hrx5_vhl_le32_inv by list_solve.
  unfold bytes_at. rewrite Zlength_sublist by lia. replace (4 - 0) with 4 by lia.
  apply data_at_tarray_tuchar_cs.
Qed.

Ltac vhl_contra := match goal with H: _ |- _ => solve [exfalso; first [apply H; reflexivity | exact (Int.one_not_zero H) | exact (Int.one_not_zero (eq_sym H))]] end.
Ltac vhl_contra2 := first [vhl_contra | exfalso; match goal with H: typed_true _ _ |- _ => revert H | H: typed_false _ _ |- _ => revert H end; vm_compute; discriminate].
Ltac vhl_ret m := unfold skb_rep; rewrite hrx5_vhl_skb_cs; rewrite (hrx5_vhl_split _ m) by (auto; lia); entailer!.

Lemma hrx5_body_vhl x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs) :
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  @semax_body hrx5_V (hrx5_Gl x25519 aead_enc aead_dec xaead_enc xaead_dec CSw HRX) HRX HRC.f_validate_header_len
    hrx5_vhl_spec.
Proof.
  intros _ _ _.
  start_function.
  unfold skb_rep. Intros. rewrite hrx5_vhl_skb_cs.
  destruct H as [Hlen Hmc].
  assert (Hp: isptr (sk_data s)) by (destruct (sk_data s); try contradiction; exact I).
  forward.
  forward_if.
  { forward. unfold skb_rep. rewrite hrx5_vhl_skb_cs. entailer!. unfold vhl_model. rewrite Hlen.
    rewrite (proj2 (Z.ltb_lt _ _) H). reflexivity. }
  assert (Hl: sk_len s = Int.repr (Zlength msg)) by (rewrite Hlen, Int.repr_unsigned; reflexivity).
  assert (Hr: Zlength msg <= Int.max_unsigned) by (rewrite Hlen; rep_lia).
  rewrite (hrx5_vhl_split shm msg) by (auto; lia).
  Intros.
  unfold skb_val. forward. forward. forward.
  forward_if (PROP () LOCAL (temp HRC._t'1 (Val.of_bool (Int.eq (hrx5_tw msg) (Int.repr 4) && (32 <=? Zlength msg))%bool); temp HRC._skb sp)
    SEP (@data_at HRX shs t_skb (skb_val s) sp; @data_at HRX shm (Tstruct HRC._message_header noattr) (Vint (hrx5_tw msg)) (sk_data s);
         bytes_at shm (sublist 4 (Zlength msg) msg) (offset_val 4 (sk_data s)))).
  { forward. forward. entailer!.
    rewrite H1, Int.eq_true, Hl. unfold Int.ltu. rewrite !Int.unsigned_repr by rep_lia.
    destruct (zlt (Zlength msg) 32); [rewrite (proj2 (Z.leb_gt _ _)) by lia | rewrite (proj2 (Z.leb_le _ _)) by lia];
      reflexivity. }
  { forward. entailer!. rewrite Int.eq_false by auto. reflexivity. }
  destruct (Int.eq (hrx5_tw msg) (Int.repr 4) && (32 <=? Zlength msg))%bool eqn:E4.
  { forward_if; [| vhl_contra]. forward. vhl_ret msg. unfold vhl_model. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite E4. reflexivity. }
  forward_if; [vhl_contra |]. rename E4 into F4.
  unfold skb_val. forward. forward. forward.
  forward_if (PROP () LOCAL (temp HRC._t'2 (Val.of_bool (Int.eq (hrx5_tw msg) Int.one && (Zlength msg =? 148))%bool); temp HRC._skb sp)
    SEP (@data_at HRX shs t_skb (skb_val s) sp; @data_at HRX shm (Tstruct HRC._message_header noattr) (Vint (hrx5_tw msg)) (sk_data s);
         bytes_at shm (sublist 4 (Zlength msg) msg) (offset_val 4 (sk_data s)))).
  { forward. forward. entailer!.
    match goal with H: hrx5_tw msg = _ |- _ => rewrite H end. rewrite Int.eq_true, <- Hlen.
    replace (sizeof _) with 148 by reflexivity. unfold Int64.cmpu, Int64.eq. rewrite !Int64.unsigned_repr by rep_lia.
    destruct (zeq (Zlength msg) 148); [rewrite (proj2 (Z.eqb_eq _ _)) by lia | rewrite (proj2 (Z.eqb_neq _ _)) by lia];
      reflexivity. }
  { forward. entailer!. rewrite Int.eq_false by auto. reflexivity. }
  destruct (Int.eq (hrx5_tw msg) Int.one && (Zlength msg =? 148))%bool eqn:E1.
  { forward_if; [| vhl_contra]. forward. vhl_ret msg. unfold vhl_model. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite F4, E1. reflexivity. }
  forward_if; [vhl_contra |]. rename E1 into F1.
  unfold skb_val. forward. forward. forward.
  forward_if (PROP () LOCAL (temp HRC._t'3 (Val.of_bool (Int.eq (hrx5_tw msg) (Int.repr 2) && (Zlength msg =? 92))%bool); temp HRC._skb sp)
    SEP (@data_at HRX shs t_skb (skb_val s) sp; @data_at HRX shm (Tstruct HRC._message_header noattr) (Vint (hrx5_tw msg)) (sk_data s);
         bytes_at shm (sublist 4 (Zlength msg) msg) (offset_val 4 (sk_data s)))).
  { forward. forward. entailer!.
    match goal with H: hrx5_tw msg = _ |- _ => rewrite H end. rewrite Int.eq_true, <- Hlen.
    replace (sizeof _) with 92 by reflexivity. unfold Int64.cmpu, Int64.eq. rewrite !Int64.unsigned_repr by rep_lia.
    destruct (zeq (Zlength msg) 92); [rewrite (proj2 (Z.eqb_eq _ _)) by lia | rewrite (proj2 (Z.eqb_neq _ _)) by lia];
      reflexivity. }
  { forward. entailer!. rewrite Int.eq_false by auto. reflexivity. }
  destruct (Int.eq (hrx5_tw msg) (Int.repr 2) && (Zlength msg =? 92))%bool eqn:E2.
  { forward_if; [| vhl_contra]. forward. vhl_ret msg. unfold vhl_model. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite F4, F1, E2. reflexivity. }
  forward_if; [vhl_contra |]. rename E2 into F2.
  unfold skb_val. forward. forward. forward.
  forward_if (PROP () LOCAL (temp HRC._t'4 (Val.of_bool (Int.eq (hrx5_tw msg) (Int.repr 3) && (Zlength msg =? 64))%bool); temp HRC._skb sp)
    SEP (@data_at HRX shs t_skb (skb_val s) sp; @data_at HRX shm (Tstruct HRC._message_header noattr) (Vint (hrx5_tw msg)) (sk_data s);
         bytes_at shm (sublist 4 (Zlength msg) msg) (offset_val 4 (sk_data s)))).
  { forward. forward. entailer!.
    match goal with H: hrx5_tw msg = _ |- _ => rewrite H end. rewrite Int.eq_true, <- Hlen.
    replace (sizeof _) with 64 by reflexivity. unfold Int64.cmpu, Int64.eq. rewrite !Int64.unsigned_repr by rep_lia.
    destruct (zeq (Zlength msg) 64); [rewrite (proj2 (Z.eqb_eq _ _)) by lia | rewrite (proj2 (Z.eqb_neq _ _)) by lia];
      reflexivity. }
  { forward. entailer!. rewrite Int.eq_false by auto. reflexivity. }
  destruct (Int.eq (hrx5_tw msg) (Int.repr 3) && (Zlength msg =? 64))%bool eqn:E3.
  { forward_if; [| vhl_contra]. forward. vhl_ret msg. unfold vhl_model. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite F4, F1, F2, E3. reflexivity. }
  forward_if; [vhl_contra |]. rename E3 into F3.
  forward. forward. vhl_ret msg. unfold vhl_model. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite F4, F1, F2, F3. reflexivity.
Qed.

Lemma hrx5_vhl_fwd_iff msg : vhl_model msg <> 0 ->
  hrx5_fwd msg = (Int.eq (hrx5_tw msg) Int.one || Int.eq (hrx5_tw msg) (Int.repr 2) || Int.eq (hrx5_tw msg) (Int.repr 3))%bool.
Proof.
  unfold vhl_model, hrx5_fwd. remember (hrx5_tw msg) as tw. clear Heqtw.
  destruct (Zlength msg <? 4) eqn:L; [congruence |].
  replace (4 <=? Zlength msg) with true by (symmetry; apply Z.leb_le; apply Z.ltb_ge in L; lia).
  cbn [andb].
  destruct (Int.eq tw (Int.repr 4)) eqn:E4;
  [apply Int.same_if_eq in E4; subst tw; intros _;
   destruct (Zlength msg =? 148), (Zlength msg =? 92), (Zlength msg =? 64); reflexivity |].
  destruct (Int.eq tw Int.one) eqn:E1, (Int.eq tw (Int.repr 2)) eqn:E2, (Int.eq tw (Int.repr 3)) eqn:E3;
  repeat match goal with H: Int.eq tw ?a = true |- _ => apply Int.same_if_eq in H; subst tw end;
  try discriminate; cbn [andb orb];
  destruct (Zlength msg =? 148), (Zlength msg =? 92), (Zlength msg =? 64); cbn; intros Hz; try congruence.
Qed.

Lemma hrx5_vhl_ge4 msg : vhl_model msg <> 0 -> 4 <= Zlength msg.
Proof. unfold vhl_model. destruct (Zlength msg <? 4) eqn:L; [congruence |]. apply Z.ltb_ge in L. lia. Qed.

Lemma hrx5_vhl_cases msg : vhl_model msg = 0 \/ vhl_model msg = 16 \/ vhl_model msg = 148 \/
  vhl_model msg = 92 \/ vhl_model msg = 64.
Proof. unfold vhl_model. repeat match goal with |- context [if ?b then _ else _] => destruct b end; auto. Qed.

Lemma hrx5_vhl_zero msg : Int64.repr (vhl_model msg) = Int64.zero -> vhl_model msg = 0.
Proof.
  intros H. destruct (hrx5_vhl_cases msg) as [E|[E|[E|[E|E]]]]; rewrite E in *; auto;
  apply (f_equal Int64.unsigned) in H; vm_compute in H; discriminate.
Qed.

Lemma hrx5_vhl_nofwd msg : vhl_model msg = 0 -> hrx5_fwd msg = false.
Proof.
  unfold vhl_model, hrx5_fwd.
  destruct (Zlength msg <? 4) eqn:L.
  - apply Z.ltb_lt in L. replace (4 <=? Zlength msg) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
  - repeat match goal with |- context [if ?b then _ else _] => destruct b end; try discriminate;
    intros _; rewrite ?andb_false_r; reflexivity.
Qed.

Definition hrx5_vhl_d0 : rxdraw := mkRD (zeros 32) (zeros 24) (zeros 32) nullval.
Lemma hrx5_vhl_d0_ok T : rxdraw_ok T hrx5_vhl_d0.
Proof. unfold rxdraw_ok, hrx5_vhl_d0, zeros; cbn [rd_r rd_nonce rd_r2 rd_k]. repeat split; try reflexivity. congruence. Qed.

Lemma hrx5_body_dispatch x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs) :
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  @semax_body hrx5_V (hrx5_Gl x25519 aead_enc aead_dec xaead_enc xaead_dec CSw HRX) HRX HRC.f_dispatch
    (hrx5_dispatch_spec x25519 aead_dec xaead_enc xaead_dec CSw).
Proof.
  intros _ _ _.
  start_function.
  forward_call (shs, sp, s, shm, msg).
  forward_if.
  { apply hrx5_vhl_zero in H1. forward. Exists hrx5_vhl_d0. unfold rx_model. rewrite hrx5_vhl_nofwd by auto.
    entailer!. apply hrx5_vhl_d0_ok. }
  assert (Hn0: vhl_model msg <> 0) by (intros E; rewrite E in H1; apply H1; reflexivity).
  clear H1.
  pose proof (hrx5_vhl_fwd_iff msg Hn0) as Hf.
  pose proof (hrx5_vhl_ge4 msg Hn0) as Hn4.
  destruct H as [Hlen Hmc].
  assert (Hp: isptr (sk_data s)) by (destruct (sk_data s); try contradiction; exact I).
  unfold skb_rep. Intros. rewrite hrx5_vhl_skb_cs.
  rewrite (hrx5_vhl_split shm msg) by auto.
  Intros. unfold skb_val. forward. forward. forward.
  forward_if (PROP () LOCAL (temp HRC._t'2 (Val.of_bool (Int.eq (hrx5_tw msg) Int.one || Int.eq (hrx5_tw msg) (Int.repr 2))%bool);
      gvars gv; temp HRC._wg wg; temp HRC._skb sp)
    SEP (@data_at HRX shs t_skb (skb_val s) sp; @data_at HRX shm (Tstruct HRC._message_header noattr) (Vint (hrx5_tw msg)) (sk_data s);
         bytes_at shm (sublist 4 (Zlength msg) msg) (offset_val 4 (sk_data s));
         rxw_rep CSw gv shd wg head W; qlen_rep gv q; wg_consts gv; mem_mgr gv)).
  { forward. entailer!. rewrite H1. reflexivity. }
  { forward. forward. forward. entailer!. rewrite (Int.eq_false _ Int.one) by exact H1. cbn [orb]. destruct (Int.eq (hrx5_tw msg) (Int.repr 2)); reflexivity. }
  forward_if (PROP () LOCAL (temp HRC._t'3 (Val.of_bool (Int.eq (hrx5_tw msg) Int.one || Int.eq (hrx5_tw msg) (Int.repr 2) || Int.eq (hrx5_tw msg) (Int.repr 3))%bool);
      gvars gv; temp HRC._wg wg; temp HRC._skb sp)
    SEP (skb_rep shs sp s; bytes_at shm msg (sk_data s);
         rxw_rep CSw gv shd wg head W; qlen_rep gv q; wg_consts gv; mem_mgr gv)).
  { destruct (Int.eq (hrx5_tw msg) Int.one || Int.eq (hrx5_tw msg) (Int.repr 2))%bool eqn:E12.
    - forward. vhl_ret msg.
    - vhl_contra2. }
  { destruct (Int.eq (hrx5_tw msg) Int.one || Int.eq (hrx5_tw msg) (Int.repr 2))%bool eqn:E12; [vhl_contra2 |].
    unfold skb_val. forward. forward. forward. vhl_ret msg. cbn [orb].
    destruct (Int.eq (hrx5_tw msg) (Int.repr 3)); reflexivity. }
  destruct (Int.eq (hrx5_tw msg) Int.one || Int.eq (hrx5_tw msg) (Int.repr 2) || Int.eq (hrx5_tw msg) (Int.repr 3))%bool eqn:E.
  - forward_if; [| vhl_contra2].
    forward_call (gv, W, q, shd, wg, head, shs, sp, s, shm, msg).
    { split; auto. }
    Intros d. Exists d. unfold rx_model. rewrite Hf. vhl_ret msg.
  - forward_if; [vhl_contra2 |].
    forward. Exists hrx5_vhl_d0. unfold rx_model. rewrite Hf. vhl_ret msg. all: apply hrx5_vhl_d0_ok.
Qed.

(* the conjunction of this file's body lemmas *)
Definition hrx5_bodies_vhl : Prop :=
  forall x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs),
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  (@semax_body hrx5_V (hrx5_Gl x25519 aead_enc aead_dec xaead_enc xaead_dec CSw HRX) HRX HRC.f_validate_header_len hrx5_vhl_spec) /\
  (@semax_body hrx5_V (hrx5_Gl x25519 aead_enc aead_dec xaead_enc xaead_dec CSw HRX) HRX HRC.f_dispatch (hrx5_dispatch_spec x25519 aead_dec xaead_enc xaead_dec CSw)).

Theorem hrx5_grp_vhl : hrx5_bodies_vhl.
Proof.
  intros x25519 aead_enc aead_dec xaead_enc xaead_dec CSw H1 H2 H3.
  exact (conj (hrx5_body_vhl _ _ _ _ _ _ H1 H2 H3)
    (hrx5_body_dispatch _ _ _ _ _ _ H1 H2 H3)).
Qed.
