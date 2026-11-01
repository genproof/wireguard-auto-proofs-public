(* nb port of the hc4b_ke_add_segC.v., (kents_add): segment C of the loop body, the keypair's fields. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common.hc3_cs.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_cs.
Require Import WgNoise.proof.harness.common4.hc4a_nb_cs.
Require Import WgNoise.proof.harness.common4.hc4_ctx.
Require Import WgNoise.proof.harness.common4.hc4a_nb_ctx.
Require Import WgNoise.proof.harness.common4.hc4nb2_ke_add_defs.
Require WgNoise.harness.x_cookie_mac.code.
Local Open Scope logic.

Section SegC.
#[local] Existing Instance CS4nb.

#[local] Instance hc4nb2_ke_add_segC_cce : change_composite_env Noise.CS CS4nb.
Proof. make_cs_preserve Noise.CS CS4nb. Defined.

(* the uninitialized keypair body at CS4nb *)
Lemma hc4nb2_ke_add_segC_b0 k : hc4nb2_ke_add_body0 k =
  @field_at_ CS4nb Ews t_kp [StructField I._sending] k *
  @field_at_ CS4nb Ews t_kp [StructField I._sending_counter] k *
  @field_at_ CS4nb Ews t_kp [StructField I._receiving] k *
  @field_at_ CS4nb Ews t_kp [StructField I._receiving_counter] k *
  @field_at_ CS4nb Ews t_kp [StructField I._remote_index] k *
  @field_at_ CS4nb Ews t_kp [StructField I._i_am_the_initiator] k *
  @field_at_ CS4nb Ews t_kp [StructField I._refcount] k *
  @field_at_ CS4nb Ews t_kp [StructField I._rcu] k *
  @field_at_ CS4nb Ews t_kp [StructField I._internal_id] k *
  spacer Ews 1181 1184 k.
Proof.
  unfold hc4nb2_ke_add_body0.
  rewrite !(@field_at__change_composite Noise.CS CS4nb _ Ews t_kp) by reflexivity. reflexivity.
Qed.

(* the key of a fresh symmetric key, lent to nondet_bytes *)
Lemma hc4nb2_ke_add_segC_ks k : field_compatible t_kp [] k ->
  field_at_ Ews t_kp (DOT I._sending) k |--
  data_at_ Ews (tarray tuchar 32) (field_address t_kp [StructField I._key; StructField I._sending] k) *
  (ALL v: list val, data_at Ews (tarray tuchar 32) v (field_address t_kp [StructField I._key; StructField I._sending] k) -*
     field_at Ews t_kp (DOT I._sending) (v, (Vundef, Vundef)) k).
Proof.
  intros FC. unfold field_at_.
  eapply derives_trans.
  { apply (gfield_ramif Ews t_kp (DOT I._sending) (StructField I._key) _ (default_val (nested_field_type t_kp [StructField I._key; StructField I._sending])) k); [apply JMeq_refl | auto with field_compatible]. }
  rewrite (field_at_data_at Ews t_kp [StructField I._key; StructField I._sending]).
  apply sepcon_derives; [apply derives_refl|].
  apply allp_right; intros v. apply (allp_left _ v).
  apply wand_derives; [rewrite (field_at_data_at Ews t_kp [StructField I._key; StructField I._sending]); apply derives_refl|].
  apply derives_refl.
Qed.

(* the same for the receiving key *)
Lemma hc4nb2_ke_add_segC_kr k : field_compatible t_kp [] k ->
  field_at_ Ews t_kp (DOT I._receiving) k |--
  data_at_ Ews (tarray tuchar 32) (field_address t_kp [StructField I._key; StructField I._receiving] k) *
  (ALL v: list val, data_at Ews (tarray tuchar 32) v (field_address t_kp [StructField I._key; StructField I._receiving] k) -*
     field_at Ews t_kp (DOT I._receiving) (v, (Vundef, Vundef)) k).
Proof.
  intros FC. unfold field_at_.
  eapply derives_trans.
  { apply (gfield_ramif Ews t_kp (DOT I._receiving) (StructField I._key) _ (default_val (nested_field_type t_kp [StructField I._key; StructField I._receiving])) k); [apply JMeq_refl | auto with field_compatible]. }
  rewrite (field_at_data_at Ews t_kp [StructField I._key; StructField I._receiving]).
  apply sepcon_derives; [apply derives_refl|].
  apply allp_right; intros v. apply (allp_left _ v).
  apply wand_derives; [rewrite (field_at_data_at Ews t_kp [StructField I._key; StructField I._receiving]); apply derives_refl|].
  apply derives_refl.
Qed.

Lemma hc4nb2_ke_add_segC_ks_close k v :
  data_at Ews (tarray tuchar 32) v (field_address t_kp [StructField I._key; StructField I._sending] k) *
  (ALL v: list val, data_at Ews (tarray tuchar 32) v (field_address t_kp [StructField I._key; StructField I._sending] k) -*
     field_at Ews t_kp (DOT I._sending) (v, (Vundef, Vundef)) k) |--
  field_at Ews t_kp (DOT I._sending) (v, (Vundef, Vundef)) k.
Proof.
  eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply (allp_left _ v); apply derives_refl] |].
  apply modus_ponens_wand.
Qed.

Lemma hc4nb2_ke_add_segC_kr_close k v :
  data_at Ews (tarray tuchar 32) v (field_address t_kp [StructField I._key; StructField I._receiving] k) *
  (ALL v: list val, data_at Ews (tarray tuchar 32) v (field_address t_kp [StructField I._key; StructField I._receiving] k) -*
     field_at Ews t_kp (DOT I._receiving) (v, (Vundef, Vundef)) k) |--
  field_at Ews t_kp (DOT I._receiving) (v, (Vundef, Vundef)) k.
Proof.
  eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply (allp_left _ v); apply derives_refl] |].
  apply modus_ponens_wand.
Qed.

Definition hc4nb2_ke_add_segC_lk : val :=
  fst (snd (@default_val CS4nb (nested_field_type t_kp (DOT I._receiving_counter)))).

Lemma hc4nb2_ke_add_segC_bt (bt: list int64) (j: Z) (w: int64) :
  Zlength bt = j -> j < 128 ->
  upd_Znth j (map Vlong bt ++ Zrepeat Vundef (128 - j)) (Vlong w) =
  map Vlong (bt ++ [w]) ++ Zrepeat Vundef (128 - (j + 1)).
Proof. intros L J. list_solve. Qed.

(* the drawn keypair *)
Definition hc4nb2_ke_add_segC_bit (b: Z) : bool := negb (Int.eq (Int.and (Int.repr b) (Int.repr 1)) Int.zero).

Definition hc4nb2_ke_add_segC_K (bs1: list Z) (sb: int64) (sv: Z) (bs2: list Z) (rb: int64) (rv: Z) (sc rc: int64)
    (bt: list int64) (ri ini: Z) (rf: int) (id: int64) : keypair :=
  mkKP (mkSym (map Byte.repr bs1) sb (hc4nb2_ke_add_segC_bit sv)) sc
       (mkSym (map Byte.repr bs2) rb (hc4nb2_ke_add_segC_bit rv)) rc bt (Int.repr ri) (hc4nb2_ke_add_segC_bit ini) rf id.

Lemma hc4nb2_ke_add_segC_bit_val b :
  Vint (if Int.eq (Int.and (Int.repr b) (Int.repr 1)) Int.zero then Int.zero else Int.one) =
  Val.of_bool (hc4nb2_ke_add_segC_bit b).
Proof. unfold hc4nb2_ke_add_segC_bit. destruct (Int.eq _ _); reflexivity. Qed.

Lemma hc4nb2_ke_add_segC_bytes (bs: list Z) :
  Forall (fun b : Z => 0 <= b <= Byte.max_unsigned) bs ->
  map (fun b : Z => Vint (Int.repr b)) bs = bytes (map Byte.repr bs).
Proof.
  intros F. unfold bytes. rewrite map_map. apply map_ext_in. intros a Ha.
  rewrite Forall_forall in F. specialize (F a Ha).
  unfold Vubyte. rewrite Byte.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma hc4nb2_ke_add_segC_Kok bs1 sb sv bs2 rb rv sc rc bt ri ini rf id :
  Zlength bs1 = 32 -> Zlength bs2 = 32 -> Zlength bt = 128 ->
  0 <= Int64.unsigned sb < 2 ^ 62 -> 0 <= Int64.unsigned rb < 2 ^ 62 -> 0 < Int.unsigned rf < 2147483647 ->
  kd_K_ok (hc4nb2_ke_add_segC_K bs1 sb sv bs2 rb rv sc rc bt ri ini rf id).
Proof.
  intros. unfold kd_K_ok, hc4nb2_ke_add_segC_K; simpl. rewrite !Zlength_map. tauto.
Qed.

Ltac hc4nb2_ke_add_segC_cc :=
  repeat match goal with
  | |- context [@field_at Noise.CS ?sh ?t ?gfs ?v ?p] =>
      rewrite (f_equal (fun f => f p) (@field_at_change_composite Noise.CS CS4nb hc4nb2_ke_add_segC_cce sh t gfs v v (JMeq_refl v) eq_refl))
  end.

(* the drawn fields form the keypair's body *)
Lemma hc4nb2_ke_add_segC_fold k bs1 sb sv bs2 rb rv sc rc bt ri ini rf id :
  @field_compatible Noise.CS t_kp [] k ->
  Zlength bs1 = 32 -> Zlength bs2 = 32 -> Zlength bt = 128 ->
  Forall (fun b : Z => 0 <= b <= Byte.max_unsigned) bs1 -> Forall (fun b : Z => 0 <= b <= Byte.max_unsigned) bs2 ->
  field_at Ews t_kp (DOT I._receiving)
    (map (fun b : Z => Vint (Int.repr b)) bs2,
     (Vlong rb, Vint (if Int.eq (Int.and (Int.repr rv) (Int.repr 1)) Int.zero then Int.zero else Int.one))) k *
  field_at Ews t_kp (DOT I._sending)
    (map (fun b : Z => Vint (Int.repr b)) bs1,
     (Vlong sb, Vint (if Int.eq (Int.and (Int.repr sv) (Int.repr 1)) Int.zero then Int.zero else Int.one))) k *
  field_at Ews t_kp (DOT I._sending_counter) (Vlong sc) k *
  field_at Ews t_kp (DOT I._receiving_counter) (Vlong rc, (hc4nb2_ke_add_segC_lk, map Vlong bt)) k *
  field_at Ews t_kp (DOT I._remote_index) (Vint (Int.repr ri)) k *
  field_at Ews t_kp (DOT I._i_am_the_initiator)
    (Vint (if Int.eq (Int.and (Int.repr ini) (Int.repr 1)) Int.zero then Int.zero else Int.one)) k *
  field_at Ews t_kp (DOT I._refcount) (Vint rf) k *
  field_at_ Ews t_kp (DOT I._rcu) k *
  field_at Ews t_kp (DOT I._internal_id) (Vlong id) k *
  spacer Ews 1181 1184 k |--
  kp_body_rep k (hc4nb2_ke_add_segC_K bs1 sb sv bs2 rb rv sc rc bt ri ini rf id).
Proof.
  intros FC L1 L2 L3 F1 F2.
  rewrite !hc4nb2_ke_add_segC_bit_val, (hc4nb2_ke_add_segC_bytes bs1 F1), (hc4nb2_ke_add_segC_bytes bs2 F2).
  unfold kp_body_rep. hc4nb2_ke_add_segC_cc.
  unfold hc4nb2_ke_add_segC_K, kp_ok, symkey_val; simpl kp_send; simpl kp_recv; simpl sk_key; simpl sk_birth; simpl sk_valid.
  Exists hc4nb2_ke_add_segC_lk (default_val (nested_field_type t_kp (DOT I._rcu))).
  hc4nb2_ke_add_segC_cc. unfold field_at_. entailer!.
  unfold bytes; rewrite !Zlength_map; auto.
Qed.

(* from nondet_bytes(kp->sending.key, 32) to kp->internal_id = draw_u64(): the keypair's body holds a keypair K
   with kd_K_ok K (keys 32 bytes, backtrack 128 words, birthdates < 2^62, 0 < refs < INT_MAX) *)
Lemma hc4nb2_ke_add_segC_ok {Espec: OracleKind} (CSw: hc4nb2_ke_add_csw) (l k n i owner tab peers p: val) (fl: int)
    (gv: globals) (FR: mpred) (rest: statement) (R: ret_assert) :
  @field_compatible Noise.CS t_kp [] k ->
  (forall K, kd_K_ok K ->
     @semax CS4nb Espec (hc4nb2_ke_add_Delta CSw)
       (PROPx [] (LOCALx (hc4nb2_ke_add_locs l k n i owner tab peers p fl gv) (SEPx [kp_body_rep k K; FR])))
       rest R) ->
  @semax CS4nb Espec (hc4nb2_ke_add_Delta CSw)
    (PROPx [] (LOCALx (hc4nb2_ke_add_locs l k n i owner tab peers p fl gv) (SEPx [hc4nb2_ke_add_body0 k; FR])))
    (hc4nb2_ke_add_sC rest) R.
Proof.
  intros FC Hrest. rewrite hc4nb2_ke_add_segC_b0. unfold hc4nb2_ke_add_sC, hc4nb2_ke_add_locs, hc4nb2_ke_add_Delta.
  abbreviate_semax.
  assert (FC4: @field_compatible CS4nb t_kp [] k)
    by (apply (@field_compatible_change_composite Noise.CS CS4nb _ t_kp); [reflexivity | auto]).
  sep_apply (hc4nb2_ke_add_segC_ks k FC4). sep_apply (hc4nb2_ke_add_segC_kr k FC4).
  forward_call (field_address t_kp [StructField I._key; StructField I._sending] k, 32, Ews).
  Intros bs1. sep_apply (hc4nb2_ke_add_segC_ks_close k (map (fun b : Z => Vint (Int.repr b)) bs1)).
  forward_call tt. Intros sb. forward.
  forward_call tt. Intros sv. forward.
  forward_call (field_address t_kp [StructField I._key; StructField I._receiving] k, 32, Ews).
  Intros bs2. sep_apply (hc4nb2_ke_add_segC_kr_close k (map (fun b : Z => Vint (Int.repr b)) bs2)).
  forward_call tt. Intros rb. forward.
  forward_call tt. Intros rv. forward.
  forward_call tt. Intros sc. forward.
  forward_call tt. Intros rc. forward.
  forward.
  match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx (?a :: ?b :: ?c :: _ :: ?rest)))) _ _ =>
  forward_loop (EX j: Z, EX bt: list int64,
    PROPx [0 <= j <= 128; Zlength bt = j]
    (LOCALx [temp HC._j (Vlong (Int64.repr j)); temp HC._l l; temp HC._k k; temp HC._n n; temp HC._i i;
             temp HC._owner owner; temp HC._kp k; gvars gv; temp HC._t tab; temp HC._peers peers; temp HC._p p;
             temp HC._fill (Vint fl)]
    (SEPx (a :: b :: c :: field_at Ews t_kp (DOT I._receiving_counter)
             (Vlong rc, (hc4nb2_ke_add_segC_lk, map Vlong bt ++ Zrepeat Vundef (128 - j))) k :: rest))))%assert
    continue: (EX j: Z, EX bt: list int64,
    PROPx [0 <= j < 128; Zlength bt = j + 1]
    (LOCALx [temp HC._j (Vlong (Int64.repr j)); temp HC._l l; temp HC._k k; temp HC._n n; temp HC._i i;
             temp HC._owner owner; temp HC._kp k; gvars gv; temp HC._t tab; temp HC._peers peers; temp HC._p p;
             temp HC._fill (Vint fl)]
    (SEPx (a :: b :: c :: field_at Ews t_kp (DOT I._receiving_counter)
             (Vlong rc, (hc4nb2_ke_add_segC_lk, map Vlong bt ++ Zrepeat Vundef (128 - (j + 1)))) k :: rest))))%assert
    break: (EX bt: list int64,
    PROPx [Zlength bt = 128]
    (LOCALx [temp HC._l l; temp HC._k k; temp HC._n n; temp HC._i i; temp HC._owner owner; temp HC._kp k;
             gvars gv; temp HC._t tab; temp HC._peers peers; temp HC._p p; temp HC._fill (Vint fl)]
    (SEPx (a :: b :: c :: field_at Ews t_kp (DOT I._receiving_counter)
             (Vlong rc, (hc4nb2_ke_add_segC_lk, map Vlong bt)) k :: rest))))%assert end.
  { Exists 0 (@nil int64). entailer!. }
  { Intros j bt.
    forward_if.
    2: { change (Int.signed (Int.divs (Int.repr 8192) (Int.repr 64))) with 128 in H9.
         unfold Int64.ltu in H9; rewrite !Int64.unsigned_repr in H9 by rep_lia.
         destruct (zlt j 128); try discriminate. assert (j = 128) by lia. subst j. forward.
         destruct R; unfold loop1_ret_assert. cbv beta iota.
         Exists bt. rewrite H10, Z.sub_diag, app_nil_r. entailer!. }
    change (Int.signed (Int.divs (Int.repr 8192) (Int.repr 64))) with 128 in H9.
    unfold Int64.ltu in H9; rewrite !Int64.unsigned_repr in H9 by rep_lia.
    destruct (zlt j 128); try discriminate.
    forward_call tt. Intros w. forward.
    Exists j (bt ++ [w]). rewrite (hc4nb2_ke_add_segC_bt bt j w H8 l0). entailer!.
    rewrite Zlength_app, Zlength_cons, Zlength_nil; lia. }
  { Intros j bt. forward. Exists (j + 1) bt. entailer!. }
  Intros bt.
  forward_call tt. Intros ri. forward.
  forward_call tt. Intros ini. forward.
  forward_call tt. Intros rf. forward.
  forward_call tt. Intros id. forward.
  eapply semax_pre; [| apply (Hrest (hc4nb2_ke_add_segC_K bs1 sb sv bs2 rb rv sc rc bt ri ini rf id))].
  2: apply hc4nb2_ke_add_segC_Kok; auto.
  unfold hc4nb2_ke_add_locs.
  sep_apply (hc4nb2_ke_add_segC_fold k bs1 sb sv bs2 rb rv sc rc bt ri ini rf id FC H H3 H7 H0 H4).
  entailer!.
Qed.
End SegC.
