(*
   An unhashed entry outside the table joins the pool (its address was not in it), and the peer field of a
   pool entry (a handshake's entry: viewed as a field of struct noise_handshake) can be read. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.

#[local] Existing Instance Noise.CS.
Local Open Scope logic.

Lemma prot3_begin_session_pool_glb sh1 sh2 :
  writable_share sh1 -> writable_share sh2 -> sepalg.nonidentity (Share.glb sh1 sh2).
Proof.
  intros W1 W2. apply nonempty_writable_glb; auto with share.
Qed.

Lemma prot3_begin_session_pool_iter {A: Type} (f: val * share * A -> mpred) D a sh v :
  sfind D a = Some (sh, v) -> iter_sepcon f D = f (a, sh, v) * iter_sepcon f (sdel D a).
Proof.
  induction D as [| [[x sh'] w] D IH]; simpl; intros H; [discriminate |].
  destruct (EqDec_val x a).
  - inv H. reflexivity.
  - simpl. rewrite (IH H). rewrite <- !sepcon_assoc, (sepcon_comm (f (x, sh', w))). reflexivity.
Qed.

Lemma prot3_begin_session_pool_sfind_in {A: Type} D a sh (v: A) :
  sfind D a = Some (sh, v) -> In (a, sh, v) D.
Proof.
  induction D as [| [[x sh'] w] D IH]; simpl; intros H; [discriminate |].
  destruct (EqDec_val x a); [inv H; auto | auto].
Qed.

Lemma prot3_begin_session_pool_in_saddrs {A: Type} D a :
  In a (@saddrs A D) -> exists sh v, In (a, sh, v) D.
Proof.
  induction D as [| [[x sh'] w] D IH]; simpl; intros H; [contradiction |].
  destruct H as [H | H].
  - subst. eauto.
  - destruct (IH H) as (sh & v & Hi). eauto.
Qed.

Lemma prot3_begin_session_pool_succ_notin L a : ~ In a L -> succ_in L a = nullval.
Proof.
  induction L as [| x L IH]; simpl; intros H; auto.
  destruct (EqDec_val x a); [subst; tauto | auto].
Qed.

Lemma prot3_begin_session_pool_vin_notin L a : ~ In a L -> vin a L = false.
Proof.
  intros H. unfold vin. destruct (in_dec eq_dec a L); tauto.
Qed.

Lemma prot3_begin_session_pool_add sht tab T a E :
  itable sht tab T * entry_out Ews a E |-- !! (~ In a (saddrs (t_D T))) && itable sht tab (t_add T a Ews E).
Proof.
  unfold itable. Intros. destruct H as (HL & Hincl & HD & HW).
  assert_PROP (~ In a (saddrs (t_D T))) as Hn.
  { apply not_prop_right. intros Hi.
    destruct (prot3_begin_session_pool_in_saddrs _ _ Hi) as (sh & v & Hin).
    assert (Wsh: writable_share sh) by (rewrite Forall_forall in HW; exact (HW _ Hin)).
    sep_apply (iter_sepcon_in_true (pool_item_rep (t_L T)) _ _ Hin).
    unfold pool_item_rep, entry_out, entry_at.
    sep_apply (data_at_conflict_glb sh Ews t_entry_s (entry_val v (succ_in (t_L T) a) (vin a (t_L T)))
                 (entry_val E nullval false) a).
    { apply prot3_begin_session_pool_glb; auto with share. }
    entailer!. }
  assert (HnL: ~ In a (t_L T)) by (intro; apply Hn, Hincl; auto).
  unfold t_add; simpl.
  rewrite (prot3_begin_session_pool_succ_notin _ _ HnL), (prot3_begin_session_pool_vin_notin _ _ HnL).
  unfold entry_out.
  assert (Hwf: itable_wf {| t_D := (a, Ews, E) :: t_D T; t_L := t_L T |}).
  { unfold itable_wf; simpl. split3; [auto | | split].
    - intros x Hx. right. auto.
    - constructor; auto.
    - constructor; auto with share. }
  entailer!.
Qed.

Definition prot3_begin_session_pool_rest (sh: share) (a: val) (E: entry) (n: val) (h: bool) : mpred :=
  field_at sh t_entry_s (DOT I._next) n a *
  (field_at sh t_entry_s (DOT I._hashed) (Val.of_bool h) a * spacer sh 17 20 a *
   (field_at sh t_entry_s (DOT I._type) (Vint (e_type E)) a *
    (field_at sh t_entry_s (DOT I._index) (Vint (e_index E)) a * spacer sh 28 32 a))).

Lemma prot3_begin_session_pool_split sh a E n h :
  field_compatible t_hs [] a ->
  entry_at sh a E n h =
  field_at sh t_hs (DOT I._entry DOT I._peer) (e_peer E) a * prot3_begin_session_pool_rest sh a E n h.
Proof.
  intros FC. unfold entry_at, entry_val, prot3_begin_session_pool_rest.
  unfold_data_at (data_at _ _ _ a).
  f_equal.
  assert (FCe: field_compatible t_hs (DOT I._entry) a)
    by (apply field_compatible_cons; simpl; split; [left; reflexivity | auto]).
  assert (FCe2 := field_compatible_nested_field _ _ _ FCe).
  simpl in FCe2. rewrite isptr_offset_val_zero in FCe2 by (destruct FC; auto).
  assert (FCp: field_compatible t_entry_s (DOT I._peer) a)
    by (apply field_compatible_cons; simpl; split; [left; reflexivity | auto]).
  assert (FCq: field_compatible t_hs (DOT I._entry DOT I._peer) a)
    by (apply field_compatible_cons; simpl; split; [left; reflexivity | auto]).
  rewrite !field_at_data_at, !field_compatible_field_address by auto.
  reflexivity.
Qed.

Lemma prot3_begin_session_pool_peer sht tab T a sh E :
  sfind (t_D T) a = Some (sh, E) -> field_compatible t_hs [] a ->
  itable sht tab T |-- !! writable_share sh &&
    (field_at sh t_hs (DOT I._entry DOT I._peer) (e_peer E) a *
     (field_at sh t_hs (DOT I._entry DOT I._peer) (e_peer E) a -* itable sht tab T)).
Proof.
  intros Hf FC. unfold itable.
  apply derives_extract_prop. intros Hwf.
  assert (Wsh: writable_share sh).
  { destruct Hwf as (_ & _ & _ & HW). rewrite Forall_forall in HW.
    exact (HW _ (prot3_begin_session_pool_sfind_in _ _ _ _ Hf)). }
  rewrite (prot3_begin_session_pool_iter _ _ _ _ _ Hf). simpl pool_item_rep.
  rewrite (prot3_begin_session_pool_split sh a E _ _ FC).
  apply andp_right; [apply prop_right; auto |].
  match goal with |- ?H * (?F * ?R * ?I) |-- ?F * _ =>
    apply derives_trans with (F * (H * R * I)); [cancel |]
  end.
  apply sepcon_derives; [apply derives_refl |].
  rewrite <- wand_sepcon_adjoint.
  apply andp_right; [apply prop_right; auto |].
  cancel.
Qed.
