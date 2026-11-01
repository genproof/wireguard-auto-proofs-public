
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.

#[local] Existing Instance Noise.CS.
Local Open Scope logic.

(* ------------------------------------------------------------------------------------------------ *)
(* Association lists                                                                                *)
(* ------------------------------------------------------------------------------------------------ *)

Lemma prot3_begin_session_sfind_sdel {A: Type} (D: list (val * share * A)) a b :
  b <> a -> sfind (sdel D a) b = sfind D b.
Proof.
  intros N. induction D as [|[[x sh] v] D IH]; simpl; auto.
  destruct (EqDec_val x a); simpl.
  - subst. destruct (EqDec_val a b); [congruence | auto].
  - destruct (EqDec_val x b); auto.
Qed.

Lemma prot3_begin_session_sfind_in {A: Type} (D: list (val * share * A)) a x :
  sfind D a = Some x -> In a (saddrs D).
Proof.
  induction D as [|[[y sh] v] D IH]; simpl; [discriminate|].
  destruct (EqDec_val y a); auto.
Qed.

Lemma prot3_begin_session_t_entry_sfind (T: tstate) a E :
  t_entry T a = Some E -> exists sh, sfind (t_D T) a = Some (sh, E).
Proof.
  unfold t_entry. destruct (sfind (t_D T) a) as [[sh E']|]; [|discriminate].
  intros H; inversion H; subst; eauto.
Qed.

Lemma prot3_begin_session_vremove_incl a L : incl (vremove a L) L.
Proof.
  induction L as [|x L IH]; simpl; [apply incl_refl|].
  destruct (EqDec_val x a).
  - intros y Hy. right. auto.
  - intros y [E|Hy]; [left; auto | right; auto].
Qed.

(* ------------------------------------------------------------------------------------------------ *)
(* kp_put and add_new_keypair keep the pool entries at other addresses                              *)
(* ------------------------------------------------------------------------------------------------ *)

Lemma prot3_begin_session_put_sfind k u W a :
  a <> k -> sfind (t_D (kw_T (kp_put k u W))) a = sfind (t_D (kw_T W)) a.
Proof.
  intros N. unfold kp_put.
  destruct (eq_dec k nullval); auto.
  destruct (afind (kw_KS W) k) as [K|]; auto.
  destruct (Int.eq (rc_sub1 (kp_refs K)) Int.zero); simpl; destruct u; simpl; auto;
    apply prot3_begin_session_sfind_sdel; auto.
Qed.

Lemma prot3_begin_session_put_L k u W : incl (t_L (kw_T (kp_put k u W))) (t_L (kw_T W)).
Proof.
  unfold kp_put.
  destruct (eq_dec k nullval); [apply incl_refl|].
  destruct (afind (kw_KS W) k) as [K|]; [|apply incl_refl].
  destruct (Int.eq (rc_sub1 (kp_refs K)) Int.zero); simpl; destruct u; simpl;
    repeat apply prot3_begin_session_vremove_incl; try apply incl_refl;
    eapply incl_tran; apply prot3_begin_session_vremove_incl.
Qed.

Lemma prot3_begin_session_add_keeps P new init W a :
  a <> p_cur P -> a <> p_prev P -> a <> p_next P ->
  sfind (t_D (kw_T (snd (add_new_keypair_model P new init W)))) a = sfind (t_D (kw_T W)) a /\
  incl (t_L (kw_T (snd (add_new_keypair_model P new init W)))) (t_L (kw_T W)).
Proof.
  intros Nc Np Nn. unfold add_new_keypair_model.
  destruct init; [destruct (negb (eq_dec (p_next P) nullval))|]; simpl;
    repeat rewrite prot3_begin_session_put_sfind by auto; split; auto;
    repeat (eapply incl_tran; [apply prot3_begin_session_put_L|]); apply incl_refl.
Qed.

(* ------------------------------------------------------------------------------------------------ *)
(* The new keypair joins the keypair world                                                          *)
(* ------------------------------------------------------------------------------------------------ *)

Lemma prot3_begin_session_slots_new P KS k :
  slots_ok P KS -> k <> nullval -> ~ In k (map fst KS) ->
  k <> p_cur P /\ k <> p_prev P /\ k <> p_next P.
Proof.
  intros [F _] Nk Nin. inversion F as [|? ? Hc F1]; subst. inversion F1 as [|? ? Hp F2]; subst.
  inversion F2 as [|? ? Hn _]; subst.
  split; [|split]; intros E; rewrite <- E in *; tauto.
Qed.

Lemma prot3_begin_session_slots_other P KS a :
  slots_ok P KS -> a <> nullval -> ~ In a (map fst KS) ->
  a <> p_cur P /\ a <> p_prev P /\ a <> p_next P.
Proof. apply prot3_begin_session_slots_new. Qed.

Lemma prot3_begin_session_slots_cons P H KS k K :
  slots_ok P KS -> slots_ok (p_set_hs P H) ((k, K) :: KS).
Proof.
  intros [F ND]. split; [|exact ND].
  simpl. rewrite Forall_forall in F |- *. intros x Hx. destruct (F x Hx); [left; auto | right; right; auto].
Qed.

Lemma prot3_begin_session_pool_cons T p KS k K :
  kps_in_pool T p KS -> ~ In k (map fst KS) ->
  kps_in_pool (t_add T k Ews (mkEntry p IDX_KEYPAIR Int.zero)) p ((k, K) :: KS).
Proof.
  intros [ND F] Nin. split; [constructor; auto|].
  constructor.
  - exists (mkEntry p IDX_KEYPAIR Int.zero). simpl. destruct (EqDec_val k k); [auto | congruence].
  - rewrite Forall_forall in F |- *. intros [x X] Hx. destruct (F _ Hx) as [E [HE HP]].
    exists E. simpl in *. destruct (EqDec_val k x); [|auto].
    subst. exfalso. apply Nin. apply (in_map fst) in Hx. auto.
Qed.

Lemma prot3_begin_session_e_peer_of_hs KS T S p :
  hs_in_pool T p -> e_peer_of_hs (mkKW KS T S) (hs_addr p) = p.
Proof.
  intros [E [HE HP]]. unfold e_peer_of_hs. simpl. rewrite HE. auto.
Qed.

(* ------------------------------------------------------------------------------------------------ *)
(* Two keypairs are at different addresses                                                          *)
(* ------------------------------------------------------------------------------------------------ *)

Lemma prot3_begin_session_kp_conflict CSw k K K' :
  keypair_rep CSw k K * keypair_rep CSw k K' |-- FF.
Proof.
  unfold keypair_rep. Intros.
  assert (C: @field_at Noise.CS Ews t_kp [StructField I._internal_id] (Vlong (kp_id K)) k *
             @field_at Noise.CS Ews t_kp [StructField I._internal_id] (Vlong (kp_id K')) k |-- FF).
  { apply (@field_at_conflict Noise.CS); [auto | simpl; lia]. }
  sep_apply C. entailer!.
Qed.

Lemma prot3_begin_session_kp_notin CSw KS k K :
  keypairs_rep CSw KS * keypair_rep CSw k K |-- !! (~ In k (map fst KS)).
Proof.
  apply not_prop_right. intros Hin.
  unfold keypairs_rep. induction KS as [|[x X] KS IH]; simpl in *; [contradiction|].
  destruct Hin as [E|Hin].
  - subst x. rewrite (sepcon_comm (keypair_rep CSw k X)), sepcon_assoc.
    sep_apply (prot3_begin_session_kp_conflict CSw k X K). entailer!.
  - rewrite sepcon_assoc. sep_apply (IH Hin). entailer!.
Qed.
