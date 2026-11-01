(* the lent objects' addresses are valid pointers.
   (Not the addresses of VKents / VKeypairs: a kent's / keypair's address is its entry's, owned by the index
   table's pool, not by kents_rep / keypairs_rep: hc4b_ke_k1_vaddrs leaves them out.) *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Local Open Scope logic.

(* the addresses of a lent object that its memory makes valid *)
Definition hc4b_ke_k1_vaddrs (o: vobj) : list val :=
  match o with
  | VKents _ _ | VKeypairs _ => []
  | _ => vobj_addrs o
  end.
Definition hc4b_ke_k1_vobjs_vaddrs (VO: list vobj) : list val := concat (map hc4b_ke_k1_vaddrs VO).

Section VP.
#[local] Existing Instance Noise.CS.

Lemma hc4b_ke_k1_vp_peer sh p P R :
  readable_share sh -> peer_rep sh p P * R |-- valid_pointer p.
Proof.
  intros RS. apply sepcon_valid_pointer1. unfold peer_rep. Intros.
  do 10 apply sepcon_valid_pointer1.
  apply field_at_valid_ptr0; [auto | simpl; lia | reflexivity].
Qed.

Lemma hc4b_ke_k1_vp_peers PS x R :
  Forall (fun x => match x with (_, sh, _) => readable_share sh end) PS -> In x (map peer_addr4 PS) ->
  peers_rep PS * R |-- valid_pointer x.
Proof.
  revert R. induction PS as [|[[a sh] P] PS IH]; simpl; intros R HF Hin; [contradiction|].
  inversion HF; subst. unfold peers_rep in *. simpl iter_sepcon. destruct Hin as [<- | Hin].
  - rewrite sepcon_assoc. apply hc4b_ke_k1_vp_peer; auto.
  - rewrite sepcon_assoc, (sepcon_comm (peer_rep sh a P)), sepcon_assoc. apply IH; auto.
Qed.

Lemma hc4b_ke_k1_vp_dev sh wg D x R :
  readable_share sh -> In x [wg; id_addr wg; cc_addr wg] -> device_rep sh wg D * R |-- valid_pointer x.
Proof.
  intros RS Hin. apply sepcon_valid_pointer1. unfold device_rep, identity_rep, checker_rep. Intros.
  destruct Hin as [<- | [<- | [<- | []]]].
  - do 4 apply sepcon_valid_pointer1.
    apply field_at_valid_ptr0; [auto | simpl; lia | reflexivity].
  - Intros lk1 lk2. apply sepcon_valid_pointer1. apply sepcon_valid_pointer1. apply sepcon_valid_pointer1.
    apply sepcon_valid_pointer2. apply data_at_valid_ptr; [auto | simpl; lia].
  - Intros lk1 lk2. apply sepcon_valid_pointer1. apply sepcon_valid_pointer1.
    apply sepcon_valid_pointer2. apply data_at_valid_ptr; [auto | simpl; lia].
Qed.

Lemma hc4b_ke_k1_saddrs_in (D: list (val * share * entry)) a :
  In a (saddrs D) -> exists sh E, In (a, sh, E) D.
Proof.
  induction D as [|[[x shx] w] D IH]; simpl; intros H; [contradiction|].
  destruct H as [<- | H]; [eauto|]. destruct (IH H) as (sh & E & HI). eauto.
Qed.

Lemma hc4b_ke_k1_vp_itab sh tab T x R :
  readable_share sh -> In x (tab :: saddrs (t_D T)) -> itable sh tab T * R |-- valid_pointer x.
Proof.
  intros RS [<- | Hin].
  - apply sepcon_valid_pointer1. unfold itable. Intros. apply sepcon_valid_pointer1.
    apply data_at_valid_ptr; [auto | simpl; lia].
  - apply sepcon_valid_pointer1. unfold itable. Intros. apply sepcon_valid_pointer2.
    destruct (hc4b_ke_k1_saddrs_in _ _ Hin) as (shx & E & HE).
    eapply derives_trans; [apply iter_sepcon_in_true; exact HE|].
    apply sepcon_valid_pointer1. unfold pool_item_rep, entry_at.
    assert (writable_share shx).
    { destruct H as (_ & _ & _ & HF). rewrite Forall_forall in HF. apply (HF _ HE). }
    apply data_at_valid_ptr; [auto | simpl; lia].
Qed.

Lemma hc4b_ke_k1_vp_obj CSw o x R :
  vobj_ok o -> In x (hc4b_ke_k1_vaddrs o) -> vobj_rep CSw o * R |-- valid_pointer x.
Proof.
  destruct o; simpl; intros OK Hin; try contradiction.
  - destruct Hin as [<- | []]. apply hc4b_ke_k1_vp_peer; auto.
  - apply hc4b_ke_k1_vp_peers; auto.
  - apply hc4b_ke_k1_vp_dev; auto.
  - apply hc4b_ke_k1_vp_itab; auto.
  - destruct Hin as [<- | []]. destruct OK as [RS LEN]. apply sepcon_valid_pointer1.
    unfold bytes_at. apply data_at_valid_ptr; [auto | simpl; rewrite Z.max_r by lia; lia].
  - destruct Hin as [<- | []]. destruct OK as [RS LEN]. apply sepcon_valid_pointer1.
    apply memory_block_valid_ptr; [auto | lia].
  - destruct Hin as [<- | []]. apply sepcon_valid_pointer1.
    apply (@malloc_token_valid_pointer CSw). apply OK.
Qed.

Lemma hc4b_ke_k1_vp_vobjs CSw VO x R :
  Forall vobj_ok VO -> In x (hc4b_ke_k1_vobjs_vaddrs VO) -> vobjs CSw VO * R |-- valid_pointer x.
Proof.
  revert R. induction VO as [|o VO IH]; simpl; intros R HF Hin; [contradiction|].
  inversion HF; subst. unfold hc4b_ke_k1_vobjs_vaddrs in Hin. simpl in Hin. apply in_app_or in Hin.
  unfold vobjs. simpl iter_sepcon. destruct Hin as [Hin | Hin].
  - rewrite sepcon_assoc. apply hc4b_ke_k1_vp_obj; auto.
  - rewrite sepcon_assoc, (sepcon_comm (vobj_rep CSw o)), sepcon_assoc. apply IH; auto.
Qed.

(* the form the comparisons use: NULL or own (valid by the caller's own memory) or lent *)
Lemma hc4b_ke_k1_vp_ok CSw VO own x R :
  Forall vobj_ok VO -> (x = nullval \/ In x own \/ In x (hc4b_ke_k1_vobjs_vaddrs VO)) ->
  (In x own -> R |-- valid_pointer x) ->
  vobjs CSw VO * R |-- valid_pointer x.
Proof.
  intros HF [-> | [Hown | Hin]] HR.
  - apply valid_pointer_null.
  - apply sepcon_valid_pointer2. auto.
  - apply hc4b_ke_k1_vp_vobjs; auto.
Qed.
End VP.

(* v4.1: VKents / VKeypairs lend no address, so every lent address is a valid one *)
Lemma hc4b_ke_k1_vaddrs_eq o : hc4b_ke_k1_vaddrs o = vobj_addrs o.
Proof. destruct o; reflexivity. Qed.

Lemma hc4b_ke_k1_HV_ok : forall VO x, In x (vobjs_addrs VO) -> In x (hc4b_ke_k1_vobjs_vaddrs VO).
Proof.
  intros VO x. unfold vobjs_addrs, hc4b_ke_k1_vobjs_vaddrs.
  rewrite (map_ext _ _ hc4b_ke_k1_vaddrs_eq). auto.
Qed.
