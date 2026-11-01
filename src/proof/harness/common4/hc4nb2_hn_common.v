(* shared infrastructure of the bodies of the harness's
   peer list functions (hnodes_add / _snap / _same_except / _free / _pick, file hc4_body_hnodes.v), adapted from
   v1's hc_hnodes_bodies3.v: compspecs conversions CKS / HCS / Noise.CS <-> CS4nb, list segments, local facts.
   struct hnode at CS4nb: p @0, snap @8 (hs_snap, 288 bytes), refs @296, padding 300..304, rest @304 (pr_snap, 176
   bytes), next @480; sizeof 488. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_cs.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common.hc3_cs.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_cs.
Require Import WgNoise.proof.harness.common4.hc4_ctx.
Require Import WgNoise.proof.harness.common4.hc4a_nb_cs.
Local Open Scope logic.

(* IMPORTANT (v1 lesson): unify @reptype CKS .. with @reptype CS4nb .. through the compspecs names *)
#[global] Strategy expand [CS4nb CKS HCS].

#[export] Instance hc4nb2_hn_CKS_4 : change_composite_env CKS CS4nb. Proof. make_cs_preserve CKS CS4nb. Defined.
#[export] Instance hc4nb2_hn_4_CKS : change_composite_env CS4nb CKS. Proof. make_cs_preserve CS4nb CKS. Defined.
#[export] Instance hc4nb2_hn_HCS_4 : change_composite_env HCS CS4nb. Proof. make_cs_preserve HCS CS4nb. Defined.
#[export] Instance hc4nb2_hn_4_HCS : change_composite_env CS4nb HCS. Proof. make_cs_preserve CS4nb HCS. Defined.
#[export] Instance hc4nb2_hn_N_4 : change_composite_env Noise.CS CS4nb. Proof. make_cs_preserve Noise.CS CS4nb. Defined.
#[export] Instance hc4nb2_hn_4_N : change_composite_env CS4nb Noise.CS. Proof. make_cs_preserve CS4nb Noise.CS. Defined.

(* one node's struct (the value typed ONCE, here: never re-type a node value in a body proof, the kernel's
   reptype CKS ~ CS4nb conversion of struct hnode costs minutes in a Qed) *)
Definition hc4nb_cell (N: hnode4) (nx l: val) : mpred :=
  @data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) l.

Lemma hc4nb_rep_nil CSw l : hnodes_rep4 CSw l [] = !! (l = nullval) && emp.
Proof. reflexivity. Qed.

Lemma hc4nb_rep_cons CSw l N NS :
  hnodes_rep4 CSw l (N :: NS) =
  !! (l = hn_addr N) && EX nx: val,
    @malloc_token CSw Ews t_hnode4 l * hc4nb_cell N nx l * @malloc_token CSw Ews t_peer (hn_p N) *
    hnodes_rep4 CSw nx NS.
Proof. reflexivity. Qed.

(* the list segment of hnodes from l to e (e excluded) *)
Fixpoint hc4nb_seg (CSw: compspecs) (l e: val) (NS: list hnode4) : mpred :=
  match NS with
  | [] => !! (l = e) && emp
  | N :: NS' =>
      !! (l = hn_addr N) &&
      EX nx: val,
        @malloc_token CSw Ews t_hnode4 l *
        hc4nb_cell N nx l * @malloc_token CSw Ews t_peer (hn_p N) *
        hc4nb_seg CSw nx e NS'
  end.

Lemma hc4nb_seg_rep CSw l e NS1 NS2 :
  hc4nb_seg CSw l e NS1 * hnodes_rep4 CSw e NS2 |-- hnodes_rep4 CSw l (NS1 ++ NS2).
Proof.
  revert l; induction NS1 as [|N NS1 IH]; intros l; simpl hc4nb_seg; simpl app.
  - Intros. subst. cancel.
  - rewrite hc4nb_rep_cons. Intros nx. Exists nx. apply andp_right; [apply prop_right; auto|].
    sep_apply (IH nx). cancel.
Qed.

Lemma hc4nb_seg_snoc CSw l e nx N NS :
  e = hn_addr N ->
  hc4nb_seg CSw l e NS *
  (@malloc_token CSw Ews t_hnode4 e *
   hc4nb_cell N nx e * @malloc_token CSw Ews t_peer (hn_p N))
  |-- hc4nb_seg CSw l nx (NS ++ [N]).
Proof.
  intros HE; revert l; induction NS as [|M NS IH]; intros l; simpl hc4nb_seg; simpl app; simpl hc4nb_seg.
  - Intros. subst. Exists nx. apply andp_right; [apply prop_right; auto|]. cancel.
    apply andp_right; [apply prop_right; auto | apply derives_refl].
  - Intros x. Exists x. apply andp_right; [apply prop_right; auto|]. sep_apply (IH x). cancel.
Qed.

Lemma hc4nb_seg_nil CSw l : emp |-- hc4nb_seg CSw l l [].
Proof. simpl. entailer!. Qed.

Lemma hc4nb_rep_local_facts CSw l NS :
  hnodes_rep4 CSw l NS |-- !! (is_pointer_or_null l /\ (l = nullval <-> NS = [])).
Proof.
  destruct NS as [|N NS].
  - rewrite hc4nb_rep_nil. entailer!. split; auto.
  - rewrite hc4nb_rep_cons. Intros nx. subst l. unfold hc4nb_cell.
    sep_apply (@data_at_local_facts CKS). Intros. apply prop_right.
    match goal with Hf: field_compatible t_hnode4 [] _ |- _ => destruct Hf as [Hp _] end.
    destruct (hn_addr N); try contradiction. split; [exact I | split; intros X; discriminate].
Qed.

Lemma hc4nb_rep_valid_pointer CSw l NS : hnodes_rep4 CSw l NS |-- valid_pointer l.
Proof.
  destruct NS as [|N NS].
  - rewrite hc4nb_rep_nil. entailer!.
  - rewrite hc4nb_rep_cons. Intros nx. subst l. unfold hc4nb_cell.
    apply sepcon_valid_pointer1, sepcon_valid_pointer1, sepcon_valid_pointer2.
    apply (@data_at_valid_ptr CKS); [auto | simpl; lia].
Qed.

#[export] Hint Resolve hc4nb_rep_valid_pointer : valid_pointer.
#[export] Hint Resolve hc4nb_rep_local_facts : saturate_local.

Lemma hc4nb_peers_length NS PS : hnodes_peers4 NS PS -> Zlength NS = Zlength PS.
Proof. unfold hnodes_peers4; intros H. rewrite <- (Zlength_map _ _ hn_p), <- (Zlength_map _ _ peer_addr4), H. auto. Qed.

Lemma hc4nb_peers_nil PS : hnodes_peers4 [] PS -> PS = [].
Proof. unfold hnodes_peers4; simpl; intros H. destruct PS; [auto | discriminate]. Qed.

Lemma hc4nb_peers_cons N NS PS :
  hnodes_peers4 (N :: NS) PS -> exists x PS', PS = x :: PS' /\ hn_p N = peer_addr4 x /\ hnodes_peers4 NS PS'.
Proof.
  unfold hnodes_peers4; simpl; intros H. destruct PS as [|x PS']; [discriminate|].
  simpl in H. inversion H. exists x, PS'. auto.
Qed.

Lemma hc4nb_peers_app NS1 NS2 PS1 PS2 :
  hnodes_peers4 NS1 PS1 -> hnodes_peers4 NS2 PS2 -> hnodes_peers4 (NS1 ++ NS2) (PS1 ++ PS2).
Proof. unfold hnodes_peers4; intros; rewrite !map_app; f_equal; auto. Qed.

Lemma hc4nb_peers_split NS1 NS2 PS1 PS2 :
  Zlength NS1 = Zlength PS1 -> hnodes_peers4 (NS1 ++ NS2) (PS1 ++ PS2) -> hnodes_peers4 NS2 PS2.
Proof.
  unfold hnodes_peers4; revert PS1; induction NS1 as [|M NS1 IH]; intros PS1 HL H; destruct PS1 as [|y PS1].
  - exact H.
  - rewrite Zlength_nil, Zlength_cons in HL. pose proof (Zlength_nonneg PS1). lia.
  - rewrite Zlength_nil, Zlength_cons in HL. pose proof (Zlength_nonneg NS1). lia.
  - rewrite !Zlength_cons in HL. simpl in H. inversion H. apply (IH PS1); auto. lia.
Qed.

Lemma hc4nb2_hn_peers_app PS1 x : peers_rep (PS1 ++ [x]) = peers_rep PS1 * peer_item_rep x.
Proof. unfold peers_rep. rewrite iter_sepcon_app. simpl. rewrite sepcon_emp. auto. Qed.

Lemma hc4nb2_hn_peers_cons x PS : peers_rep (x :: PS) = peer_item_rep x * peers_rep PS.
Proof. reflexivity. Qed.

