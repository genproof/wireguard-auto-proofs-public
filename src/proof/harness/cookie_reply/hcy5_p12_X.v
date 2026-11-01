(* law cookie_reply, phase P12, segment X:
   s71: if (target == NULL) CHECK(hnodes_same_except(peers, NULL)); else { tn = target->n; CHECK(hnodes_same_except(peers, tn->p)); CHECK(hs_same(&tn->snap, &tn->p->handshake) && tn->p->refcount.refcount == tn->refs && pr_same_but_cookie(&tn->rest, tn->p)); } (NEW; v1 H = hcy4_p12_H.v for the NULL case).
   St -> St over fixed values (hcy5_p12_defs.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_cut.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_spec.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_defs.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p12_defs.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p12_x_defs.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p12_x_null.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p12_x_some.
Require WgNoise.harness.x_cookie_reply.code.

#[local] Existing Instance W_cookie_reply.
Local Open Scope Z_scope.

(* the target is NULL or a cnode: a valid pointer *)
Lemma hcy5_p12_x_cns_vp l CL v :
  (v = nullval \/ In v (map (fun x => fst (fst x)) CL)) -> hcy5_cns l CL |-- valid_pointer v.
Proof.
  intros [-> | Hin]; [apply valid_pointer_null |].
  revert l; induction CL as [| [[c nd] o] CL IH]; intros l; [contradiction |].
  cbn [hcy5_cns]. Intros.
  destruct Hin as [Hv | Hin].
  - simpl in Hv. subst v.
    apply sepcon_valid_pointer1.
    apply sepcon_valid_pointer1, sepcon_valid_pointer1, sepcon_valid_pointer2.
    apply field_at_valid_ptr0; auto. vm_compute. reflexivity.
  - apply sepcon_valid_pointer2. apply IH; auto.
Qed.

Lemma hcy5_p12_x_cfind_in NS CL a :
  hcy5_cfind NS CL a = nullval \/ In (hcy5_cfind NS CL a) (map (fun x => fst (fst x)) CL).
Proof.
  induction CL as [| [[c nd] o] CL IH]; simpl; [left; reflexivity |].
  destruct (EqDec_val (hcy5_nodepeer NS nd) a); [right; left; reflexivity |].
  destruct IH as [IH | IH]; [left; exact IH | right; right; exact IH].
Qed.

Lemma hcy5_p12_x_tgt_in NS CL res :
  hcy5_tgt NS CL res = nullval \/ In (hcy5_tgt NS CL res) (map (fun x => fst (fst x)) CL).
Proof.
  destruct res as [[a P] |]; simpl; [apply hcy5_p12_x_cfind_in | left; reflexivity].
Qed.

Lemma hcy5_p12_x_tgt_vp l CL NS res : hcy5_cns l CL |-- valid_pointer (hcy5_tgt NS CL res).
Proof. apply hcy5_p12_x_cns_vp, hcy5_p12_x_tgt_in. Qed.
#[local] Hint Resolve hcy5_p12_x_tgt_vp : valid_pointer.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hcy5_p12_X_ok {Espec: OracleKind} gv L FR R S m c rp Q nonce rr CK CM NS PS T np CL KE CM' honest now2 :
  hcy5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hcy5_p12_inv x25519 xaead_enc R L Q m nonce rr CK CM NS PS T np CL KE CM' honest now2 ->
  semax (hcy5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hcy5_p12_St x25519 xaead_dec gv L FR R S m c rp Q rr CK NS PS T np CL KE CM' honest now2)
    hcy5_p12_s71
    (normal_ret_assert (hcy5_p12_St x25519 xaead_dec gv L FR R S m c rp Q rr CK NS PS T np CL KE CM' honest now2)).
Proof.
  intros HH Hinv.
  pose proof (hcy5_p12_x_null_ok x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R S m c rp Q nonce rr CK CM NS PS T np CL KE CM' honest now2 HH Hinv) as HN.
  pose proof (hcy5_p12_x_some_ok x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R S m c rp Q nonce rr CK CM NS PS T np CL KE CM' honest now2 HH Hinv) as HS.
  unfold hcy5_p12_St, hcy5_Delta in *. simplify_func_tycontext. abbreviate_semax.
  rewrite hcy5_p12_x_s71_eq. unfold hcy5_p12_x_cond.
  unfold hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_globs, hcy5_lvars in *; cbn [app] in *.
  forward_if.
  { exact (HN H). }
  { exact (HS H). }
Qed.

End Seg.
