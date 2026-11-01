(* law consume_response_any, phase PK: statement 12 of main: kes = kents_add(&ita, peers, NULL, 1).
*)
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
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_cut.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_model.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_spec.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_defs.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_conv.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_pk_lemmas.
Require WgNoise.harness.x_consume_response_any.code.

#[local] Existing Instance W_consume_response_any.
Local Open Scope logic.

Lemma hcr5_pk_head_ptr NS :
  hnodes_rep4 W (hcr5_head NS) NS |--
  !! (is_pointer_or_null (hcr5_head NS) /\ (NS <> [] -> hcr5_head NS <> nullval)).
Proof.
  destruct NS as [| N NS]; simpl.
  - apply prop_right. split; [reflexivity | congruence].
  - Intros nx. entailer!.
    match goal with H: field_compatible _ _ (hn_addr N) |- _ => destruct H as [Hp _] end.
    split; [apply isptr_is_pointer_or_null; auto |].
    intros _ E. rewrite E in Hp. inv Hp.
Qed.

Section Phase.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hcr5_PK_ok {Espec: OracleKind} gv L FR :
  hcr5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec -> 
  semax (hcr5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hcr5_SA x25519 gv L FR) hcr5_PK
    (overridePost (hcr5_SK x25519 gv L FR) (hcr5_R gv)).
Proof.
  intros HH. unfold hcr5_SA, hcr5_Delta, hcr5_R, hcr5_PK. simplify_func_tycontext.
  Intros R S NS PS head nb T.
  abbreviate_semax.
  unfold hcr5_world, hcr5_globs, hcr5_lvars, hcr5_snaps0, hcr5_scr; cbn [app].
  assert_PROP (is_pointer_or_null (hcr5_head NS) /\ (NS <> [] -> hcr5_head NS <> nullval)) as Hhd
    by (sep_apply (hcr5_pk_head_ptr NS); entailer!).
  destruct Hhd as [Hhp Hhn].
  forward.
  forward_call (gv, Tsh, l_ita L, T, hcr5_head NS, NS, nullval, PS, Int.one, S, hcr5_w0).
  { destruct H0 as (Hpok & Hwf & _ & Hnp & _). split; auto. split; [apply hcr5_pk_owners; auto |].
    (* common4 v4.1: the owners' slots are NULL or pool entries (here NULL: no kent yet) *)
    eapply Forall_impl; [| exact Hpok]. intros [[p sh] P] Hk. destruct Hk as (_ & _ & _ & _ & _ & _ & Hs).
    eapply Forall_impl; [| exact Hs]. intros v [Hv | []]. left; exact Hv. }
  Intros KD.
  forward.
  change (negb (Int.eq Int.one Int.zero)) with true.
  destruct (hcr5_pk_core L NS PS T head nb KD H1 H0 H2 H3) as [Hpool Hlist].
  unfold hcr5_SK.
  Exists R (kents_S S KD) NS (kents_PS true PS KD) head nb (kents_T T KD) (map kd_kent KD).
  rewrite hcr5_pk_khead.
  unfold hcr5_world, hcr5_globs, hcr5_lvars, hcr5_snaps0, hcr5_scr; cbn [app].
  entailer!.
Qed.

End Phase.
