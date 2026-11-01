(* law consume_initiation_any, phase P8, segment A3 (the else branch's statements 5..12) cut into
   one statement per lemma (port of v1's hci3_p8_A3_defs.v).  Every statement is a CHECK (a do { .. } while (0)
   block) that changes no memory: the intermediate state is hci5_p8_QA1 itself (QA1 -> QA1), the last one goes
   QA1 -> Q2.
     s5   CHECK(h->state == HANDSHAKE_CONSUMED_INITIATION)
     s6   CHECK(bytes_eq(h->remote_ephemeral, msg->unencrypted_ephemeral, 32))
     s7   CHECK(bytes_eq(h->latest_timestamp, ci.ts, 12))
     s8   CHECK(bytes_eq(h->hash, ci.st.h, 32) && bytes_eq(h->chaining_key, ci.st.ck, 32))
     s9   CHECK(h->remote_index == msg->sender_index)
     s10  CHECK(h->last_initiation_consumption == m_last_consumption(s->last_initiation_consumption, now))
     s11  CHECK(h->entry.{peer,next,hashed,type,index} == s->.., static_identity, 4 x bytes_eq with s)
     s12  CHECK(target->p->refcount.refcount == target->refs && pr_same(&target->rest, target->p))  QA1 -> Q2
   Segment lemmas: hci5_p8_A3_s<k>_ok in hci5_p8_A3_s<k>.v; shared facts: hci5_p8_A3_pure.v, hci5_p8_A3_sep.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_cut.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p8_defs.
Require WgNoise.harness.x_consume_initiation_any.code.

Local Open Scope Z_scope.

Definition hci5_p8_A3_s5 := ltac:(let x := eval cbv beta iota delta [nth hci5_p8_acc] in (nth 5 hci5_p8_acc Sskip) in exact x).
Definition hci5_p8_A3_s6 := ltac:(let x := eval cbv beta iota delta [nth hci5_p8_acc] in (nth 6 hci5_p8_acc Sskip) in exact x).
Definition hci5_p8_A3_s7 := ltac:(let x := eval cbv beta iota delta [nth hci5_p8_acc] in (nth 7 hci5_p8_acc Sskip) in exact x).
Definition hci5_p8_A3_s8 := ltac:(let x := eval cbv beta iota delta [nth hci5_p8_acc] in (nth 8 hci5_p8_acc Sskip) in exact x).
Definition hci5_p8_A3_s9 := ltac:(let x := eval cbv beta iota delta [nth hci5_p8_acc] in (nth 9 hci5_p8_acc Sskip) in exact x).
Definition hci5_p8_A3_s10 := ltac:(let x := eval cbv beta iota delta [nth hci5_p8_acc] in (nth 10 hci5_p8_acc Sskip) in exact x).
Definition hci5_p8_A3_s11 := ltac:(let x := eval cbv beta iota delta [nth hci5_p8_acc] in (nth 11 hci5_p8_acc Sskip) in exact x).
Definition hci5_p8_A3_s12 := ltac:(let x := eval cbv beta iota delta [nth hci5_p8_acc] in (nth 12 hci5_p8_acc Sskip) in exact x).

Lemma hci5_p8_A3_eq :
  hci5_p8_A3 = Ssequence hci5_p8_A3_s5 (Ssequence hci5_p8_A3_s6 (Ssequence hci5_p8_A3_s7
    (Ssequence hci5_p8_A3_s8 (Ssequence hci5_p8_A3_s9 (Ssequence hci5_p8_A3_s10
    (Ssequence hci5_p8_A3_s11 hci5_p8_A3_s12)))))).
Proof. reflexivity. Qed.

(* the cut: seven CHECKs from Q1 back to Q1, the last one from Q1 to the final post *)
Lemma hci5_p8_A3_cut {Espec: OracleKind} {cs: compspecs} Delta Q1 R :
  semax Delta Q1 hci5_p8_A3_s5 (overridePost Q1 R) ->
  semax Delta Q1 hci5_p8_A3_s6 (overridePost Q1 R) ->
  semax Delta Q1 hci5_p8_A3_s7 (overridePost Q1 R) ->
  semax Delta Q1 hci5_p8_A3_s8 (overridePost Q1 R) ->
  semax Delta Q1 hci5_p8_A3_s9 (overridePost Q1 R) ->
  semax Delta Q1 hci5_p8_A3_s10 (overridePost Q1 R) ->
  semax Delta Q1 hci5_p8_A3_s11 (overridePost Q1 R) ->
  semax Delta Q1 hci5_p8_A3_s12 R ->
  semax Delta Q1 hci5_p8_A3 R.
Proof.
  intros H5 H6 H7 H8 H9 H10 H11 H12. rewrite hci5_p8_A3_eq.
  eapply semax_seq; [exact H5 |]. eapply semax_seq; [exact H6 |].
  eapply semax_seq; [exact H7 |]. eapply semax_seq; [exact H8 |].
  eapply semax_seq; [exact H9 |]. eapply semax_seq; [exact H10 |].
  eapply semax_seq; [exact H11 | exact H12].
Qed.
