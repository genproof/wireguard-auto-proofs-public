
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require WgNoise.units.DataHeader.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_dec3.
Require Import WgNoise.proof.harness.common4t.ht4_worlds.
Require Import WgNoise.proof.harness.common4t.ht4c_spec.
Require Import WgNoise.proof.harness.common4t.ht4r_spec.
Require Import WgNoise.proof.harness.common4t.ht4a_aead.
Require Import WgNoise.proof.data_header.dh4_spec.
Require Import WgNoise.proof.data_header.dh4_body.
Require Import WgNoise.proof.harness.transport_len.htl5_defs.
Require WgNoise.harness.x_transport_len.code.

#[local] Existing Instance W_transport_len.
Local Open Scope Z_scope.

Lemma htl5_segC_range t l : 0 <= dh4_len t l <= 148.
Proof. unfold dh4_len; repeat match goal with |- context [if ?b then _ else _] => destruct b end; lia. Qed.

Lemma htl5_segC_adm l : dh4_len 4 l <> 0 -> 32 <= l.
Proof.
  unfold dh4_len. destruct (l <? 4); [congruence|]. destruct (32 <=? l) eqn:E; simpl.
  - intros _. apply Z.leb_le in E. lia.
  - congruence.
Qed.

(* the value of dh4_len from the comparisons the branches established *)
Ltac htl5_segC_fin :=
  unfold dh4_len; destruct (_ <? 4) eqn:?;
  [match goal with E: (_ <? 4) = true |- _ => apply Z.ltb_lt in E; lia end |];
  repeat match goal with E: ?b = true |- context [?b] => rewrite E | E: ?b = false |- context [?b] => rewrite E end;
  reflexivity.

(* if (t) expect = c; else ...: the then-branch is closed, the else-branch remains with b = false *)
Ltac htl5_segC_then :=
  forward_if;
  [ match goal with H: (if ?b then Int.one else _) <> Int.zero |- _ =>
      let E := fresh "E" in destruct b eqn:E; [| contradiction H; reflexivity] end;
    forward; entailer!; try simpl sizeof; htl5_segC_fin
  | match goal with H: (if ?b then Int.one else _) = Int.zero |- _ =>
      let E := fresh "E" in destruct b eqn:E; [contradiction (Int.one_not_zero H) |] end ].

Ltac htl5_segC_branch k ty t c :=
  forward_if (temp k (Vint (if andb (ty =? t) c then Int.one else Int.zero)));
  [ forward; entailer!; try simpl sizeof; first [rewrite dh4_ge by rep_lia | rewrite dh4_eqv by rep_lia]; reflexivity
  | forward; entailer!;
    match goal with H: ty <> t |- _ => rewrite (proj2 (Z.eqb_neq ty t) H); reflexivity end
  | ].

Lemma htl5_segC_ok {Espec: OracleKind} gv vk FR :
  semax htl5_Delta (htl5_PB gv vk FR) htl5_segC (overridePost (htl5_PC gv vk FR) (htl5_R gv)).
Proof.
  unfold htl5_PB. Intros key nonce tot type pkt pk.
  unfold htl5_Delta, htl5_segC, htl5_R. apply htl5_post_canon.
  simplify_func_tycontext. abbreviate_semax.
  match goal with H: htl5_ranges _ _ _ |- _ => pose proof H as Hr; destruct H as (Hk & Hno & Htot) end.
  unfold htl5_lv. simpl app.
  forward_call (type, tot). unfold htl5_buf. Intros.
  forward_if (temp TLC._expect (Vlong (Int64.repr (dh4_len type tot)))).
  { forward. entailer!. unfold dh4_len. destruct (_ <? 4) eqn:E; [reflexivity | apply Z.ltb_ge in E; lia]. }
  { htl5_segC_branch TLC._t'14 type 4 (32 <=? tot). htl5_segC_then.
    htl5_segC_branch TLC._t'13 type 1 (tot =? 148). htl5_segC_then.
    htl5_segC_branch TLC._t'12 type 2 (tot =? 92). htl5_segC_then.
    htl5_segC_branch TLC._t'11 type 3 (tot =? 64). htl5_segC_then.
    forward. entailer!. htl5_segC_fin. }
  match goal with |- semax _ ?P _ _ => forward_loop P break: P end.
  { apply ENTAIL_refl. }
  { match goal with |- semax _ ?P _ _ => forward_if P end.
    - match goal with Hc: Int.repr (Z.b2z (Int64.eq _ _)) = Int.zero |- _ =>
        rewrite Int64.eq_true in Hc; discriminate Hc end.
    - forward. entailer!.
    - forward. entailer!. }
  pose proof (htl5_segC_range type tot) as Hrg.
  forward_if (temp TLC._t'15 (Vint (if andb (type =? 4) (negb (dh4_len type tot =? 0)) then Int.zero else Int.one))).
  { forward. entailer!. rewrite (proj2 (Z.eqb_neq type 4)) by auto. reflexivity. }
  { forward. entailer!. rewrite dh4_eqv by rep_lia. simpl. destruct (_ =? 0); reflexivity. }
  forward_if.
  { assert_PROP (isptr pkt) as Pp by entailer!.
    forward_call (tarray tuchar tot, pkt, gv).
    { rewrite if_false by (destruct pkt; try contradiction; discriminate).
      sep_apply (data_at_data_at_ Ews (tarray tuchar tot) (map Vubyte pk) pkt). cancel. }
    forward.
    sep_apply (data_at_data_at_ Tsh (tarray tuchar 32) (map Vubyte key) vk).
    cancel. }
  match goal with H: (if ?b then _ else Int.one) = Int.zero |- _ =>
    let E := fresh "E" in destruct b eqn:E; [| contradiction (Int.one_not_zero H)] end.
  apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.eqb_eq in E1. subst type.
  apply negb_true_iff, Z.eqb_neq, htl5_segC_adm in E2.
  forward. unfold htl5_PC, htl5_buf, htl5_lv. Exists key nonce tot pkt pk. simpl app. entailer!.
Qed.