(* the body of wg_validate_header_len (unit DataHeader)
   against dh4_spec.v, and the piece. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require WgNoise.units.DataHeader.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.data_header.dh4_spec.
Require WgNoise.data_header.code.

#[local] Existing Instance DataHeader.CS.
Local Open Scope Z_scope.

Module DC := WgNoise.data_header.code.

Definition dh4_Vprog : varspecs := QPvarspecs DataHeader.qp.
Definition dh4_Gprog : funspecs := dh4_imports DataHeader.CS ++ dh4_G.

Lemma dh4_ltu_c n c : 0 <= n <= Int64.max_unsigned -> 0 <= c <= Int64.max_unsigned ->
  Int64.ltu (Int64.repr n) (Int64.repr c) = (n <? c).
Proof.
  intros. unfold Int64.ltu. rewrite !Int64.unsigned_repr by lia.
  destruct (zlt n c), (n <? c) eqn:E; auto; [apply Z.ltb_ge in E | apply Z.ltb_lt in E]; lia.
Qed.

Lemma dh4_eq_c n c : 0 <= n <= Int64.max_unsigned -> 0 <= c <= Int64.max_unsigned ->
  Int64.eq (Int64.repr n) (Int64.repr c) = (n =? c).
Proof.
  intros. unfold Int64.eq. rewrite !Int64.unsigned_repr by lia.
  destruct (zeq n c), (n =? c) eqn:E; auto; [apply Z.eqb_neq in E | apply Z.eqb_eq in E]; lia.
Qed.

Lemma dh4_int_eq_c t c : 0 <= t <= Int.max_unsigned -> 0 <= c <= Int.max_unsigned ->
  Int.eq (Int.repr t) (Int.repr c) = (t =? c).
Proof.
  intros. unfold Int.eq. rewrite !Int.unsigned_repr by lia.
  destruct (zeq t c), (t =? c) eqn:E; auto; [apply Z.eqb_neq in E | apply Z.eqb_eq in E]; lia.
Qed.

Lemma dh4_ge n c : 0 <= n <= Int64.max_unsigned -> 0 <= c <= Int64.max_unsigned ->
  bool2val (Int64.cmpu Cge (Int64.repr n) (Int64.repr c)) = Vint (if c <=? n then Int.one else Int.zero).
Proof.
  intros. unfold Int64.cmpu. rewrite dh4_ltu_c by lia.
  destruct (n <? c) eqn:E1, (c <=? n) eqn:E2; try reflexivity;
    [apply Z.ltb_lt in E1; apply Z.leb_le in E2 | apply Z.ltb_ge in E1; apply Z.leb_gt in E2]; lia.
Qed.

Lemma dh4_eqv n c : 0 <= n <= Int64.max_unsigned -> 0 <= c <= Int64.max_unsigned ->
  bool2val (Int64.cmpu Ceq (Int64.repr n) (Int64.repr c)) = Vint (if n =? c then Int.one else Int.zero).
Proof.
  intros. unfold Int64.cmpu. rewrite dh4_eq_c by lia. destruct (n =? c); reflexivity.
Qed.

Ltac dh4_branch k ty ln t c :=
  forward_if (PROP () LOCAL (temp k (Vint (if andb (ty =? t) c then Int.one else Int.zero));
                             temp DC._type (Vint (Int.repr ty)); temp DC._len (Vlong (Int64.repr ln))) SEP ());
  [ forward; entailer!; first [rewrite dh4_ge by (simpl; rep_lia) | rewrite dh4_eqv by (simpl; rep_lia)]; reflexivity
  | forward; entailer!;
    match goal with H: ty <> t |- _ => rewrite (proj2 (Z.eqb_neq ty t) H); reflexivity end
  | ].

(* the return of a branch taken (b true), or b false for the rest *)
Ltac dh4_split :=
  forward_if;
  [ match goal with H: (if ?b then Int.one else _) <> Int.zero |- _ =>
      let E := fresh "E" in destruct b eqn:E; [| contradiction H; reflexivity] end;
    forward; entailer!; unfold dh4_len;
    repeat match goal with E: _ = _ |- _ => rewrite E end; reflexivity
  | match goal with H: (if ?b then Int.one else _) = Int.zero |- _ =>
      let E := fresh "E" in destruct b eqn:E; [discriminate |] end ].

Lemma dh4_body :
  semax_body dh4_Vprog dh4_Gprog DC.f_wg_validate_header_len wg_validate_header_len_spec.
Proof.
  start_function.
  forward_if.
  { forward. entailer!. unfold dh4_len. rewrite (proj2 (Z.ltb_lt len 4)) by lia. reflexivity. }
  assert (L4: (len <? 4) = false) by (apply Z.ltb_ge; lia).
  dh4_branch DC._t'1 type len 4 (32 <=? len). dh4_split.
  dh4_branch DC._t'2 type len 1 (len =? 148). dh4_split.
  dh4_branch DC._t'3 type len 2 (len =? 92). dh4_split.
  dh4_branch DC._t'4 type len 3 (len =? 64). dh4_split.
  forward. entailer!. unfold dh4_len.
  repeat match goal with E: _ = _ |- _ => rewrite E end; reflexivity.
Qed.

Theorem dh4_piece : piece_ok [u_data_header] dh4_imports dh4_G.
Proof.
  split; [repeat constructor; simpl; intuition |].
  repeat constructor. exists u_data_header. split; [left; reflexivity |].
  exists DC.f_wg_validate_header_len. split; [reflexivity | exact dh4_body].
Qed.
