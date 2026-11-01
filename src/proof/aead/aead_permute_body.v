(* Body proofs of chacha_permute. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require WgNoise.chacha_block.code.
Require Import WgNoise.proof.libc.spec.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.aead.aead_spec.
Require Import WgNoise.proof.aead.aead_cce.
Require Import WgNoise.proof.aead.aead_bytes.
Require Import WgNoise.proof.aead.aead_model.
Require Import WgNoise.proof.aead.aead_permute_model.

Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* the statements of the loop body                                         *)
(* ---------------------------------------------------------------------- *)

Definition xel (k: Z) : expr :=
  Ederef (Ebinop Oadd (Etempvar WgNoise.chacha_block.code._x (tptr tuint)) (Econst_int (Int.repr k) tint)
    (tptr tuint)) tuint.
Definition s_add (t1 t2: ident) (a b: Z) : statement :=
  Ssequence (Sset t1 (xel a)) (Ssequence (Sset t2 (xel b))
    (Sassign (xel a) (Ebinop Oadd (Etempvar t1 tuint) (Etempvar t2 tuint) tuint))).
Definition s_rol (t1 t2 t3: ident) (d a s: Z) : statement :=
  Ssequence (Ssequence (Sset t1 (xel d)) (Ssequence (Sset t2 (xel a))
    (Scall (Some t3) (Evar _rol32 (Tfunction (tuint :: tuint :: nil) tuint cc_default))
       ((Ebinop Oxor (Etempvar t1 tuint) (Etempvar t2 tuint) tuint) :: (Econst_int (Int.repr s) tint) :: nil))))
  (Sassign (xel d) (Etempvar t3 tuint)).

Definition perm_Vprog : varspecs := QPvarspecs ChachaBlock.qp.
Definition perm_Gprog : funspecs := aead_imports_def ChachaBlock.CS ++ aead_G_def.
Definition perm_Delta : tycontext :=
  func_tycontext WgNoise.chacha_block.code.f_chacha_permute perm_Vprog perm_Gprog nil.

Definition perm_P (sh: share) (x vi vn: val) (l: list int) : environ -> mpred :=
  PROP () LOCAL (temp WgNoise.chacha_block.code._x x; temp WgNoise.chacha_block.code._i vi;
                 temp WgNoise.chacha_block.code._nrounds vn)
  SEP (@data_at ChachaBlock.CS sh (tarray tuint 16) (map Vint l) x).

Section Steps.
Context {Espec: OracleKind}.
#[local] Existing Instance ChachaBlock.CS.

Ltac step_start :=
  unfold perm_Delta, perm_P, s_add, s_rol, xel; simplify_func_tycontext; abbreviate_semax.
Ltac step_add_tac :=
  step_start; forward; forward; forward; entailer!; unfold kadd; rewrite upd_Znth_map; auto.
Ltac step_rol_tac w s :=
  step_start; forward; forward; forward_call (w, s); forward;
  entailer!; unfold krol; rewrite upd_Znth_map; auto.

Definition perm_body : statement :=
  Ssequence (s_add WgNoise.chacha_block.code._t'160 WgNoise.chacha_block.code._t'161 0 4)
  (Ssequence (s_rol WgNoise.chacha_block.code._t'158 WgNoise.chacha_block.code._t'159 WgNoise.chacha_block.code._t'2 12 0 16)
  (Ssequence (s_add WgNoise.chacha_block.code._t'156 WgNoise.chacha_block.code._t'157 1 5)
  (Ssequence (s_rol WgNoise.chacha_block.code._t'154 WgNoise.chacha_block.code._t'155 WgNoise.chacha_block.code._t'3 13 1 16)
  (Ssequence (s_add WgNoise.chacha_block.code._t'152 WgNoise.chacha_block.code._t'153 2 6)
  (Ssequence (s_rol WgNoise.chacha_block.code._t'150 WgNoise.chacha_block.code._t'151 WgNoise.chacha_block.code._t'4 14 2 16)
  (Ssequence (s_add WgNoise.chacha_block.code._t'148 WgNoise.chacha_block.code._t'149 3 7)
  (Ssequence (s_rol WgNoise.chacha_block.code._t'146 WgNoise.chacha_block.code._t'147 WgNoise.chacha_block.code._t'5 15 3 16)
  (Ssequence (s_add WgNoise.chacha_block.code._t'144 WgNoise.chacha_block.code._t'145 8 12)
  (Ssequence (s_rol WgNoise.chacha_block.code._t'142 WgNoise.chacha_block.code._t'143 WgNoise.chacha_block.code._t'6 4 8 12)
  (Ssequence (s_add WgNoise.chacha_block.code._t'140 WgNoise.chacha_block.code._t'141 9 13)
  (Ssequence (s_rol WgNoise.chacha_block.code._t'138 WgNoise.chacha_block.code._t'139 WgNoise.chacha_block.code._t'7 5 9 12)
  (Ssequence (s_add WgNoise.chacha_block.code._t'136 WgNoise.chacha_block.code._t'137 10 14)
  (Ssequence (s_rol WgNoise.chacha_block.code._t'134 WgNoise.chacha_block.code._t'135 WgNoise.chacha_block.code._t'8 6 10 12)
  (Ssequence (s_add WgNoise.chacha_block.code._t'132 WgNoise.chacha_block.code._t'133 11 15)
  (Ssequence (s_rol WgNoise.chacha_block.code._t'130 WgNoise.chacha_block.code._t'131 WgNoise.chacha_block.code._t'9 7 11 12)
  (Ssequence (s_add WgNoise.chacha_block.code._t'128 WgNoise.chacha_block.code._t'129 0 4)
  (Ssequence (s_rol WgNoise.chacha_block.code._t'126 WgNoise.chacha_block.code._t'127 WgNoise.chacha_block.code._t'10 12 0 8)
  (Ssequence (s_add WgNoise.chacha_block.code._t'124 WgNoise.chacha_block.code._t'125 1 5)
  (Ssequence (s_rol WgNoise.chacha_block.code._t'122 WgNoise.chacha_block.code._t'123 WgNoise.chacha_block.code._t'11 13 1 8)
  (Ssequence (s_add WgNoise.chacha_block.code._t'120 WgNoise.chacha_block.code._t'121 2 6)
  (Ssequence (s_rol WgNoise.chacha_block.code._t'118 WgNoise.chacha_block.code._t'119 WgNoise.chacha_block.code._t'12 14 2 8)
  (Ssequence (s_add WgNoise.chacha_block.code._t'116 WgNoise.chacha_block.code._t'117 3 7)
  (Ssequence (s_rol WgNoise.chacha_block.code._t'114 WgNoise.chacha_block.code._t'115 WgNoise.chacha_block.code._t'13 15 3 8)
  (Ssequence (s_add WgNoise.chacha_block.code._t'112 WgNoise.chacha_block.code._t'113 8 12)
  (Ssequence (s_rol WgNoise.chacha_block.code._t'110 WgNoise.chacha_block.code._t'111 WgNoise.chacha_block.code._t'14 4 8 7)
  (Ssequence (s_add WgNoise.chacha_block.code._t'108 WgNoise.chacha_block.code._t'109 9 13)
  (Ssequence (s_rol WgNoise.chacha_block.code._t'106 WgNoise.chacha_block.code._t'107 WgNoise.chacha_block.code._t'15 5 9 7)
  (Ssequence (s_add WgNoise.chacha_block.code._t'104 WgNoise.chacha_block.code._t'105 10 14)
  (Ssequence (s_rol WgNoise.chacha_block.code._t'102 WgNoise.chacha_block.code._t'103 WgNoise.chacha_block.code._t'16 6 10 7)
  (Ssequence (s_add WgNoise.chacha_block.code._t'100 WgNoise.chacha_block.code._t'101 11 15)
  (Ssequence (s_rol WgNoise.chacha_block.code._t'98 WgNoise.chacha_block.code._t'99 WgNoise.chacha_block.code._t'17 7 11 7)
  (Ssequence (s_add WgNoise.chacha_block.code._t'96 WgNoise.chacha_block.code._t'97 0 5)
  (Ssequence (s_rol WgNoise.chacha_block.code._t'94 WgNoise.chacha_block.code._t'95 WgNoise.chacha_block.code._t'18 15 0 16)
  (Ssequence (s_add WgNoise.chacha_block.code._t'92 WgNoise.chacha_block.code._t'93 1 6)
  (Ssequence (s_rol WgNoise.chacha_block.code._t'90 WgNoise.chacha_block.code._t'91 WgNoise.chacha_block.code._t'19 12 1 16)
  (Ssequence (s_add WgNoise.chacha_block.code._t'88 WgNoise.chacha_block.code._t'89 2 7)
  (Ssequence (s_rol WgNoise.chacha_block.code._t'86 WgNoise.chacha_block.code._t'87 WgNoise.chacha_block.code._t'20 13 2 16)
  (Ssequence (s_add WgNoise.chacha_block.code._t'84 WgNoise.chacha_block.code._t'85 3 4)
  (Ssequence (s_rol WgNoise.chacha_block.code._t'82 WgNoise.chacha_block.code._t'83 WgNoise.chacha_block.code._t'21 14 3 16)
  (Ssequence (s_add WgNoise.chacha_block.code._t'80 WgNoise.chacha_block.code._t'81 10 15)
  (Ssequence (s_rol WgNoise.chacha_block.code._t'78 WgNoise.chacha_block.code._t'79 WgNoise.chacha_block.code._t'22 5 10 12)
  (Ssequence (s_add WgNoise.chacha_block.code._t'76 WgNoise.chacha_block.code._t'77 11 12)
  (Ssequence (s_rol WgNoise.chacha_block.code._t'74 WgNoise.chacha_block.code._t'75 WgNoise.chacha_block.code._t'23 6 11 12)
  (Ssequence (s_add WgNoise.chacha_block.code._t'72 WgNoise.chacha_block.code._t'73 8 13)
  (Ssequence (s_rol WgNoise.chacha_block.code._t'70 WgNoise.chacha_block.code._t'71 WgNoise.chacha_block.code._t'24 7 8 12)
  (Ssequence (s_add WgNoise.chacha_block.code._t'68 WgNoise.chacha_block.code._t'69 9 14)
  (Ssequence (s_rol WgNoise.chacha_block.code._t'66 WgNoise.chacha_block.code._t'67 WgNoise.chacha_block.code._t'25 4 9 12)
  (Ssequence (s_add WgNoise.chacha_block.code._t'64 WgNoise.chacha_block.code._t'65 0 5)
  (Ssequence (s_rol WgNoise.chacha_block.code._t'62 WgNoise.chacha_block.code._t'63 WgNoise.chacha_block.code._t'26 15 0 8)
  (Ssequence (s_add WgNoise.chacha_block.code._t'60 WgNoise.chacha_block.code._t'61 1 6)
  (Ssequence (s_rol WgNoise.chacha_block.code._t'58 WgNoise.chacha_block.code._t'59 WgNoise.chacha_block.code._t'27 12 1 8)
  (Ssequence (s_add WgNoise.chacha_block.code._t'56 WgNoise.chacha_block.code._t'57 2 7)
  (Ssequence (s_rol WgNoise.chacha_block.code._t'54 WgNoise.chacha_block.code._t'55 WgNoise.chacha_block.code._t'28 13 2 8)
  (Ssequence (s_add WgNoise.chacha_block.code._t'52 WgNoise.chacha_block.code._t'53 3 4)
  (Ssequence (s_rol WgNoise.chacha_block.code._t'50 WgNoise.chacha_block.code._t'51 WgNoise.chacha_block.code._t'29 14 3 8)
  (Ssequence (s_add WgNoise.chacha_block.code._t'48 WgNoise.chacha_block.code._t'49 10 15)
  (Ssequence (s_rol WgNoise.chacha_block.code._t'46 WgNoise.chacha_block.code._t'47 WgNoise.chacha_block.code._t'30 5 10 7)
  (Ssequence (s_add WgNoise.chacha_block.code._t'44 WgNoise.chacha_block.code._t'45 11 12)
  (Ssequence (s_rol WgNoise.chacha_block.code._t'42 WgNoise.chacha_block.code._t'43 WgNoise.chacha_block.code._t'31 6 11 7)
  (Ssequence (s_add WgNoise.chacha_block.code._t'40 WgNoise.chacha_block.code._t'41 8 13)
  (Ssequence (s_rol WgNoise.chacha_block.code._t'38 WgNoise.chacha_block.code._t'39 WgNoise.chacha_block.code._t'32 7 8 7)
  (Ssequence (s_add WgNoise.chacha_block.code._t'36 WgNoise.chacha_block.code._t'37 9 14)
  (s_rol WgNoise.chacha_block.code._t'34 WgNoise.chacha_block.code._t'35 WgNoise.chacha_block.code._t'33 4 9 7))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Lemma perm_step0 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_add WgNoise.chacha_block.code._t'160 WgNoise.chacha_block.code._t'161 0 4)
    (normal_ret_assert (perm_P sh x vi vn (kadd l 0 4))).
Proof. intros sh x vi vn l Hsh Hl. step_add_tac. Qed.

Lemma perm_step1 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_rol WgNoise.chacha_block.code._t'158 WgNoise.chacha_block.code._t'159 WgNoise.chacha_block.code._t'2 12 0 16)
    (normal_ret_assert (perm_P sh x vi vn (krol l 12 0 16))).
Proof. intros sh x vi vn l Hsh Hl. step_rol_tac (Int.xor (Znth 12 l) (Znth 0 l)) 16. Qed.

Lemma perm_step2 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_add WgNoise.chacha_block.code._t'156 WgNoise.chacha_block.code._t'157 1 5)
    (normal_ret_assert (perm_P sh x vi vn (kadd l 1 5))).
Proof. intros sh x vi vn l Hsh Hl. step_add_tac. Qed.

Lemma perm_step3 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_rol WgNoise.chacha_block.code._t'154 WgNoise.chacha_block.code._t'155 WgNoise.chacha_block.code._t'3 13 1 16)
    (normal_ret_assert (perm_P sh x vi vn (krol l 13 1 16))).
Proof. intros sh x vi vn l Hsh Hl. step_rol_tac (Int.xor (Znth 13 l) (Znth 1 l)) 16. Qed.

Lemma perm_step4 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_add WgNoise.chacha_block.code._t'152 WgNoise.chacha_block.code._t'153 2 6)
    (normal_ret_assert (perm_P sh x vi vn (kadd l 2 6))).
Proof. intros sh x vi vn l Hsh Hl. step_add_tac. Qed.

Lemma perm_step5 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_rol WgNoise.chacha_block.code._t'150 WgNoise.chacha_block.code._t'151 WgNoise.chacha_block.code._t'4 14 2 16)
    (normal_ret_assert (perm_P sh x vi vn (krol l 14 2 16))).
Proof. intros sh x vi vn l Hsh Hl. step_rol_tac (Int.xor (Znth 14 l) (Znth 2 l)) 16. Qed.

Lemma perm_step6 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_add WgNoise.chacha_block.code._t'148 WgNoise.chacha_block.code._t'149 3 7)
    (normal_ret_assert (perm_P sh x vi vn (kadd l 3 7))).
Proof. intros sh x vi vn l Hsh Hl. step_add_tac. Qed.

Lemma perm_step7 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_rol WgNoise.chacha_block.code._t'146 WgNoise.chacha_block.code._t'147 WgNoise.chacha_block.code._t'5 15 3 16)
    (normal_ret_assert (perm_P sh x vi vn (krol l 15 3 16))).
Proof. intros sh x vi vn l Hsh Hl. step_rol_tac (Int.xor (Znth 15 l) (Znth 3 l)) 16. Qed.

Lemma perm_step8 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_add WgNoise.chacha_block.code._t'144 WgNoise.chacha_block.code._t'145 8 12)
    (normal_ret_assert (perm_P sh x vi vn (kadd l 8 12))).
Proof. intros sh x vi vn l Hsh Hl. step_add_tac. Qed.

Lemma perm_step9 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_rol WgNoise.chacha_block.code._t'142 WgNoise.chacha_block.code._t'143 WgNoise.chacha_block.code._t'6 4 8 12)
    (normal_ret_assert (perm_P sh x vi vn (krol l 4 8 12))).
Proof. intros sh x vi vn l Hsh Hl. step_rol_tac (Int.xor (Znth 4 l) (Znth 8 l)) 12. Qed.

Lemma perm_step10 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_add WgNoise.chacha_block.code._t'140 WgNoise.chacha_block.code._t'141 9 13)
    (normal_ret_assert (perm_P sh x vi vn (kadd l 9 13))).
Proof. intros sh x vi vn l Hsh Hl. step_add_tac. Qed.

Lemma perm_step11 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_rol WgNoise.chacha_block.code._t'138 WgNoise.chacha_block.code._t'139 WgNoise.chacha_block.code._t'7 5 9 12)
    (normal_ret_assert (perm_P sh x vi vn (krol l 5 9 12))).
Proof. intros sh x vi vn l Hsh Hl. step_rol_tac (Int.xor (Znth 5 l) (Znth 9 l)) 12. Qed.

Lemma perm_step12 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_add WgNoise.chacha_block.code._t'136 WgNoise.chacha_block.code._t'137 10 14)
    (normal_ret_assert (perm_P sh x vi vn (kadd l 10 14))).
Proof. intros sh x vi vn l Hsh Hl. step_add_tac. Qed.

Lemma perm_step13 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_rol WgNoise.chacha_block.code._t'134 WgNoise.chacha_block.code._t'135 WgNoise.chacha_block.code._t'8 6 10 12)
    (normal_ret_assert (perm_P sh x vi vn (krol l 6 10 12))).
Proof. intros sh x vi vn l Hsh Hl. step_rol_tac (Int.xor (Znth 6 l) (Znth 10 l)) 12. Qed.

Lemma perm_step14 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_add WgNoise.chacha_block.code._t'132 WgNoise.chacha_block.code._t'133 11 15)
    (normal_ret_assert (perm_P sh x vi vn (kadd l 11 15))).
Proof. intros sh x vi vn l Hsh Hl. step_add_tac. Qed.

Lemma perm_step15 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_rol WgNoise.chacha_block.code._t'130 WgNoise.chacha_block.code._t'131 WgNoise.chacha_block.code._t'9 7 11 12)
    (normal_ret_assert (perm_P sh x vi vn (krol l 7 11 12))).
Proof. intros sh x vi vn l Hsh Hl. step_rol_tac (Int.xor (Znth 7 l) (Znth 11 l)) 12. Qed.

Lemma perm_step16 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_add WgNoise.chacha_block.code._t'128 WgNoise.chacha_block.code._t'129 0 4)
    (normal_ret_assert (perm_P sh x vi vn (kadd l 0 4))).
Proof. intros sh x vi vn l Hsh Hl. step_add_tac. Qed.

Lemma perm_step17 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_rol WgNoise.chacha_block.code._t'126 WgNoise.chacha_block.code._t'127 WgNoise.chacha_block.code._t'10 12 0 8)
    (normal_ret_assert (perm_P sh x vi vn (krol l 12 0 8))).
Proof. intros sh x vi vn l Hsh Hl. step_rol_tac (Int.xor (Znth 12 l) (Znth 0 l)) 8. Qed.

Lemma perm_step18 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_add WgNoise.chacha_block.code._t'124 WgNoise.chacha_block.code._t'125 1 5)
    (normal_ret_assert (perm_P sh x vi vn (kadd l 1 5))).
Proof. intros sh x vi vn l Hsh Hl. step_add_tac. Qed.

Lemma perm_step19 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_rol WgNoise.chacha_block.code._t'122 WgNoise.chacha_block.code._t'123 WgNoise.chacha_block.code._t'11 13 1 8)
    (normal_ret_assert (perm_P sh x vi vn (krol l 13 1 8))).
Proof. intros sh x vi vn l Hsh Hl. step_rol_tac (Int.xor (Znth 13 l) (Znth 1 l)) 8. Qed.

Lemma perm_step20 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_add WgNoise.chacha_block.code._t'120 WgNoise.chacha_block.code._t'121 2 6)
    (normal_ret_assert (perm_P sh x vi vn (kadd l 2 6))).
Proof. intros sh x vi vn l Hsh Hl. step_add_tac. Qed.

Lemma perm_step21 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_rol WgNoise.chacha_block.code._t'118 WgNoise.chacha_block.code._t'119 WgNoise.chacha_block.code._t'12 14 2 8)
    (normal_ret_assert (perm_P sh x vi vn (krol l 14 2 8))).
Proof. intros sh x vi vn l Hsh Hl. step_rol_tac (Int.xor (Znth 14 l) (Znth 2 l)) 8. Qed.

Lemma perm_step22 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_add WgNoise.chacha_block.code._t'116 WgNoise.chacha_block.code._t'117 3 7)
    (normal_ret_assert (perm_P sh x vi vn (kadd l 3 7))).
Proof. intros sh x vi vn l Hsh Hl. step_add_tac. Qed.

Lemma perm_step23 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_rol WgNoise.chacha_block.code._t'114 WgNoise.chacha_block.code._t'115 WgNoise.chacha_block.code._t'13 15 3 8)
    (normal_ret_assert (perm_P sh x vi vn (krol l 15 3 8))).
Proof. intros sh x vi vn l Hsh Hl. step_rol_tac (Int.xor (Znth 15 l) (Znth 3 l)) 8. Qed.

Lemma perm_step24 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_add WgNoise.chacha_block.code._t'112 WgNoise.chacha_block.code._t'113 8 12)
    (normal_ret_assert (perm_P sh x vi vn (kadd l 8 12))).
Proof. intros sh x vi vn l Hsh Hl. step_add_tac. Qed.

Lemma perm_step25 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_rol WgNoise.chacha_block.code._t'110 WgNoise.chacha_block.code._t'111 WgNoise.chacha_block.code._t'14 4 8 7)
    (normal_ret_assert (perm_P sh x vi vn (krol l 4 8 7))).
Proof. intros sh x vi vn l Hsh Hl. step_rol_tac (Int.xor (Znth 4 l) (Znth 8 l)) 7. Qed.

Lemma perm_step26 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_add WgNoise.chacha_block.code._t'108 WgNoise.chacha_block.code._t'109 9 13)
    (normal_ret_assert (perm_P sh x vi vn (kadd l 9 13))).
Proof. intros sh x vi vn l Hsh Hl. step_add_tac. Qed.

Lemma perm_step27 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_rol WgNoise.chacha_block.code._t'106 WgNoise.chacha_block.code._t'107 WgNoise.chacha_block.code._t'15 5 9 7)
    (normal_ret_assert (perm_P sh x vi vn (krol l 5 9 7))).
Proof. intros sh x vi vn l Hsh Hl. step_rol_tac (Int.xor (Znth 5 l) (Znth 9 l)) 7. Qed.

Lemma perm_step28 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_add WgNoise.chacha_block.code._t'104 WgNoise.chacha_block.code._t'105 10 14)
    (normal_ret_assert (perm_P sh x vi vn (kadd l 10 14))).
Proof. intros sh x vi vn l Hsh Hl. step_add_tac. Qed.

Lemma perm_step29 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_rol WgNoise.chacha_block.code._t'102 WgNoise.chacha_block.code._t'103 WgNoise.chacha_block.code._t'16 6 10 7)
    (normal_ret_assert (perm_P sh x vi vn (krol l 6 10 7))).
Proof. intros sh x vi vn l Hsh Hl. step_rol_tac (Int.xor (Znth 6 l) (Znth 10 l)) 7. Qed.

Lemma perm_step30 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_add WgNoise.chacha_block.code._t'100 WgNoise.chacha_block.code._t'101 11 15)
    (normal_ret_assert (perm_P sh x vi vn (kadd l 11 15))).
Proof. intros sh x vi vn l Hsh Hl. step_add_tac. Qed.

Lemma perm_step31 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_rol WgNoise.chacha_block.code._t'98 WgNoise.chacha_block.code._t'99 WgNoise.chacha_block.code._t'17 7 11 7)
    (normal_ret_assert (perm_P sh x vi vn (krol l 7 11 7))).
Proof. intros sh x vi vn l Hsh Hl. step_rol_tac (Int.xor (Znth 7 l) (Znth 11 l)) 7. Qed.

Lemma perm_step32 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_add WgNoise.chacha_block.code._t'96 WgNoise.chacha_block.code._t'97 0 5)
    (normal_ret_assert (perm_P sh x vi vn (kadd l 0 5))).
Proof. intros sh x vi vn l Hsh Hl. step_add_tac. Qed.

Lemma perm_step33 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_rol WgNoise.chacha_block.code._t'94 WgNoise.chacha_block.code._t'95 WgNoise.chacha_block.code._t'18 15 0 16)
    (normal_ret_assert (perm_P sh x vi vn (krol l 15 0 16))).
Proof. intros sh x vi vn l Hsh Hl. step_rol_tac (Int.xor (Znth 15 l) (Znth 0 l)) 16. Qed.

Lemma perm_step34 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_add WgNoise.chacha_block.code._t'92 WgNoise.chacha_block.code._t'93 1 6)
    (normal_ret_assert (perm_P sh x vi vn (kadd l 1 6))).
Proof. intros sh x vi vn l Hsh Hl. step_add_tac. Qed.

Lemma perm_step35 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_rol WgNoise.chacha_block.code._t'90 WgNoise.chacha_block.code._t'91 WgNoise.chacha_block.code._t'19 12 1 16)
    (normal_ret_assert (perm_P sh x vi vn (krol l 12 1 16))).
Proof. intros sh x vi vn l Hsh Hl. step_rol_tac (Int.xor (Znth 12 l) (Znth 1 l)) 16. Qed.

Lemma perm_step36 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_add WgNoise.chacha_block.code._t'88 WgNoise.chacha_block.code._t'89 2 7)
    (normal_ret_assert (perm_P sh x vi vn (kadd l 2 7))).
Proof. intros sh x vi vn l Hsh Hl. step_add_tac. Qed.

Lemma perm_step37 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_rol WgNoise.chacha_block.code._t'86 WgNoise.chacha_block.code._t'87 WgNoise.chacha_block.code._t'20 13 2 16)
    (normal_ret_assert (perm_P sh x vi vn (krol l 13 2 16))).
Proof. intros sh x vi vn l Hsh Hl. step_rol_tac (Int.xor (Znth 13 l) (Znth 2 l)) 16. Qed.

Lemma perm_step38 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_add WgNoise.chacha_block.code._t'84 WgNoise.chacha_block.code._t'85 3 4)
    (normal_ret_assert (perm_P sh x vi vn (kadd l 3 4))).
Proof. intros sh x vi vn l Hsh Hl. step_add_tac. Qed.

Lemma perm_step39 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_rol WgNoise.chacha_block.code._t'82 WgNoise.chacha_block.code._t'83 WgNoise.chacha_block.code._t'21 14 3 16)
    (normal_ret_assert (perm_P sh x vi vn (krol l 14 3 16))).
Proof. intros sh x vi vn l Hsh Hl. step_rol_tac (Int.xor (Znth 14 l) (Znth 3 l)) 16. Qed.

Lemma perm_step40 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_add WgNoise.chacha_block.code._t'80 WgNoise.chacha_block.code._t'81 10 15)
    (normal_ret_assert (perm_P sh x vi vn (kadd l 10 15))).
Proof. intros sh x vi vn l Hsh Hl. step_add_tac. Qed.

Lemma perm_step41 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_rol WgNoise.chacha_block.code._t'78 WgNoise.chacha_block.code._t'79 WgNoise.chacha_block.code._t'22 5 10 12)
    (normal_ret_assert (perm_P sh x vi vn (krol l 5 10 12))).
Proof. intros sh x vi vn l Hsh Hl. step_rol_tac (Int.xor (Znth 5 l) (Znth 10 l)) 12. Qed.

Lemma perm_step42 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_add WgNoise.chacha_block.code._t'76 WgNoise.chacha_block.code._t'77 11 12)
    (normal_ret_assert (perm_P sh x vi vn (kadd l 11 12))).
Proof. intros sh x vi vn l Hsh Hl. step_add_tac. Qed.

Lemma perm_step43 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_rol WgNoise.chacha_block.code._t'74 WgNoise.chacha_block.code._t'75 WgNoise.chacha_block.code._t'23 6 11 12)
    (normal_ret_assert (perm_P sh x vi vn (krol l 6 11 12))).
Proof. intros sh x vi vn l Hsh Hl. step_rol_tac (Int.xor (Znth 6 l) (Znth 11 l)) 12. Qed.

Lemma perm_step44 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_add WgNoise.chacha_block.code._t'72 WgNoise.chacha_block.code._t'73 8 13)
    (normal_ret_assert (perm_P sh x vi vn (kadd l 8 13))).
Proof. intros sh x vi vn l Hsh Hl. step_add_tac. Qed.

Lemma perm_step45 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_rol WgNoise.chacha_block.code._t'70 WgNoise.chacha_block.code._t'71 WgNoise.chacha_block.code._t'24 7 8 12)
    (normal_ret_assert (perm_P sh x vi vn (krol l 7 8 12))).
Proof. intros sh x vi vn l Hsh Hl. step_rol_tac (Int.xor (Znth 7 l) (Znth 8 l)) 12. Qed.

Lemma perm_step46 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_add WgNoise.chacha_block.code._t'68 WgNoise.chacha_block.code._t'69 9 14)
    (normal_ret_assert (perm_P sh x vi vn (kadd l 9 14))).
Proof. intros sh x vi vn l Hsh Hl. step_add_tac. Qed.

Lemma perm_step47 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_rol WgNoise.chacha_block.code._t'66 WgNoise.chacha_block.code._t'67 WgNoise.chacha_block.code._t'25 4 9 12)
    (normal_ret_assert (perm_P sh x vi vn (krol l 4 9 12))).
Proof. intros sh x vi vn l Hsh Hl. step_rol_tac (Int.xor (Znth 4 l) (Znth 9 l)) 12. Qed.

Lemma perm_step48 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_add WgNoise.chacha_block.code._t'64 WgNoise.chacha_block.code._t'65 0 5)
    (normal_ret_assert (perm_P sh x vi vn (kadd l 0 5))).
Proof. intros sh x vi vn l Hsh Hl. step_add_tac. Qed.

Lemma perm_step49 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_rol WgNoise.chacha_block.code._t'62 WgNoise.chacha_block.code._t'63 WgNoise.chacha_block.code._t'26 15 0 8)
    (normal_ret_assert (perm_P sh x vi vn (krol l 15 0 8))).
Proof. intros sh x vi vn l Hsh Hl. step_rol_tac (Int.xor (Znth 15 l) (Znth 0 l)) 8. Qed.

Lemma perm_step50 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_add WgNoise.chacha_block.code._t'60 WgNoise.chacha_block.code._t'61 1 6)
    (normal_ret_assert (perm_P sh x vi vn (kadd l 1 6))).
Proof. intros sh x vi vn l Hsh Hl. step_add_tac. Qed.

Lemma perm_step51 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_rol WgNoise.chacha_block.code._t'58 WgNoise.chacha_block.code._t'59 WgNoise.chacha_block.code._t'27 12 1 8)
    (normal_ret_assert (perm_P sh x vi vn (krol l 12 1 8))).
Proof. intros sh x vi vn l Hsh Hl. step_rol_tac (Int.xor (Znth 12 l) (Znth 1 l)) 8. Qed.

Lemma perm_step52 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_add WgNoise.chacha_block.code._t'56 WgNoise.chacha_block.code._t'57 2 7)
    (normal_ret_assert (perm_P sh x vi vn (kadd l 2 7))).
Proof. intros sh x vi vn l Hsh Hl. step_add_tac. Qed.

Lemma perm_step53 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_rol WgNoise.chacha_block.code._t'54 WgNoise.chacha_block.code._t'55 WgNoise.chacha_block.code._t'28 13 2 8)
    (normal_ret_assert (perm_P sh x vi vn (krol l 13 2 8))).
Proof. intros sh x vi vn l Hsh Hl. step_rol_tac (Int.xor (Znth 13 l) (Znth 2 l)) 8. Qed.

Lemma perm_step54 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_add WgNoise.chacha_block.code._t'52 WgNoise.chacha_block.code._t'53 3 4)
    (normal_ret_assert (perm_P sh x vi vn (kadd l 3 4))).
Proof. intros sh x vi vn l Hsh Hl. step_add_tac. Qed.

Lemma perm_step55 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_rol WgNoise.chacha_block.code._t'50 WgNoise.chacha_block.code._t'51 WgNoise.chacha_block.code._t'29 14 3 8)
    (normal_ret_assert (perm_P sh x vi vn (krol l 14 3 8))).
Proof. intros sh x vi vn l Hsh Hl. step_rol_tac (Int.xor (Znth 14 l) (Znth 3 l)) 8. Qed.

Lemma perm_step56 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_add WgNoise.chacha_block.code._t'48 WgNoise.chacha_block.code._t'49 10 15)
    (normal_ret_assert (perm_P sh x vi vn (kadd l 10 15))).
Proof. intros sh x vi vn l Hsh Hl. step_add_tac. Qed.

Lemma perm_step57 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_rol WgNoise.chacha_block.code._t'46 WgNoise.chacha_block.code._t'47 WgNoise.chacha_block.code._t'30 5 10 7)
    (normal_ret_assert (perm_P sh x vi vn (krol l 5 10 7))).
Proof. intros sh x vi vn l Hsh Hl. step_rol_tac (Int.xor (Znth 5 l) (Znth 10 l)) 7. Qed.

Lemma perm_step58 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_add WgNoise.chacha_block.code._t'44 WgNoise.chacha_block.code._t'45 11 12)
    (normal_ret_assert (perm_P sh x vi vn (kadd l 11 12))).
Proof. intros sh x vi vn l Hsh Hl. step_add_tac. Qed.

Lemma perm_step59 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_rol WgNoise.chacha_block.code._t'42 WgNoise.chacha_block.code._t'43 WgNoise.chacha_block.code._t'31 6 11 7)
    (normal_ret_assert (perm_P sh x vi vn (krol l 6 11 7))).
Proof. intros sh x vi vn l Hsh Hl. step_rol_tac (Int.xor (Znth 6 l) (Znth 11 l)) 7. Qed.

Lemma perm_step60 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_add WgNoise.chacha_block.code._t'40 WgNoise.chacha_block.code._t'41 8 13)
    (normal_ret_assert (perm_P sh x vi vn (kadd l 8 13))).
Proof. intros sh x vi vn l Hsh Hl. step_add_tac. Qed.

Lemma perm_step61 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_rol WgNoise.chacha_block.code._t'38 WgNoise.chacha_block.code._t'39 WgNoise.chacha_block.code._t'32 7 8 7)
    (normal_ret_assert (perm_P sh x vi vn (krol l 7 8 7))).
Proof. intros sh x vi vn l Hsh Hl. step_rol_tac (Int.xor (Znth 7 l) (Znth 8 l)) 7. Qed.

Lemma perm_step62 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_add WgNoise.chacha_block.code._t'36 WgNoise.chacha_block.code._t'37 9 14)
    (normal_ret_assert (perm_P sh x vi vn (kadd l 9 14))).
Proof. intros sh x vi vn l Hsh Hl. step_add_tac. Qed.

Lemma perm_step63 : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) (s_rol WgNoise.chacha_block.code._t'34 WgNoise.chacha_block.code._t'35 WgNoise.chacha_block.code._t'33 4 9 7)
    (normal_ret_assert (perm_P sh x vi vn (krol l 4 9 7))).
Proof. intros sh x vi vn l Hsh Hl. step_rol_tac (Int.xor (Znth 4 l) (Znth 9 l)) 7. Qed.

End Steps.

Section Body.
Context {Espec: OracleKind}.
#[local] Existing Instance ChachaBlock.CS.

Lemma perm_body_ok : forall sh x vi vn l, writable_share sh -> Zlength l = 16 ->
  semax perm_Delta (perm_P sh x vi vn l) perm_body (normal_ret_assert (perm_P sh x vi vn (k_dround l))).
Proof.
  intros. unfold perm_body, k_dround; cbv zeta.
  eapply semax_seq'; [apply perm_step0; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step1; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step2; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step3; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step4; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step5; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step6; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step7; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step8; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step9; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step10; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step11; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step12; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step13; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step14; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step15; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step16; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step17; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step18; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step19; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step20; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step21; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step22; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step23; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step24; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step25; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step26; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step27; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step28; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step29; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step30; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step31; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step32; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step33; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step34; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step35; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step36; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step37; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step38; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step39; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step40; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step41; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step42; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step43; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step44; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step45; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step46; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step47; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step48; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step49; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step50; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step51; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step52; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step53; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step54; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step55; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step56; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step57; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step58; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step59; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step60; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step61; auto; zl16 | ].
  eapply semax_seq'; [apply perm_step62; auto; zl16 | ].
  apply perm_step63; auto; zl16.
Qed.

End Body.

#[local] Existing Instance ChachaBlock.CS.

Theorem aead_permute_bodies :
  @semax_body (QPvarspecs ChachaBlock.qp) (aead_imports_def ChachaBlock.CS ++ aead_G_def) ChachaBlock.CS
    WgNoise.chacha_block.code.f_chacha_permute chacha_permute_spec.
Proof.
  start_function.
  forward.
  (* x = &state->x: the struct is its one array field *)
  assert_PROP (field_compatible t_chacha_state [] state) as FC by entailer!.
  replace (align 0 (bitalignof cenv_cs (tarray tuint 16)) / 8) with 0 by reflexivity.
  unfold_data_at (data_at _ _ _ state). rewrite field_at_data_at.
  rewrite field_compatible_field_address by auto with field_compatible.
  simpl nested_field_offset.
  change (nested_field_type t_chacha_state (DOT WgNoise.chacha_block.code._x)) with (tarray tuint 16).
  remember (offset_val 0 state) as x eqn:Ex.
  (* WARN_ON_ONCE(nrounds != 20 && nrounds != 12): t'1 is never used *)
  forward_if (PROP () LOCAL (temp WgNoise.chacha_block.code._x x; temp WgNoise.chacha_block.code._nrounds (Vint (Int.repr nr)))
              SEP (data_at sh (tarray tuint 16) (map Vint st) x)).
  { forward. entailer!. }
  { forward. entailer!. }
  unfold Sfor. forward.
  forward_loop (EX j: Z, PROP (0 <= j; 2*j <= nr)
      LOCAL (temp WgNoise.chacha_block.code._x x; temp WgNoise.chacha_block.code._i (Vint (Int.repr (2*j))); temp WgNoise.chacha_block.code._nrounds (Vint (Int.repr nr)))
      SEP (data_at sh (tarray tuint 16) (map Vint (chacha_rounds (Z.to_nat j) st)) x))%assert
    continue: (EX j: Z, PROP (0 <= j; 2*j+2 <= nr)
      LOCAL (temp WgNoise.chacha_block.code._x x; temp WgNoise.chacha_block.code._i (Vint (Int.repr (2*j))); temp WgNoise.chacha_block.code._nrounds (Vint (Int.repr nr)))
      SEP (data_at sh (tarray tuint 16) (map Vint (chacha_rounds (Z.to_nat (j+1)) st)) x))%assert
    break: (PROP () LOCAL () SEP (data_at sh (tarray tuint 16) (map Vint (chacha_rounds (Z.to_nat (nr/2)) st)) x)).
  - Exists 0. change (Z.to_nat 0) with O. rewrite rounds_O. entailer!.
  - Intros j. forward_if.
    + (* one double round: the chained step lemmas *)
      match goal with |- semax _ _ ?c _ => change c with perm_body end.
      assert (LEN: Zlength (chacha_rounds (Z.to_nat j) st) = 16) by (apply Zlength_chacha_rounds; auto).
      assert (E: chacha_rounds (Z.to_nat (j+1)) st = k_dround (chacha_rounds (Z.to_nat j) st)).
      { rewrite k_dround_eq by auto. rewrite <- chacha_rounds_S.
        replace (Z.to_nat (j+1)) with (S (Z.to_nat j)) by (rewrite <- Z2Nat.inj_succ by lia; f_equal; lia).
        reflexivity. }
      remember (chacha_rounds (Z.to_nat j) st) as l eqn:El.
      eapply semax_pre; [| eapply semax_post; [| | | |
        apply (perm_body_ok sh x (Vint (Int.repr (2*j))) (Vint (Int.repr nr)) l SH LEN)]].
      * unfold perm_P. apply ENTAIL_refl.
      * simpl_ret_assert. unfold perm_P. Exists j. rewrite E. entailer!.
      * simpl_ret_assert. normalize.
      * simpl_ret_assert. normalize.
      * intros. simpl_ret_assert. normalize.
    + assert (Hj: nr / 2 = j) by (destruct H0; subst nr; [change (20/2) with 10 | change (12/2) with 6]; lia).
      rewrite <- Hj. forward. entailer!.
  - Intros j. forward. Exists (j+1). entailer!. do 2 f_equal. lia.
  - remember (chacha_rounds (Z.to_nat (nr / 2)) st) as r eqn:Er.
    unfold POSTCONDITION, abbreviate. simpl_ret_assert.
    unfold_data_at (data_at _ t_chacha_state _ state). rewrite field_at_data_at.
    rewrite field_compatible_field_address by auto with field_compatible.
    simpl nested_field_offset. subst x. entailer!.
Qed.
