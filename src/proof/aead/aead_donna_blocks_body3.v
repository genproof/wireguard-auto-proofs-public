(* body proof of poly1305_core_blocks (donna32), against aead_spec3.aead_G3. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require WgNoise.chacha.code WgNoise.chacha_block.code WgNoise.poly1305.code WgNoise.poly1305_donna32.code
        WgNoise.chacha20poly1305.code WgNoise.shim.code.
Require Import WgNoise.proof.libc.spec.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.common.wg3_iface.
Require Import WgNoise.proof.aead.aead_spec3.
Require Import WgNoise.proof.aead.aead_cce.
Require Import WgNoise.proof.aead.aead_bytes.
Require Import WgNoise.proof.aead.aead_model.
Require Import WgNoise.proof.aead.aead_donna3_math.
Require Import WgNoise.proof.aead.aead_donna3_msg.

Local Open Scope Z_scope.

Module C := WgNoise.poly1305_donna32.code.
Local Definition _input := WgNoise.poly1305_donna32.code._input.
Local Definition _state := WgNoise.poly1305_donna32.code._state.
Local Definition _key := WgNoise.poly1305_donna32.code._key.
Local Definition _src := WgNoise.poly1305_donna32.code._src.
Local Definition _nblocks := WgNoise.poly1305_donna32.code._nblocks.
Local Definition _hibit := WgNoise.poly1305_donna32.code._hibit.

#[local] Existing Instance Poly1305Donna32.CS.

(* p1305_h_val / p1305_key_val with their reptype computed in Poly1305Donna32.CS (same terms) *)
Definition adb3_h_val (h: list Z) : reptype t_p1305_state := inl (map Vint (map Int.repr h)).
Definition adb3_key_val (r: Z) : reptype t_p1305_core_key :=
  (inl (map Vint (map Int.repr (p1305_r_limbs r))),
   inl (map (fun z => Vint (Int.repr (5 * z))) (sublist 1 5 (p1305_r_limbs r)) ++ [Vundef])).

Lemma adb3_h_cs sh h p :
  @data_at Poly1305.CS sh t_p1305_state (p1305_h_val h) p =
  @data_at Poly1305Donna32.CS sh t_p1305_state (adb3_h_val h) p.
Proof.
  rewrite (@data_at_change_composite Poly1305.CS Poly1305Donna32.CS _ sh t_p1305_state (p1305_h_val h) (adb3_h_val h));
  [reflexivity | apply JMeq_refl | reflexivity].
Qed.

Lemma adb3_key_cs sh r p :
  @data_at Poly1305.CS sh t_p1305_core_key (p1305_key_val r) p =
  @data_at Poly1305Donna32.CS sh t_p1305_core_key (adb3_key_val r) p.
Proof.
  rewrite (@data_at_change_composite Poly1305.CS Poly1305Donna32.CS _ sh t_p1305_core_key (p1305_key_val r) (adb3_key_val r));
  [reflexivity | apply JMeq_refl | reflexivity].
Qed.

Definition adb3_key_val' (r0 r1 r2 r3 r4: Z) : reptype t_p1305_core_key :=
  (inl [Vint (Int.repr r0); Vint (Int.repr r1); Vint (Int.repr r2); Vint (Int.repr r3); Vint (Int.repr r4)],
   inl [Vint (Int.repr (5 * r1)); Vint (Int.repr (5 * r2)); Vint (Int.repr (5 * r3)); Vint (Int.repr (5 * r4));
        Vundef]).

Lemma adb3_key_val_eq r :
  adb3_key_val r = adb3_key_val' (r mod 2 ^ 26) ((r / 2 ^ 26) mod 2 ^ 26) ((r / 2 ^ 52) mod 2 ^ 26)
                     ((r / 2 ^ 78) mod 2 ^ 26) (r / 2 ^ 104).
Proof. reflexivity. Qed.

Lemma adb3_h_list (h: list Z) : Zlength h = 5 -> h = [Znth 0 h; Znth 1 h; Znth 2 h; Znth 3 h; Znth 4 h].
Proof.
  intros Hl. destruct h as [|a [|b [|c [|d [|e [|f t]]]]]]; rewrite ?Zlength_cons, ?Zlength_nil in Hl;
  try (pose proof (Zlength_nonneg t)); try lia; reflexivity.
Qed.

(* the words of a block are the words of the whole buffer at the block's offset *)
Lemma adb3_le32_sublist bs o j :
  0 <= o -> 0 <= j <= 12 -> o + 16 <= Zlength bs ->
  le32_at (sublist o (o + 16) bs) j = le32_at bs (o + j).
Proof.
  intros. unfold le32_at.
  rewrite !Znth_sublist by lia.
  f_equal; f_equal; lia.
Qed.

Definition adb3_blks (bs: list byte) (n: nat) : list (list byte) :=
  map (fun i => sublist (16 * i) (16 * i + 16) bs) (map Z.of_nat (seq 0 n)).

Lemma adb3_blks_ext bs bs' n :
  (forall i, 0 <= i < Z.of_nat n -> sublist (16 * i) (16 * i + 16) bs = sublist (16 * i) (16 * i + 16) bs') ->
  adb3_blks bs n = adb3_blks bs' n.
Proof.
  intros Hx. unfold adb3_blks. rewrite !map_map. apply map_ext_in.
  intros a Ha. apply in_seq in Ha. apply Hx. lia.
Qed.

Lemma adb3_core_blocks_eq r hibit acc bs :
  Zlength bs mod 16 = 0 ->
  p1305_core_blocks r hibit acc bs = fold_left (p1305_core_step r hibit) (adb3_blks bs (Z.to_nat (Zlength bs / 16))) acc.
Proof. reflexivity. Qed.

(* one more block *)
Lemma adb3_core_blocks_snoc r hibit acc bs k :
  0 <= k -> 16 * (k + 1) <= Zlength bs ->
  p1305_core_blocks r hibit acc (sublist 0 (16 * (k + 1)) bs) =
  p1305_core_step r hibit (p1305_core_blocks r hibit acc (sublist 0 (16 * k) bs)) (sublist (16 * k) (16 * k + 16) bs).
Proof.
  intros Hk Hl. unfold p1305_core_blocks.
  rewrite !Zlength_sublist by lia.
  replace ((16 * (k + 1) - 0) / 16) with (k + 1) by (rewrite Z.sub_0_r, Z.mul_comm, Z.div_mul; lia).
  replace ((16 * k - 0) / 16) with k by (rewrite Z.sub_0_r, Z.mul_comm, Z.div_mul; lia).
  change (fun i => sublist (16 * i) (16 * i + 16) (sublist 0 (16 * (k + 1)) bs)) with
    (fun i => sublist (16 * i) (16 * i + 16) (sublist 0 (16 * (k + 1)) bs)).
  fold (adb3_blks (sublist 0 (16 * (k + 1)) bs) (Z.to_nat (k + 1))).
  fold (adb3_blks (sublist 0 (16 * k) bs) (Z.to_nat k)).
  rewrite Z2Nat.inj_add by lia. change (Z.to_nat 1) with 1%nat.
  unfold adb3_blks at 1. rewrite seq_app, !map_app, fold_left_app. simpl.
  rewrite Z2Nat.id by lia.
  f_equal.
  - fold (adb3_blks (sublist 0 (16 * (k + 1)) bs) (Z.to_nat k)).
    f_equal. apply adb3_blks_ext. intros i Hi. rewrite Z2Nat.id in Hi by lia.
    rewrite !sublist_sublist by lia. f_equal; lia.
  - rewrite sublist_sublist by lia. f_equal; lia.
Qed.

(* the step only depends on the accumulator mod p *)
Lemma adb3_step_mod r hibit a b blk :
  a mod p1305_p = b mod p1305_p -> p1305_core_step r hibit a blk = p1305_core_step r hibit b blk.
Proof.
  intros E. unfold p1305_core_step.
  rewrite Zmult_mod. symmetry. rewrite Zmult_mod. symmetry. f_equal. f_equal.
  rewrite <- !Z.add_assoc, Zplus_mod, E, <- Zplus_mod. reflexivity.
Qed.

Lemma adb3_repr_znth (l: list int) i : 0 <= i < Zlength l -> Int.repr (Znth i (map Int.unsigned l)) = Znth i l.
Proof. intros. rewrite Znth_map by lia. apply Int.repr_unsigned. Qed.

Lemma adb3_upd5 (a b: list Z) :
  Zlength a = 5 -> Zlength b = 5 ->
  upd_Znth 4 (upd_Znth 3 (upd_Znth 2 (upd_Znth 1 (upd_Znth 0 (map Vint (map Int.repr a))
    (Vint (Int.repr (Znth 0 b)))) (Vint (Int.repr (Znth 1 b)))) (Vint (Int.repr (Znth 2 b))))
    (Vint (Int.repr (Znth 3 b)))) (Vint (Int.repr (Znth 4 b))) = map Vint (map Int.repr b).
Proof.
  intros Ha Hb. rewrite (adb3_h_list a Ha). rewrite (adb3_h_list b Hb) at 6. reflexivity.
Qed.

Theorem aead_donna_blocks_bodies3 :
  @semax_body (QPvarspecs Poly1305Donna32.qp) (aead_imports3 Poly1305Donna32.CS ++ aead_G3) Poly1305Donna32.CS
    WgNoise.poly1305_donna32.code.f_poly1305_core_blocks poly1305_core_blocks_spec.
Proof.
start_function.
forward.
forward_if (PROP (nb <> 0) LOCAL (temp _input src; temp _state hp; temp _key kp; temp _src src;
   temp _nblocks (Vint (Int.repr nb)); temp _hibit (Vint (Int.repr hibit)))
   SEP (data_at hsh t_p1305_state (p1305_h_val h) hp; data_at ksh t_p1305_core_key (p1305_key_val r) kp;
        prim_bytes msh bs src)).
{ forward. Exists h.
  assert (nb = 0) by (apply (f_equal Int.unsigned) in H4; rewrite Int.unsigned_repr in H4 by rep_lia; exact H4).
  subst nb. assert (bs = []) by (apply Zlength_nil_inv; lia). subst bs.
  entailer!. }
{ forward. entailer!. }
Intros.
rewrite adb3_h_cs, adb3_key_cs, adb3_key_val_eq.
unfold adb3_h_val. rewrite (adb3_h_list h) by (destruct H; auto).
assert (Hbs: Zlength bs > 0) by lia.
unfold prim_bytes. rewrite if_false by lia.
unfold adb3_key_val'.
remember (r mod 2 ^ 26) as r0 eqn:Hr0. remember ((r / 2 ^ 26) mod 2 ^ 26) as r1 eqn:Hr1.
remember ((r / 2 ^ 52) mod 2 ^ 26) as r2 eqn:Hr2. remember ((r / 2 ^ 78) mod 2 ^ 26) as r3 eqn:Hr3.
remember (r / 2 ^ 104) as r4 eqn:Hr4.
forward.
forward. forward. forward. forward. forward.
forward. forward. forward. forward.
forward. forward. forward. forward. forward.
forward_loop
 (EX k: Z, EX hk: list Z,
  PROP (0 <= k < nb; p1305_limbs_ok hk;
        p1305_limbs_val hk mod p1305_p = p1305_core_blocks r hibit (p1305_limbs_val h) (sublist 0 (16 * k) bs) mod p1305_p)
  LOCAL (temp _input (offset_val (16 * k) src); temp _nblocks (Vint (Int.repr (nb - k)));
         temp C._h0 (Vint (Int.repr (Znth 0 hk))); temp C._h1 (Vint (Int.repr (Znth 1 hk)));
         temp C._h2 (Vint (Int.repr (Znth 2 hk))); temp C._h3 (Vint (Int.repr (Znth 3 hk)));
         temp C._h4 (Vint (Int.repr (Znth 4 hk)));
         temp C._r0 (Vint (Int.repr r0)); temp C._r1 (Vint (Int.repr r1)); temp C._r2 (Vint (Int.repr r2));
         temp C._r3 (Vint (Int.repr r3)); temp C._r4 (Vint (Int.repr r4));
         temp C._s1 (Vint (Int.repr (5 * r1))); temp C._s2 (Vint (Int.repr (5 * r2)));
         temp C._s3 (Vint (Int.repr (5 * r3))); temp C._s4 (Vint (Int.repr (5 * r4)));
         temp _hibit (Vint (Int.repr (hibit * 2 ^ 24))); temp _state hp)
  SEP (data_at hsh t_p1305_state (inl (map Vint (map Int.repr [Znth 0 h; Znth 1 h; Znth 2 h; Znth 3 h; Znth 4 h]))) hp;
       data_at ksh t_p1305_core_key
         (inl [Vint (Int.repr r0); Vint (Int.repr r1); Vint (Int.repr r2); Vint (Int.repr r3); Vint (Int.repr r4)],
          inl [Vint (Int.repr (5 * r1)); Vint (Int.repr (5 * r2)); Vint (Int.repr (5 * r3)); Vint (Int.repr (5 * r4));
               Vundef]) kp;
       data_at msh (tarray tuchar (Zlength bs)) (map Vubyte bs) src))%assert
 continue:
 (EX k: Z, EX hk: list Z,
  PROP (0 <= k < nb; p1305_limbs_ok hk;
        p1305_limbs_val hk mod p1305_p = p1305_core_blocks r hibit (p1305_limbs_val h) (sublist 0 (16 * (k + 1)) bs) mod p1305_p)
  LOCAL (temp _input (offset_val (16 * (k + 1)) src); temp _nblocks (Vint (Int.repr (nb - k)));
         temp C._h0 (Vint (Int.repr (Znth 0 hk))); temp C._h1 (Vint (Int.repr (Znth 1 hk)));
         temp C._h2 (Vint (Int.repr (Znth 2 hk))); temp C._h3 (Vint (Int.repr (Znth 3 hk)));
         temp C._h4 (Vint (Int.repr (Znth 4 hk)));
         temp C._r0 (Vint (Int.repr r0)); temp C._r1 (Vint (Int.repr r1)); temp C._r2 (Vint (Int.repr r2));
         temp C._r3 (Vint (Int.repr r3)); temp C._r4 (Vint (Int.repr r4));
         temp C._s1 (Vint (Int.repr (5 * r1))); temp C._s2 (Vint (Int.repr (5 * r2)));
         temp C._s3 (Vint (Int.repr (5 * r3))); temp C._s4 (Vint (Int.repr (5 * r4)));
         temp _hibit (Vint (Int.repr (hibit * 2 ^ 24))); temp _state hp)
  SEP (data_at hsh t_p1305_state (inl (map Vint (map Int.repr [Znth 0 h; Znth 1 h; Znth 2 h; Znth 3 h; Znth 4 h]))) hp;
       data_at ksh t_p1305_core_key
         (inl [Vint (Int.repr r0); Vint (Int.repr r1); Vint (Int.repr r2); Vint (Int.repr r3); Vint (Int.repr r4)],
          inl [Vint (Int.repr (5 * r1)); Vint (Int.repr (5 * r2)); Vint (Int.repr (5 * r3)); Vint (Int.repr (5 * r4));
               Vundef]) kp;
       data_at msh (tarray tuchar (Zlength bs)) (map Vubyte bs) src))%assert
 break:
 (EX hk: list Z,
  PROP (p1305_limbs_ok hk;
        p1305_limbs_val hk mod p1305_p = p1305_core_blocks r hibit (p1305_limbs_val h) bs mod p1305_p)
  LOCAL (temp C._h0 (Vint (Int.repr (Znth 0 hk))); temp C._h1 (Vint (Int.repr (Znth 1 hk)));
         temp C._h2 (Vint (Int.repr (Znth 2 hk))); temp C._h3 (Vint (Int.repr (Znth 3 hk)));
         temp C._h4 (Vint (Int.repr (Znth 4 hk))); temp _state hp)
  SEP (data_at hsh t_p1305_state (inl (map Vint (map Int.repr [Znth 0 h; Znth 1 h; Znth 2 h; Znth 3 h; Znth 4 h]))) hp;
       data_at ksh t_p1305_core_key
         (inl [Vint (Int.repr r0); Vint (Int.repr r1); Vint (Int.repr r2); Vint (Int.repr r3); Vint (Int.repr r4)],
          inl [Vint (Int.repr (5 * r1)); Vint (Int.repr (5 * r2)); Vint (Int.repr (5 * r3)); Vint (Int.repr (5 * r4));
               Vundef]) kp;
       data_at msh (tarray tuchar (Zlength bs)) (map Vubyte bs) src))%assert.
{ Exists 0 h. entailer!. destruct H3; subst; reflexivity. }
{ Intros k hk.
  forward_call (msh, src, 16 * k, bs). { entailer!. }
  forward.
  forward_call (msh, src, 16 * k + 3, bs). { entailer!. }
  forward.
  forward_call (msh, src, 16 * k + 6, bs). { entailer!. }
  forward.
  forward_call (msh, src, 16 * k + 9, bs). { entailer!. }
  forward.
  forward_call (msh, src, 16 * k + 12, bs). { entailer!. }
  forward.
  forward. forward. forward. forward. forward.
  forward. forward. forward. forward. forward.
  forward. forward. forward. forward. forward.
  forward. forward. forward. forward. forward.
  forward. forward. forward. forward.
  pose proof (adb3_c_ok hk r hibit (le32_at bs (16 * k)) (le32_at bs (16 * k + 3)) (le32_at bs (16 * k + 6))
    (le32_at bs (16 * k + 9)) (le32_at bs (16 * k + 12)) H6 H0 H3) as HC.
  cbv zeta in HC.
  change (Znth 0 (p1305_r_limbs r)) with (r mod 2 ^ 26) in HC.
  change (Znth 1 (p1305_r_limbs r)) with ((r / 2 ^ 26) mod 2 ^ 26) in HC.
  change (Znth 2 (p1305_r_limbs r)) with ((r / 2 ^ 52) mod 2 ^ 26) in HC.
  change (Znth 3 (p1305_r_limbs r)) with ((r / 2 ^ 78) mod 2 ^ 26) in HC.
  change (Znth 4 (p1305_r_limbs r)) with (r / 2 ^ 104) in HC.
  rewrite <- Hr0, <- Hr1, <- Hr2, <- Hr3, <- Hr4 in HC.
  set (L := adb3_c (Int.repr (Znth 0 hk)) (Int.repr (Znth 1 hk)) (Int.repr (Znth 2 hk))
    (Int.repr (Znth 3 hk)) (Int.repr (Znth 4 hk)) (Int.repr r0) (Int.repr r1) (Int.repr r2) (Int.repr r3)
    (Int.repr r4) (Int.repr (5 * r1)) (Int.repr (5 * r2)) (Int.repr (5 * r3)) (Int.repr (5 * r4))
    (le32_at bs (16 * k)) (le32_at bs (16 * k + 3)) (le32_at bs (16 * k + 6)) (le32_at bs (16 * k + 9))
    (le32_at bs (16 * k + 12)) (Int.repr (hibit * 2 ^ 24))) in HC.
  destruct HC as [Hok Hval].
  assert (HL: Zlength L = 5) by reflexivity.
  match goal with |- context [LOCALx (temp _ _ :: temp _ (Vint ?X1) :: temp _ (Vint ?X0) :: temp _ _ ::
        temp _ (Vint ?X4) :: temp _ _ :: temp _ (Vint ?X3) :: temp _ _ :: temp _ (Vint ?X2) :: _) _] =>
    change X0 with (Znth 0 L); change X1 with (Znth 1 L); change X2 with (Znth 2 L);
    change X3 with (Znth 3 L); change X4 with (Znth 4 L)
  end.
  clearbody L.
  Exists k (map Int.unsigned L).
  rewrite !adb3_repr_znth by lia.
  entailer!.
  split; [ | f_equal; lia].
  assert (Hk1: 16 * k + 16 <= Zlength bs) by lia.
  rewrite Hval.
  rewrite <- (adb3_le32_sublist bs (16 * k) 3), <- (adb3_le32_sublist bs (16 * k) 6),
    <- (adb3_le32_sublist bs (16 * k) 9), <- (adb3_le32_sublist bs (16 * k) 12) by lia.
  replace (le32_at bs (16 * k)) with (le32_at (sublist (16 * k) (16 * k + 16) bs) 0)
    by (rewrite adb3_le32_sublist by lia; f_equal; lia).
  rewrite adb3_m_le by (rewrite Zlength_sublist by lia; lia).
  rewrite adb3_core_blocks_snoc by lia.
  change ((p1305_limbs_val hk + le_Z (sublist (16 * k) (16 * k + 16) bs) + hibit * 2 ^ 128) * r mod p1305_p)
    with (p1305_core_step r hibit (p1305_limbs_val hk) (sublist (16 * k) (16 * k + 16) bs)).
  rewrite (adb3_step_mod _ _ _ _ _ H7).
  unfold p1305_core_step. rewrite Zmod_mod. reflexivity.
}
{ Intros k hk.
  forward. forward.
  forward_if.
  - forward. Exists (k + 1) hk. entailer!.
    rewrite !Int.unsigned_repr in H8' by rep_lia. split; [lia | f_equal; f_equal; lia].
  - forward. Exists hk. entailer!.
    assert (nb - k - 1 = 0) by (apply (f_equal Int.unsigned) in H8; rewrite Int.unsigned_repr in H8 by rep_lia; exact H8).
    replace (16 * (k + 1)) with (Zlength bs) in H7 by lia. rewrite sublist_same in H7 by lia. exact H7. }
Intros hk.
forward. forward. forward. forward. forward.
Exists hk.
rewrite adb3_upd5 by (destruct H; destruct H5; auto).
rewrite adb3_h_cs, adb3_key_cs, adb3_key_val_eq. unfold adb3_key_val', adb3_h_val.
subst r0 r1 r2 r3 r4.
unfold prim_bytes. rewrite if_false by lia.
entailer!.
Qed.
