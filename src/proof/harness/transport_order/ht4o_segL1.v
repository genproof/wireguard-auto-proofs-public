(* law transport_order: main's segment L1 (body statements 0..8): kind, L, the PTRDIFF_MAX guard (break), enc_len, tot, the three
   mallocs and their NULL test (3 frees + break).
   States and the cut: ht4o_main_defs.v; *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_dec3.
Require Import WgNoise.proof.counter.counter_spec.
Require Import WgNoise.proof.harness.common4t.ht4_worlds.
Require Import WgNoise.proof.harness.common4t.ht4c_spec.
Require Import WgNoise.proof.harness.common4t.ht4r_spec.
Require Import WgNoise.proof.harness.common4t.ht4a_aead.
Require Import WgNoise.proof.harness.transport_order.ht4o_main_defs.

#[local] Existing Instance W_transport_order.
Local Open Scope Z_scope.

(* a malloc result: NULL, or a token and an uninitialised buffer of n bytes (as haead_cda_body3_B.v) *)
Definition ht4oL1_mres (n: Z) (p: val) : mpred :=
  if eq_dec p nullval then emp else (malloc_token Ews (tarray tuchar n) p * data_at_ Ews (tarray tuchar n) p)%logic.
Definition ht4oL1_nul (p: val) : bool := if eq_dec p nullval then true else false.

Lemma ht4oL1_mres_valid (n: Z) (p: val) : ht4oL1_mres n p |-- valid_pointer p.
Proof.
  unfold ht4oL1_mres. destruct (eq_dec p nullval).
  - subst. apply valid_pointer_null.
  - destruct (zlt 0 n).
    + apply sepcon_valid_pointer2. unfold data_at_. apply data_at_valid_ptr; auto.
      simpl. rewrite Z.max_r by lia. lia.
    + apply sepcon_valid_pointer1. apply malloc_token_valid_pointer. simpl. lia.
Qed.

Lemma ht4oL1_mres_local (n: Z) (p: val) : ht4oL1_mres n p |-- !! is_pointer_or_null p.
Proof.
  unfold ht4oL1_mres. destruct (eq_dec p nullval).
  - subst. entailer!.
  - entailer!.
Qed.

Lemma ht4oL1_cmp (p: val) : is_pointer_or_null p ->
  force_val (sem_cast_i2bool (force_val (sem_cmp_pp Ceq p (Vlong (Int64.repr 0))))) =
  Vint (if ht4oL1_nul p then Int.one else Int.zero).
Proof.
  intros Hp. unfold ht4oL1_nul. destruct (eq_dec p nullval) as [-> | Hn]; [reflexivity |].
  destruct p; try contradiction; simpl in Hp.
  - subst. contradiction Hn. reflexivity.
  - reflexivity.
Qed.

#[local] Hint Resolve ht4oL1_mres_valid : valid_pointer.
#[local] Hint Resolve ht4oL1_mres_local : saturate_local.

Lemma ht4oL1_buf (n: Z) (p: val) : p <> nullval -> ht4oL1_mres n p |-- ht4o_buf n (Zrepeat Vundef n) p.
Proof. intros. unfold ht4oL1_mres, ht4o_buf. rewrite if_false by auto. apply derives_refl. Qed.

Ltac ht4oL1_ur :=
  repeat match goal with Hx: context [Int64.unsigned (Int64.repr _)] |- _ =>
    rewrite !Int64.unsigned_repr in Hx by rep_lia end.

Lemma ht4o_segL1_ok {Espec: OracleKind} (F: ht4o_fix) (FR: mpred) (i: Z) (R: ret_assert) :
  semax ht4o_Delta (ht4o_Icont F FR i) ht4o_segL1
    (overridePost (ht4o_PL1 F FR i) (loop1_ret_assert (ht4o_Icont F FR i) (overridePost (ht4o_Brk F FR) R))).
Proof.
  intros. destruct F as [gv vrc vwm vsnap vkey K steps]. destruct R as [Rn Rb Rc Rr].
  unfold ht4o_Icont, ht4o_St, ht4o_Delta, ht4o_temps, ht4o_lvars, ht4o_world, ht4o_segL1.
  cbn [f_gv f_rc f_wm f_snap f_key f_K f_steps]. simpl app.
  simplify_func_tycontext. abbreviate_semax. Intros Y.
  forward_call. Intros u.
  forward. { entailer!. destruct H10 as [_ X]; discriminate. }
  assert (Hk: Int.mods (Int.repr u) (Int.repr 4) = Int.repr (u mod 4)).
  { unfold Int.mods. rewrite !Int.signed_repr by rep_lia. rewrite Z.rem_mod_nonneg by lia. reflexivity. }
  rewrite Hk. clear Hk.
  assert (Hkd: 0 <= u mod 4 < 4) by (apply Z.mod_pos_bound; lia).
  forget (u mod 4) as kind.
  forward_call. Intros L.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx ((L <= Int64.max_signed - 32) :: P) (LOCALx Q (SEPx R))) end.
  { forward. cbn [RA_break RA_normal loop1_ret_assert overridePost]. unfold ht4o_Brk, ht4o_lvars.
    cbn [f_gv f_rc f_wm f_snap f_key f_K f_steps].
    Exists (y_top Y) (y_S Y). sep_apply (data_at_data_at_ Tsh ht4o_trc). entailer!. }
  { forward. entailer!. rewrite !Int64.unsigned_repr in H4 by rep_lia. rep_lia. }
  Intros.
  forward_if (temp TO._t'4 (Vint (if andb (Z.eqb kind 3) (Z.ltb L 16) then Int.one else Int.zero))).
  { forward. entailer!. simpl Z.eqb. cbn [andb]. unfold Int64.cmpu, Int64.ltu.
    rewrite !Int64.unsigned_repr by rep_lia.
    destruct (Z.ltb_spec L 16), (zlt L 16); try lia; reflexivity. }
  { forward. entailer!. rewrite (proj2 (Z.eqb_neq kind 3) H5). reflexivity. }
  forward_if (temp TO._enc_len (Vlong (Int64.repr (ht4o_enc kind L)))).
  { forward. entailer!. unfold ht4o_enc.
    destruct ((kind =? 3) && (L <? 16))%bool; [reflexivity | contradiction H5; reflexivity]. }
  { forward. entailer!. unfold ht4o_enc.
    destruct ((kind =? 3) && (L <? 16))%bool; [discriminate | reflexivity]. }
  assert (He: L <= ht4o_enc kind L <= L + 16) by (unfold ht4o_enc; destruct (_ && _)%bool; lia).
  forward.
  forward_call (tarray tuchar (16 + ht4o_enc kind L), gv).
  { simpl sizeof. rep_lia. }
  Intros pkt. fold (ht4oL1_mres (16 + ht4o_enc kind L) pkt).
  forward_if (temp TO._t'6 (Vlong (Int64.repr (ht4o_plen (ht4o_enc kind L))))).
  { forward. entailer!. ht4oL1_ur.
    unfold ht4o_plen. rewrite Z.max_r by lia. reflexivity. }
  { forward. entailer!. ht4oL1_ur.
    unfold ht4o_plen. rewrite Z.max_l by lia. reflexivity. }
  assert (Hp: 0 <= ht4o_plen (ht4o_enc kind L) <= L) by (unfold ht4o_plen; lia).
  forward_call (tarray tuchar (ht4o_plen (ht4o_enc kind L)), gv).
  { simpl sizeof. rep_lia. }
  Intros po. fold (ht4oL1_mres (ht4o_plen (ht4o_enc kind L)) po). forward.
  forward_if (temp TO._t'8 (Vlong (Int64.repr (ht4o_plen (ht4o_enc kind L))))).
  { forward. entailer!. ht4oL1_ur.
    unfold ht4o_plen. rewrite Z.max_r by lia. reflexivity. }
  { forward. entailer!. ht4oL1_ur.
    unfold ht4o_plen. rewrite Z.max_l by lia. reflexivity. }
  forward_call (tarray tuchar (ht4o_plen (ht4o_enc kind L)), gv).
  { simpl sizeof. rep_lia. }
  Intros rp. fold (ht4oL1_mres (ht4o_plen (ht4o_enc kind L)) rp). forward.
  forward_if (temp TO._t'10 (Vint (if orb (ht4oL1_nul pkt) (ht4oL1_nul po) then Int.one else Int.zero))).
  { forward. entailer!. }
  { forward. entailer!. rewrite ht4oL1_cmp by auto. unfold ht4oL1_nul at 1.
    destruct (eq_dec pkt nullval); [contradiction | reflexivity]. }
  forward_if (temp TO._t'11 (Vint (if orb (orb (ht4oL1_nul pkt) (ht4oL1_nul po)) (ht4oL1_nul rp) then Int.one else Int.zero))).
  { forward. destruct (ht4oL1_nul pkt || ht4oL1_nul po)%bool; [entailer! | exfalso; match goal with Hx: Int.repr 0 <> Int.zero |- _ => apply Hx; reflexivity end]. }
  { destruct (ht4oL1_nul pkt || ht4oL1_nul po)%bool; [contradiction Int.one_not_zero | ].
    forward. entailer!. rewrite ht4oL1_cmp by auto. reflexivity. }
  destruct (ht4oL1_nul pkt || ht4oL1_nul po || ht4oL1_nul rp)%bool eqn:E.
  - forward_if.
    2:{ exfalso. match goal with Hx: _ = Int.zero |- _ => apply Int.one_not_zero, Hx end. }
    unfold ht4oL1_mres.
    forward_call (tarray tuchar (16 + ht4o_enc kind L), pkt, gv).
    forward_call (tarray tuchar (ht4o_plen (ht4o_enc kind L)), po, gv).
    forward_call (tarray tuchar (ht4o_plen (ht4o_enc kind L)), rp, gv).
    forward. cbn [RA_break RA_normal loop1_ret_assert overridePost]. unfold ht4o_Brk, ht4o_lvars.
    cbn [f_gv f_rc f_wm f_snap f_key f_K f_steps].
    Exists (y_top Y) (y_S Y). sep_apply (data_at_data_at_ Tsh ht4o_trc). entailer!.
  - assert (pkt <> nullval /\ po <> nullval /\ rp <> nullval) as [Hn1 [Hn2 Hn3]].
    { unfold ht4oL1_nul in E.
      destruct (eq_dec pkt nullval), (eq_dec po nullval), (eq_dec rp nullval); try discriminate. auto. }
    forward_if.
    { exfalso; lia. }
    forward. unfold ht4o_PL1. Exists Y kind L pkt po rp.
    unfold ht4o_tB, ht4o_temps, ht4o_lvars, ht4o_world, ht4o_kL. cbn [f_gv f_rc f_wm f_snap f_key f_K f_steps].
    simpl app.
    sep_apply (ht4oL1_buf (16 + ht4o_enc kind L) pkt Hn1).
    sep_apply (ht4oL1_buf (ht4o_plen (ht4o_enc kind L)) po Hn2).
    sep_apply (ht4oL1_buf (ht4o_plen (ht4o_enc kind L)) rp Hn3).
    entailer!.
Qed.
