(* segment A of main's loop body (statements 0..7: kind, enc_len, tot, pt_len, the three mallocs, the NULL test with its frees and break).
   States and segments: hka5_defs.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_dec3.
Require Import WgNoise.proof.counter.counter_spec.
Require Import WgNoise.proof.harness.transport_keepalive.hka5_defs.

#[local] Existing Instance W_transport_keepalive.
Local Open Scope Z_scope.

Ltac hka5a_mod_tc :=
  entailer!;
  match goal with H: _ /\ Int.repr ?k = Int.mone |- _ =>
    let H' := fresh in destruct H as [_ H']; apply (f_equal Int.signed) in H';
    rewrite Int.signed_repr in H' by rep_lia; rewrite Int.signed_mone in H'; lia end.

(* the RA_normal of a forward_if's post inside hka5_LR, made concrete *)
Ltac hka5a_post := unfold hka5_LR, hka5_R;
  cbn [RA_normal loop1_ret_assert overridePost frame_ret_assert function_body_ret_assert].

Ltac hka5a_brk := unfold hka5_LR, hka5_R;
  cbn [RA_break RA_normal loop1_ret_assert overridePost frame_ret_assert function_body_ret_assert].

Lemma hka5a_add16 enc : Int64.add (Int64.repr (Int.signed (Int.repr 16))) (Int64.repr enc) = Int64.repr (16 + enc).
Proof.
  rewrite Int.signed_repr by rep_lia. unfold Int64.add. apply Int64.eqm_samerepr.
  apply Int64.eqm_add; apply Int64.eqm_sym; apply Int64.eqm_unsigned_repr.
Qed.

Lemma hka5a_enc_range k e : hka5_kind_ok k e -> 0 <= e <= 16.
Proof. unfold hka5_kind_ok. intros (Hk & H3 & Hn3). destruct (Z.eq_dec k 3); [specialize (H3 e0) | specialize (Hn3 n)]; lia. Qed.

Lemma hka5a_mods b k : 0 <= b <= Byte.max_unsigned -> 0 < k <= 255 ->
  Int.mods (Int.repr b) (Int.repr k) = Int.repr (b mod k).
Proof.
  intros. unfold Int.mods. rewrite !Int.signed_repr by rep_lia. rewrite Z.rem_mod_nonneg by lia. reflexivity.
Qed.

Lemma hka5a_signed_mod b k : 0 <= b -> 0 < k <= 255 -> Int.signed (Int.repr (b mod k)) = b mod k.
Proof. intros. pose proof (Z.mod_pos_bound b k ltac:(lia)). apply Int.signed_repr. rep_lia. Qed.

Lemma hka5_segA_ok {Espec: OracleKind} gv vrc vwm vsnap vkey key steps FR i top S bm ha ln :
  semax hka5_Delta (hka5_PA gv vrc vwm vsnap vkey key steps FR i top S bm ha ln) hka5_segA
    (overridePost (hka5_QA gv vrc vwm vsnap vkey key steps FR i top S bm ha ln)
                  (hka5_LR gv vrc vwm vsnap vkey key steps FR)).
Proof.
  unfold hka5_Delta, hka5_PA, hka5_QA, hka5_PB, hka5_segA, hka5_tA, hka5_tl, hka5_lv, hka5_cw, hka5_fr.
  simpl app. abbreviate_semax.
  Intros.
  forward_call tt. Intros b1.
  forward.
  { hka5a_mod_tc. }
  rewrite (hka5a_mods b1 4) by rep_lia.
  assert (Hkr: 0 <= b1 mod 4 < 4) by (apply Z.mod_pos_bound; lia).
  forward_if (EX enc: Z,
    PROP (hka5_kind_ok (b1 mod 4) enc)
    LOCAL (temp KA._enc_len (Vlong (Int64.repr enc)); temp KA._kind (Vint (Int.repr (b1 mod 4)));
      temp KA._i (Vlong (Int64.repr i)); temp KA._steps (Vlong (Int64.repr steps));
      temp KA._have_auth (Vint (Int.repr ha)); temp KA._last_nonce (Vlong (Int64.repr ln));
      lvar KA._rc ht4k_trc vrc; lvar KA._wm ht4k_twm vwm; lvar KA._snap ht4k_tsnap vsnap;
      lvar KA._key (tarray tuchar 32) vkey; gvars gv)
    SEP (data_at Tsh ht4k_trc (ht4k_rc top bm) vrc; ht4k_wm Tsh top S vwm; data_at_ Tsh ht4k_tsnap vsnap;
      data_at Tsh (tarray tuchar 32) (map Vubyte key) vkey; mem_mgr gv; zero_page gv; ht4_minusp hka5_mp gv; FR)).
  - forward_call tt. Intros b2.
    forward.
    { hka5a_mod_tc. }
    rewrite (hka5a_mods b2 16), (hka5a_signed_mod b2 16) by rep_lia.
    hka5a_post. Exists (b2 mod 16). entailer!.
    unfold hka5_kind_ok. pose proof (Z.mod_pos_bound b2 16). lia.
  - forward. hka5a_post. Exists 16. entailer!.
    unfold hka5_kind_ok. lia.
  - Intros enc.
    pose proof (hka5a_enc_range _ _ H2) as He.
    forward.
    rewrite hka5a_add16.
    forward_if (temp KA._t'4 (Vlong (Int64.repr 0))).
    { forward. hka5a_post. entailer!.
      rewrite Int64.unsigned_repr in H3 by rep_lia. change (Int64.unsigned (Int64.repr 16)) with 16 in H3.
      replace enc with 16 by lia. reflexivity. }
    { forward. hka5a_post. entailer!. }
    forward.
    forward_call (tarray tuchar (16 + enc), gv).
    { simpl sizeof. rep_lia. }
    Intros pkt.
    forward_call (tarray tuchar 0, gv).
    { simpl sizeof. rep_lia. }
    Intros po.
    forward_call (tarray tuchar 0, gv).
    { simpl sizeof. rep_lia. }
    Intros rp.
    destruct (eq_dec pkt nullval) as [Hn | Hn].
    + subst pkt.
      forward_if (temp KA._t'8 (Vint Int.one)).
      { forward. hka5a_post. entailer!. }
      { exfalso. auto. }
      forward_if.
      * forward_call (tarray tuchar (16 + enc), nullval, gv).
        { rewrite (if_true _ (eq_dec nullval nullval)) by reflexivity. cancel. }
        forward_call (tarray tuchar 0, po, gv).
        forward_call (tarray tuchar 0, rp, gv).
        forward.
        hka5a_brk. unfold hka5_Brk, hka5_lv, hka5_fr. Exists top S. entailer!.
      * exfalso. apply Int.one_not_zero. assumption.
    + Intros.
      forward_if (temp KA._t'8 (Vint Int.zero)).
      { exfalso. subst. contradiction. }
      { forward_if (temp KA._t'8 (Vint Int.zero)).
        { exfalso. auto. }
        { forward. hka5a_post. entailer!. } }
      forward_if.
      { exfalso. auto. }
      forward. hka5a_post. Exists (b1 mod 4) enc pkt po rp. unfold hka5_mb. entailer!.
Qed.
