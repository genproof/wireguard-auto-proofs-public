(* (law transport_order): the bodies of rc_init, rc_take, rc_same (transport.h), draw_steps
   and draw_nonce (transport_order.c) against ht4o_wm_spec.v.  Templates:
   law counter's main (hcnt_piece3.v: the counter's init loop, draw_steps, the nonce switch). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.harness.common4t.ht4_worlds.
Require Import WgNoise.proof.counter.counter_spec.
Require Import WgNoise.proof.harness.transport_order.ht4o_wm_spec.

#[local] Existing Instance W_transport_order.
Local Open Scope Z_scope.

(* one more word of a copied array: positions [0, i) copied, the rest undefined *)
Lemma ht4o_upd_sublist_step {A} {d: Inhabitant A} (l: list A) (u: A) i n:
  0 <= i < n -> Zlength l = n ->
  upd_Znth i (sublist 0 i l ++ Zrepeat u (n - i)) (Znth i l) = sublist 0 (i + 1) l ++ Zrepeat u (n - (i + 1)).
Proof.
  intros H Hl.
  rewrite upd_Znth_app2 by (rewrite Zlength_sublist, Zlength_Zrepeat by lia; lia).
  rewrite Zlength_sublist by lia. replace (i - (i - 0)) with 0 by lia.
  unfold Zrepeat. replace (Z.to_nat (n - i)) with (S (Z.to_nat (n - (i + 1)))) by lia.
  change (repeat u (S ?k)) with (u :: repeat u k). rewrite upd_Znth0.
  rewrite (sublist_split 0 i (i + 1)) by lia. rewrite sublist_len_1 by lia.
  rewrite <- app_assoc. reflexivity.
Qed.

Lemma ht4o_body_rc_init : semax_body ht4o_V0 [] TO.f_rc_init ht4o_rc_init_spec.
Proof.
  start_function.
  forward.
  forward_for_simple_bound 128 (EX i: Z, PROP ()
    LOCAL (temp TO._c c)
    SEP (data_at sh ht4o_trc
           (Vlong (Int64.repr 0), (Vundef, Zrepeat (Vlong (Int64.repr 0)) i ++ Zrepeat Vundef (128 - i))) c))%assert.
  - entailer!.
  - forward. rewrite hcnt_defs3.upd_Znth_Zrepeat_step by lia. entailer!.
  - entailer!.
Qed.

Lemma ht4o_body_rc_take : semax_body ht4o_V0 [] TO.f_rc_take ht4o_rc_take_spec.
Proof.
  start_function.
  unfold ht4o_rc, ht4o_snap.
  forward. forward.
  forward_for_simple_bound 128 (EX i: Z, PROP ()
    LOCAL (temp TO._s s; temp TO._c c)
    SEP (data_at ssh ht4o_tsnap
           (Vlong (Int64.repr top), sublist 0 i (map (fun w => Vlong (Int64.repr w)) bm) ++ Zrepeat Vundef (128 - i)) s;
         data_at csh ht4o_trc (Vlong (Int64.repr top), (Vundef, map (fun w => Vlong (Int64.repr w)) bm)) c))%assert.
  - entailer!.
  - forward. forward.
    entailer!.
    replace (Vlong (Int64.repr (Znth i bm))) with (Znth i (map (fun w => Vlong (Int64.repr w)) bm))
      by (rewrite Znth_map by lia; reflexivity).
    rewrite ht4o_upd_sublist_step by (rewrite ?Zlength_map; lia). cancel.
  - entailer!. rewrite sublist_same by (rewrite ?Zlength_map; lia). rewrite app_nil_r. cancel.
Qed.

Lemma ht4o_body_rc_same : semax_body ht4o_V0 [] TO.f_rc_same ht4o_rc_same_spec.
Proof.
  start_function.
  destruct H1 as [Hl1 Hw1], H2 as [Hl2 Hw2].
  unfold ht4o_rc, ht4o_snap.
  forward. forward.
  forward_if (PROP (top1 = top2)
    LOCAL (temp TO._s s; temp TO._c c)
    SEP (data_at ssh ht4o_tsnap (Vlong (Int64.repr top1), map (fun w => Vlong (Int64.repr w)) bm1) s;
         data_at csh ht4o_trc (Vlong (Int64.repr top2), (Vundef, map (fun w => Vlong (Int64.repr w)) bm2)) c)).
  - forward. destruct (Z.eq_dec top1 top2). { subst. contradiction. } entailer!.
  - forward. entailer!. apply repr_inj_unsigned64; auto. apply Int64.same_if_eq; auto.
  - Intros. subst top2.
    forward_for_simple_bound 128 (EX i: Z, PROP (sublist 0 i bm1 = sublist 0 i bm2)
      LOCAL (temp TO._s s; temp TO._c c)
      SEP (data_at ssh ht4o_tsnap (Vlong (Int64.repr top1), map (fun w => Vlong (Int64.repr w)) bm1) s;
           data_at csh ht4o_trc (Vlong (Int64.repr top1), (Vundef, map (fun w => Vlong (Int64.repr w)) bm2)) c))%assert.
    + entailer!.
    + cbv beta. Intros. forward. forward.
      assert (B1: 0 <= Znth i bm1 <= Int64.max_unsigned) by (apply (proj1 (Forall_Znth _ _) Hw1); lia).
      assert (B2: 0 <= Znth i bm2 <= Int64.max_unsigned) by (apply (proj1 (Forall_Znth _ _) Hw2); lia).
      forward_if (PROP (Znth i bm1 = Znth i bm2)
        LOCAL (temp TO._i (Vlong (Int64.repr i)); temp TO._s s; temp TO._c c)
        SEP (data_at ssh ht4o_tsnap (Vlong (Int64.repr top1), map (fun w => Vlong (Int64.repr w)) bm1) s;
             data_at csh ht4o_trc (Vlong (Int64.repr top1), (Vundef, map (fun w => Vlong (Int64.repr w)) bm2)) c)).
      * forward. destruct (Z.eq_dec top1 top1); [|contradiction].
        destruct (list_eq_dec Z.eq_dec bm1 bm2). { subst. contradiction. } entailer!.
      * forward. entailer!. apply repr_inj_unsigned64; auto. apply Int64.same_if_eq; auto.
      * Intros. entailer!.
        rewrite (sublist_split 0 i (i + 1) bm1), (sublist_split 0 i (i + 1) bm2) by lia.
        rewrite !sublist_len_1 by lia. congruence.
    + forward.
      match goal with Hs: sublist 0 128 bm1 = sublist 0 128 bm2 |- _ =>
        rewrite !sublist_same in Hs by lia; subst bm2 end.
      destruct (Z.eq_dec top1 top1); [|contradiction].
      destruct (list_eq_dec Z.eq_dec bm1 bm1); [|contradiction]. entailer!.
Qed.

Lemma ht4o_body_draw_steps : semax_body ht4o_V0 ht4o_G_draw TO.f_draw_steps ht4o_draw_steps_spec.
Proof.
  start_function.
  forward_call tt. Intros n.
  forward_if (temp TO._t'2 (Vlong (Int64.repr n))).
  { forward. entailer!. }
  { exfalso. unfold Int64.ltu in H0. rewrite (Int64.unsigned_repr n) in H0 by rep_lia.
    change (Int64.unsigned (Int64.repr (-1))) with Int64.max_unsigned in H0.
    if_tac in H0. lia. discriminate. }
  forward. Exists n. entailer!.
Qed.

Lemma ht4o_body_draw_nonce : semax_body ht4o_V0 ht4o_G_draw TO.f_draw_nonce ht4o_draw_nonce_spec.
Proof.
  start_function.
  forward_call tt. Intros b.
  apply (semax_switch_PQR (b mod 5)).
  - reflexivity.
  - entailer!. destruct H2 as [_ H2]. apply (f_equal Int.signed) in H2.
    rewrite Int.signed_repr in H2 by rep_lia. rewrite Int.signed_mone in H2. lia.
  - entailer!. unfold Int.mods. rewrite !Int.signed_repr by rep_lia.
    rewrite Z.rem_mod_nonneg by lia. reflexivity.
  - rewrite Int.unsigned_repr by (pose proof (Z.mod_pos_bound b 5); rep_lia).
    assert (Hb: b mod 5 = 0 \/ b mod 5 = 1 \/ b mod 5 = 2 \/ b mod 5 = 3 \/ b mod 5 = 4)
      by (pose proof (Z.mod_pos_bound b 5); lia).
    destruct Hb as [Hb|[Hb|[Hb|[Hb|Hb]]]]; rewrite Hb; simpl seq_of_labeled_statement.
    5: forward_call tt; Intros x; forward; Exists x; entailer!.
    all: forward_call tt; Intros x; forward;
      match goal with |- context [Vlong (Int64.repr ?E) = _] => Exists (Int64.unsigned (Int64.repr E)) end;
      entailer!; rewrite Int64.repr_unsigned; reflexivity.
Qed.

(* the target of this file *)
Lemma ht4o_rc_bodies :
  semax_body ht4o_V0 [] TO.f_rc_init ht4o_rc_init_spec /\
  semax_body ht4o_V0 [] TO.f_rc_take ht4o_rc_take_spec /\
  semax_body ht4o_V0 [] TO.f_rc_same ht4o_rc_same_spec /\
  semax_body ht4o_V0 ht4o_G_draw TO.f_draw_nonce ht4o_draw_nonce_spec.
Proof.
  exact (conj ht4o_body_rc_init (conj ht4o_body_rc_take (conj ht4o_body_rc_same ht4o_body_draw_nonce))).
Qed.
