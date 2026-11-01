(* (law transport_keepalive): the bodies of rc_init, rc_take, rc_same (transport.h) and draw_steps
   (common.h) against ht4k_wm_spec.v: ht4o_rc_body.v (transport_order)
   by `sed -e s/transport_order/transport_keepalive/g -e s/ht4o_/ht4k_/g`, draw_nonce dropped (transport_order's only),
   draw_steps proved with the Gprog [nondet_size_spec] (the only function it calls; draw_u64 has no real
   specification in this law's program).  Templates: law counter's main (hcnt_piece3.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.harness.common4t.ht4_worlds.
Require Import WgNoise.proof.counter.counter_spec.
Require Import WgNoise.proof.harness.transport_keepalive.ht4k_wm_spec.
Require WgNoise.proof.harness.counter.hcnt_defs3.

#[local] Existing Instance W_transport_keepalive.
Local Open Scope Z_scope.

(* one more word of a copied array: positions [0, i) copied, the rest undefined *)
Lemma ht4k_upd_sublist_step {A} {d: Inhabitant A} (l: list A) (u: A) i n:
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

Lemma ht4k_body_rc_init : semax_body ht4k_V0 [] TO.f_rc_init ht4k_rc_init_spec.
Proof.
  start_function.
  forward.
  forward_for_simple_bound 128 (EX i: Z, PROP ()
    LOCAL (temp TO._c c)
    SEP (data_at sh ht4k_trc
           (Vlong (Int64.repr 0), (Vundef, Zrepeat (Vlong (Int64.repr 0)) i ++ Zrepeat Vundef (128 - i))) c))%assert.
  - entailer!.
  - forward. rewrite hcnt_defs3.upd_Znth_Zrepeat_step by lia. entailer!.
  - entailer!.
Qed.

Lemma ht4k_body_rc_take : semax_body ht4k_V0 [] TO.f_rc_take ht4k_rc_take_spec.
Proof.
  start_function.
  unfold ht4k_rc, ht4k_snap.
  set (bv := map (fun w => Vlong (Int64.repr w)) bm).
  assert (Lbv: Zlength bv = 128) by (unfold bv; rewrite Zlength_map; auto).
  forward. forward.
  forward_for_simple_bound 128 (EX i: Z, PROP ()
    LOCAL (temp TO._s s; temp TO._c c)
    SEP (data_at ssh ht4k_tsnap (Vlong (Int64.repr top), sublist 0 i bv ++ Zrepeat Vundef (128 - i)) s;
         data_at csh ht4k_trc (Vlong (Int64.repr top), (Vundef, bv)) c))%assert.
  - entailer!.
  - forward.
    { entailer!. unfold bv. rewrite Znth_map by lia. exact I. }
    forward.
    rewrite (ht4k_upd_sublist_step bv Vundef i 128) by lia.
    entailer!.
  - rewrite sublist_same by lia. rewrite Zrepeat_0, app_nil_r.
    entailer!.
Qed.

Lemma ht4k_repr64_inj a b : 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.repr a = Int64.repr b -> a = b.
Proof.
  intros Ha Hb E. apply (f_equal Int64.unsigned) in E. rewrite !Int64.unsigned_repr in E by lia. exact E.
Qed.

Lemma ht4k_sublist_snoc (l1 l2: list Z) i : 0 <= i < Zlength l1 -> Zlength l1 = Zlength l2 ->
  sublist 0 i l1 = sublist 0 i l2 -> Znth i l1 = Znth i l2 -> sublist 0 (i + 1) l1 = sublist 0 (i + 1) l2.
Proof.
  intros Hi HL E1 E2. rewrite (sublist_split 0 i (i + 1) l1), (sublist_split 0 i (i + 1) l2) by lia.
  rewrite !sublist_len_1 by lia. rewrite E1, E2. reflexivity.
Qed.

Lemma ht4k_body_rc_same : semax_body ht4k_V0 [] TO.f_rc_same ht4k_rc_same_spec.
Proof.
  start_function.
  unfold ht4k_rc, ht4k_snap. destruct H1 as [L1 F1]. destruct H2 as [L2 F2].
  rewrite Forall_forall in F1, F2.
  forward. forward.
  forward_if (top1 = top2).
  - forward. rewrite if_false by (intro; subst; contradiction). entailer!.
  - match goal with Hx: Int64.eq _ _ = true |- _ => apply Int64.same_if_eq, ht4k_repr64_inj in Hx; auto end.
    forward. entailer!.
  - Intros. subst top2.
    forward_for_simple_bound 128 (EX i: Z, PROP (sublist 0 i bm1 = sublist 0 i bm2)
      LOCAL (temp TO._s s; temp TO._c c)
      SEP (data_at ssh ht4k_tsnap (Vlong (Int64.repr top1), map (fun w => Vlong (Int64.repr w)) bm1) s;
           data_at csh ht4k_trc (Vlong (Int64.repr top1), (Vundef, map (fun w => Vlong (Int64.repr w)) bm2)) c))%assert.
    + entailer!.
    + cbv beta. Intros.
      forward. forward.
      forward_if.
      * forward. rewrite if_true by reflexivity. rewrite if_false. { entailer!. }
        intro E. subst bm2. apply H3. reflexivity.
      * match goal with Hx: Int64.eq _ _ = true |- _ => apply Int64.same_if_eq, ht4k_repr64_inj in Hx;
          [| apply F1, Znth_In; lia | apply F2, Znth_In; lia] end.
        forward. entailer!. apply ht4k_sublist_snoc; auto; lia.
    + forward. rewrite if_true by reflexivity. rewrite if_true. { entailer!. }
      rewrite !sublist_same in H1 by lia. exact H1.
Qed.

Lemma ht4k_body_draw_steps1 : semax_body ht4k_V0 [nondet_size_spec] TO.f_draw_steps ht4k_draw_steps_spec.
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

(* the target of this file *)
Lemma ht4k_rc_bodies :
  semax_body ht4k_V0 [] TO.f_rc_init ht4k_rc_init_spec /\
  semax_body ht4k_V0 [] TO.f_rc_take ht4k_rc_take_spec /\
  semax_body ht4k_V0 [] TO.f_rc_same ht4k_rc_same_spec /\
  semax_body ht4k_V0 [nondet_size_spec] TO.f_draw_steps ht4k_draw_steps_spec.
Proof. exact (conj ht4k_body_rc_init (conj ht4k_body_rc_take (conj ht4k_body_rc_same ht4k_body_draw_steps1))). Qed.
