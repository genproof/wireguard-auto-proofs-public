(* (law transport_order): the bodies of wm_init, wm_accepts, wm_free (transport.h) against
   ht4o_wm_spec.v.  Template: law counter's main (hcnt_piece3.v), whose
   membership and free loops are these functions. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.harness.common4t.ht4_worlds.
Require Import WgNoise.proof.counter.counter_spec.
Require Import WgNoise.proof.harness.transport_order.ht4o_wm_spec.
Require WgNoise.proof.harness.counter.hcnt_defs3.

#[local] Existing Instance W_transport_order.
Local Open Scope Z_scope.

(* helpers (template: hcnt_defs3.v's accs / accseg, here for ht4o_wlist) *)

(* a segment of nodes from p up to q (excluded) *)
Fixpoint ht4o_wseg (K: list Z) (p q: val) : mpred :=
  match K with
  | nil => !! (p = q) && emp
  | x :: K' => EX r: val,
      malloc_token Ews ht4o_twacc p * data_at Ews ht4o_twacc (Vlong (Int64.repr x), r) p * ht4o_wseg K' r q
  end.

Lemma ht4o_wlist_local_facts S p: ht4o_wlist S p |-- !! (is_pointer_or_null p /\ (p = nullval <-> S = nil)).
Proof.
  destruct S as [|x S]; simpl; Intros; [entailer!; tauto|].
  Intros q. entailer!. split; intros; [subst; contradiction | discriminate].
Qed.
#[local] Hint Resolve ht4o_wlist_local_facts : saturate_local.

Lemma ht4o_wlist_valid_pointer S p: ht4o_wlist S p |-- valid_pointer p.
Proof. destruct S as [|x S]; simpl; Intros; [subst; auto with valid_pointer|]. Intros q. entailer!. Qed.
#[local] Hint Resolve ht4o_wlist_valid_pointer : valid_pointer.

Lemma ht4o_wseg_app K x p q r:
  ht4o_wseg K p q * malloc_token Ews ht4o_twacc q * data_at Ews ht4o_twacc (Vlong (Int64.repr x), r) q |--
  ht4o_wseg (K ++ [x]) p r.
Proof.
  revert p. induction K as [|y K IH]; intros p; simpl.
  - Intros. subst. Exists r. entailer!.
  - Intros s. Exists s. sep_apply (IH s). entailer!.
Qed.

Lemma ht4o_wseg_wlist K R p q: ht4o_wseg K p q * ht4o_wlist R q |-- ht4o_wlist (K ++ R) p.
Proof.
  revert p. induction K as [|y K IH]; intros p; simpl.
  - Intros. subst. entailer!.
  - Intros s. Exists s. sep_apply (IH s). entailer!.
Qed.

Lemma ht4o_existsb_snoc n K x: existsb (Z.eqb n) (K ++ [x]) = orb (existsb (Z.eqb n) K) (n =? x).
Proof. rewrite existsb_app. simpl. rewrite orb_false_r. reflexivity. Qed.

Lemma ht4o_body_wm_init : semax_body ht4o_V0 [] TO.f_wm_init ht4o_wm_init_spec.
Proof.
  start_function. forward. forward.
  unfold ht4o_wm. Exists nullval. simpl ht4o_wlist. entailer!.
Qed.

Lemma ht4o_body_wm_accepts : semax_body ht4o_V0 [] TO.f_wm_accepts ht4o_wm_accepts_spec.
Proof.
  start_function.
  unfold ht4o_wm. Intros p.
  forward_loop (EX K: list Z, EX R: list Z, EX a: val,
    PROP (S = K ++ R; existsb (Z.eqb n) K = false)
    LOCAL (temp TO._a a; temp TO._m m; temp TO._n (Vlong (Int64.repr n)))
    SEP (data_at sh ht4o_twm (p, Vlong (Int64.repr top)) m; ht4o_wseg K p a; ht4o_wlist R a))%assert
  continue: (EX K: list Z, EX x: Z, EX R: list Z, EX a: val, EX q: val,
    PROP (S = K ++ x :: R; existsb (Z.eqb n) (K ++ [x]) = false)
    LOCAL (temp TO._a a; temp TO._m m; temp TO._n (Vlong (Int64.repr n)))
    SEP (data_at sh ht4o_twm (p, Vlong (Int64.repr top)) m; ht4o_wseg K p a; malloc_token Ews ht4o_twacc a;
         data_at Ews ht4o_twacc (Vlong (Int64.repr x), q) a; ht4o_wlist R q))%assert
  break: (
    PROP (existsb (Z.eqb n) S = false)
    LOCAL (temp TO._m m; temp TO._n (Vlong (Int64.repr n)))
    SEP (data_at sh ht4o_twm (p, Vlong (Int64.repr top)) m; ht4o_wlist S p))%assert.
  { forward. Exists (@nil Z) S p. simpl ht4o_wseg. entailer!. }
  { Intros K R a.
    forward_if.
    2:{ forward. subst a. destruct R as [|x R].
        - rewrite app_nil_r in *. subst S. sep_apply (ht4o_wseg_wlist K [] p nullval). rewrite app_nil_r.
          entailer!.
        - simpl ht4o_wlist. Intros q. entailer!. }
    destruct R as [|x R]. { simpl ht4o_wlist. Intros. subst a. simpl in *. contradiction. }
    simpl ht4o_wlist. Intros q.
    forward.
    forward_if.
    - forward.
      assert (Hx: 0 <= x <= Int64.max_unsigned)
        by (rewrite Forall_app in H1; destruct H1 as [_ H1]; inv H1; auto).
      rewrite hcnt_defs3.int64_eq_repr in H5 by auto. apply Z.eqb_eq in H5. subst x.
      replace (cnt_ok top (K ++ n :: R) n) with false.
      2:{ unfold cnt_ok. rewrite existsb_app. simpl. rewrite Z.eqb_refl, orb_true_r. simpl.
          rewrite andb_false_r. reflexivity. }
      unfold ht4o_wm. Exists p. entailer!.
      eapply derives_trans; [|apply (ht4o_wseg_wlist K (n :: R) p a)]. simpl ht4o_wlist. Exists q. cancel.
    - forward. Exists K x R a q. entailer!.
      rewrite ht4o_existsb_snoc, H3. simpl. apply Z.eqb_neq. intro; subst; contradiction. }
  { Intros K x R a q. forward. Exists (K ++ [x]) R q. entailer!.
    - rewrite <- app_assoc. auto.
    - sep_apply (ht4o_wseg_app K x p a q). entailer!. }
  (* return m->top < M_R + 1 && n < M_R && n + 1 + M_W >= m->top *)
  Intros. forward.
  forward_if (temp TO._t'1 (Val.of_bool ((top <? CNT_R + 1) && (n <? CNT_R)))).
  { forward. entailer!.
    rewrite hcnt_defs3.u64_R1, Int64.unsigned_repr in H3 by lia.
    replace (top <? CNT_R + 1) with true by (symmetry; apply Z.ltb_lt; lia). simpl andb.
    unfold Int64.cmpu, Int64.ltu. rewrite hcnt_defs3.u64_R, Int64.unsigned_repr by lia.
    destruct (zlt n CNT_R), (Z.ltb_spec n CNT_R); auto; lia. }
  { match type of H3 with _ >= Int64.unsigned ?e =>
      let E := fresh in assert (E: Int64.unsigned e = CNT_R + 1) by reflexivity; rewrite E in H3 end.
    rewrite Int64.unsigned_repr in H3 by lia.
    forward. entailer!.
    replace (top <? CNT_R + 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
  forward_if (temp TO._t'2 (Val.of_bool ((top <? CNT_R + 1) && (n <? CNT_R) && (top <=? n + 1 + CNT_W)))).
  { forward. forward. entailer!.
    change 18446744073709543487 with (CNT_R + 1) in H3.
    destruct ((top <? CNT_R + 1) && (n <? CNT_R))%bool eqn:E; [|inv H3].
    rewrite andb_true_iff, !Z.ltb_lt in E. destruct E as [E1 E2].
    replace (top <? CNT_R + 1) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (n <? CNT_R) with true by (symmetry; apply Z.ltb_lt; lia). simpl andb.
    unfold Int64.cmpu.
    rewrite hcnt_defs3.ltu_repr by (rewrite hcnt_defs3.CNT_R_val in *; rep_lia). unfold CNT_W.
    destruct (Z.ltb_spec (n + 1 + 8128) top), (Z.leb_spec top (n + 1 + 8128)); auto; lia. }
  { forward. entailer!. change 18446744073709543487 with (CNT_R + 1) in *.
    destruct ((top <? CNT_R + 1) && (n <? CNT_R))%bool; [inv H3 | reflexivity]. }
  forward.
  unfold ht4o_wm. Exists p. entailer!.
  unfold cnt_ok. rewrite H2. simpl negb. rewrite andb_true_r.
  destruct ((top <? CNT_R + 1) && (n <? CNT_R) && (top <=? n + 1 + CNT_W))%bool; reflexivity.
Qed.

Lemma ht4o_body_wm_free : semax_body ht4o_V0 ht4o_G_mem TO.f_wm_free ht4o_wm_free_spec.
Proof.
  start_function.
  unfold ht4o_wm. Intros p.
  forward_loop (EX S': list Z, EX p': val,
    PROP ()
    LOCAL (temp TO._m m; gvars gv)
    SEP (data_at sh ht4o_twm (p', Vlong (Int64.repr top)) m; ht4o_wlist S' p'; mem_mgr gv))%assert
  break: (PROP () LOCAL (temp TO._m m; gvars gv)
    SEP (data_at sh ht4o_twm (nullval, Vlong (Int64.repr top)) m; mem_mgr gv))%assert.
  { Exists S p. entailer!. }
  { Intros S' p'. forward. forward_if.
    2:{ forward. assert_PROP (S' = nil) by (entailer!; tauto). subst. simpl ht4o_wlist. entailer!. }
    destruct S' as [|x S']. { simpl ht4o_wlist. Intros. subst p'. contradiction. }
    simpl ht4o_wlist. Intros q.
    forward. forward. forward.
    forward_call (ht4o_twacc, p', gv).
    { rewrite if_false by (intro; subst; contradiction). entailer!. }
    forward. Exists S' q. entailer!. }
  forward.
Qed.

(* the target of this file *)
Lemma ht4o_wm_bodies_a :
  semax_body ht4o_V0 [] TO.f_wm_accepts ht4o_wm_accepts_spec /\
  semax_body ht4o_V0 ht4o_G_mem TO.f_wm_free ht4o_wm_free_spec.
Proof. exact (conj ht4o_body_wm_accepts ht4o_body_wm_free). Qed.
