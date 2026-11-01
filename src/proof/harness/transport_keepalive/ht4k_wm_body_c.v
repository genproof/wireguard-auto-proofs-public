(* (law transport_keepalive): the body of wm_commit (transport.h) against ht4k_wm_spec.v.  Template: law counter's main (hcnt_piece3.v), whose `if (ok) { malloc ... }`
   and pruning loop (cseg, cseg_extend, cseg_close of hcnt_defs3.v) are this function. *)
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

(* helpers (template: hcnt_defs3.v's cseg / csh / cseg_extend / cseg_close / acc_split, here for ht4k_twacc) *)

Lemma ht4k_wlist_local_facts S p: ht4k_wlist S p |-- !! (is_pointer_or_null p /\ (p = nullval <-> S = nil)).
Proof.
  destruct S as [|x S]; simpl; Intros; [entailer!; tauto|].
  Intros q. entailer!. split; intros; [subst; contradiction | discriminate].
Qed.
#[local] Hint Resolve ht4k_wlist_local_facts : saturate_local.

Lemma ht4k_wlist_valid_pointer S p: ht4k_wlist S p |-- valid_pointer p.
Proof. destruct S as [|x S]; simpl; Intros; [subst; auto with valid_pointer|]. Intros q. entailer!. Qed.
#[local] Hint Resolve ht4k_wlist_valid_pointer : valid_pointer.

(* a chain of cells: the cell c (share sh) points to the first node of K, the next field of each node of K
   points to the following one, the last one's next field is the cell l (not included) *)
Fixpoint ht4k_cseg (sh: share) (K: list Z) (c l: val) : mpred :=
  match K with
  | nil => !! (c = l) && emp
  | x :: K' => EX p: val,
      data_at sh (tptr ht4k_twacc) p c * malloc_token Ews ht4k_twacc p *
      field_at Ews ht4k_twacc [StructField TO._n] (Vlong (Int64.repr x)) p *
      ht4k_cseg Ews K' (field_address ht4k_twacc [StructField TO._next] p) l
  end.

(* the share of the current cell after the chain K *)
Definition ht4k_csh (sh: share) (K: list Z) : share := match K with nil => sh | _ => Ews end.

Lemma ht4k_csh_Ews K: ht4k_csh Ews K = Ews.
Proof. destruct K; reflexivity. Qed.

Lemma ht4k_cseg_extend sh K c l p x:
  ht4k_cseg sh K c l * data_at (ht4k_csh sh K) (tptr ht4k_twacc) p l * malloc_token Ews ht4k_twacc p *
  field_at Ews ht4k_twacc [StructField TO._n] (Vlong (Int64.repr x)) p |--
  ht4k_cseg sh (K ++ [x]) c (field_address ht4k_twacc [StructField TO._next] p).
Proof.
  revert sh c. induction K as [|y K IH]; intros sh c; simpl.
  - Intros. subst. Exists p. entailer!.
  - Intros s. Exists s. specialize (IH Ews (field_address ht4k_twacc [StructField TO._next] s)).
    rewrite ht4k_csh_Ews in IH. sep_apply IH. entailer!.
Qed.

Lemma ht4k_cseg_close sh K R c l q:
  ht4k_cseg sh K c l * data_at (ht4k_csh sh K) (tptr ht4k_twacc) q l * ht4k_wlist R q |--
  EX p: val, data_at sh (tptr ht4k_twacc) p c * ht4k_wlist (K ++ R) p.
Proof.
  revert sh c. induction K as [|y K IH]; intros sh c; simpl.
  - Intros. subst. Exists q. entailer!.
  - Intros s. specialize (IH Ews (field_address ht4k_twacc [StructField TO._next] s)).
    rewrite ht4k_csh_Ews in IH. sep_apply IH. Intros p.
    Exists s p. unfold_data_at (data_at Ews ht4k_twacc _ s).
    rewrite (field_at_data_at Ews ht4k_twacc [StructField TO._next]).
    entailer!.
Qed.

Lemma ht4k_acc_split x r q:
  data_at Ews ht4k_twacc (Vlong (Int64.repr x), r) q =
  (field_at Ews ht4k_twacc [StructField TO._n] (Vlong (Int64.repr x)) q *
   data_at Ews (tptr ht4k_twacc) r (field_address ht4k_twacc [StructField TO._next] q))%logic.
Proof.
  unfold_data_at (data_at _ _ _ q). rewrite (field_at_data_at Ews ht4k_twacc [StructField TO._next]).
  reflexivity.
Qed.

Lemma ht4k_body_wm_commit : semax_body ht4k_V0 ht4k_G_mem TO.f_wm_commit ht4k_wm_commit_spec.
Proof.
  start_function.
  unfold ht4k_wm. Intros p.
  forward_call (ht4k_twacc, gv).
  Intros a.
  if_tac.
  { subst a. forward_if.
    - forward. Exists false. unfold ht4k_wm. Exists p. entailer!.
    - exfalso. match goal with Hx: ?x <> ?x |- _ => apply Hx; reflexivity end. }
  Intros.
  forward_if.
  { exfalso. subst a. contradiction. }
  forward. forward. forward. forward. forward.
  assert (Hn1: 0 <= n + 1 <= CNT_R) by lia.
  forward_if (PROP ()
    LOCAL (temp TO._a a; gvars gv; temp TO._m m; temp TO._n (Vlong (Int64.repr n)))
    SEP (mem_mgr gv; malloc_token Ews ht4k_twacc a; data_at Ews ht4k_twacc (Vlong (Int64.repr n), p) a;
         data_at sh ht4k_twm (a, Vlong (Int64.repr (Z.max top (n + 1)))) m; ht4k_wlist S p)).
  { forward. entailer!.
    rewrite !Int64.unsigned_repr in H4 by (rewrite hcnt_defs3.CNT_R_val in *; rep_lia).
    rewrite Z.max_r by lia. cancel. }
  { forward. entailer!.
    rewrite !Int64.unsigned_repr in H4 by (rewrite hcnt_defs3.CNT_R_val in *; rep_lia).
    rewrite Z.max_l by lia. cancel. }
  remember (Z.max top (n + 1)) as top' eqn:Etop'.
  assert (Htop': 0 <= top' <= CNT_R) by lia.
  assert (HnS: forall x, In x (n :: S) -> 0 <= x < CNT_R).
  { intros x [Hx|Hx]; [subst; lia | rewrite Forall_forall in H1; auto]. }
  unfold_data_at (data_at sh ht4k_twm _ m).
  rewrite (field_at_data_at sh ht4k_twm [StructField TO._set]).
  forward.
  forward_loop (EX K: list Z, EX R: list Z, EX l: val, EX q: val,
    PROP (ht4k_prune top' (n :: S) = K ++ ht4k_prune top' R; forall x, In x R -> In x (n :: S))
    LOCAL (temp TO._l l; gvars gv; temp TO._m m; temp TO._n (Vlong (Int64.repr n)))
    SEP (mem_mgr gv; field_at sh ht4k_twm [StructField TO._top] (Vlong (Int64.repr top')) m;
         ht4k_cseg sh K (field_address ht4k_twm [StructField TO._set] m) l;
         data_at (ht4k_csh sh K) (tptr ht4k_twacc) q l; ht4k_wlist R q))%assert
  break: (EX p'': val,
    PROP ()
    LOCAL (gvars gv; temp TO._m m; temp TO._n (Vlong (Int64.repr n)))
    SEP (mem_mgr gv; field_at sh ht4k_twm [StructField TO._top] (Vlong (Int64.repr top')) m;
         data_at sh (tptr ht4k_twacc) p'' (field_address ht4k_twm [StructField TO._set] m);
         ht4k_wlist (ht4k_prune top' (n :: S)) p''))%assert.
  { Exists (@nil Z) (n :: S) (field_address ht4k_twm [StructField TO._set] m) a.
    simpl ht4k_cseg. simpl ht4k_wlist. Exists p. entailer!. }
  { Intros K R l q.
    assert (Hsh: writable_share (ht4k_csh sh K)) by (destruct K; simpl; auto).
    forward.
    forward_if.
    2:{ forward. assert_PROP (R = []) by (entailer!; tauto). subst q R.
        sep_apply (ht4k_cseg_close sh K [] (field_address ht4k_twm [StructField TO._set] m) l nullval).
        Intros p''. Exists p''.
        rewrite app_nil_r. change (ht4k_prune top' []) with (@nil Z) in H4. rewrite app_nil_r in H4. rewrite H4. entailer!. }
    destruct R as [|x R]. { simpl ht4k_wlist. Intros. subst q. contradiction. }
    simpl ht4k_wlist. Intros q'.
    forward. forward. forward.
    assert (Hx: 0 <= x < CNT_R) by (apply HnS; apply H5; left; auto).
    forward_if.
    - rewrite !add64_repr in H7.
      rewrite !Int64.unsigned_repr in H7 by (rewrite hcnt_defs3.CNT_R_val in *; rep_lia).
      forward. forward. forward.
      forward_call (ht4k_twacc, q, gv).
      { rewrite if_false by (intro; subst; contradiction). entailer!. }
      Exists K R l q'. entailer!. split.
      + rewrite H4. unfold ht4k_prune, hcnt_defs3.hcnt_prune. simpl. unfold CNT_W.
        match goal with |- context [?t <=? x + 1 + 8128] => replace (t <=? x + 1 + 8128) with false by (symmetry; apply Z.leb_gt; lia) end. auto.
      + intros y Hy. apply H5. right. auto.
    - rewrite !add64_repr in H7.
      rewrite !Int64.unsigned_repr in H7 by (rewrite hcnt_defs3.CNT_R_val in *; rep_lia).
      forward. forward.
      Exists (K ++ [x]) R (field_address ht4k_twacc [StructField TO._next] q) q'. entailer!.
      { split.
        - rewrite H4, <- app_assoc. f_equal. unfold ht4k_prune, hcnt_defs3.hcnt_prune. simpl. unfold CNT_W.
          match goal with |- context [?t <=? x + 1 + 8128] => replace (t <=? x + 1 + 8128) with true by (symmetry; apply Z.leb_le; lia) end. reflexivity.
        - intros y Hy. apply H5. right. auto. }
      { rewrite ht4k_acc_split.
        replace (ht4k_csh sh (K ++ [x])) with Ews by (destruct K; reflexivity).
        sep_apply (ht4k_cseg_extend sh K (field_address ht4k_twm [StructField TO._set] m) l q x). cancel. } }
  Intros p''. forward. Exists true. unfold ht4k_wm. Exists p''. entailer!.
  unfold_data_at (data_at sh ht4k_twm _ m). rewrite (field_at_data_at sh ht4k_twm [StructField TO._set]).
  cancel.
Qed.
