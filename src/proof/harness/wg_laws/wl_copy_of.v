(* wg_laws.h's copy_of(source, n): NULL (a failed malloc) or a new object holding the first n bytes of source.
   Only ae_fail_untouched uses it.  Proved for ANY compspecs with its only callee, malloc, as context, so that it
   moves into the law's program (asm_lib's asm_body_lift), like the helpers of wl_bodies.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require Import WgNoise.harness.ae_fail_untouched.code.

Local Open Scope Z_scope.

Section CopyOf.
Context {cs: compspecs}.

(* copy_of(source, n), source an object of the bytes bs, n <= |bs| *)
Definition copy_of_spec :=
  DECLARE _copy_of
  WITH sh: share, source: val, bs: list byte, n: Z, gv: globals
  PRE [ tptr tuchar, tulong ]
    PROP (readable_share sh; 0 <= n <= Zlength bs; Zlength bs <= Int64.max_unsigned)
    PARAMS (source; Vlong (Int64.repr n)) GLOBALS (gv)
    SEP (mem_mgr gv; data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) source)
  POST [ tptr tuchar ] EX p: val,
    PROP () RETURN (p)
    SEP (mem_mgr gv; data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) source;
         if eq_dec p nullval then emp
         else malloc_token Ews (tarray tuchar n) p *
              data_at Ews (tarray tuchar n) (map Vubyte (sublist 0 n bs)) p).

End CopyOf.

(* the body of copy_of, for any compspecs, with malloc as context *)
Definition wl_copy_of_ok : Prop :=
  forall cs: compspecs,
    @semax_body nil [(_quickproof_malloc, @malloc_spec' cs)] cs f_copy_of (@copy_of_spec cs).

Lemma wl_copy_of_holds : wl_copy_of_ok.
Proof.
  intro cs. start_function.
  forward_call (tarray tuchar n, gv).
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros p. forward.
  destruct (eq_dec p nullval) as [Hp|Hp].
  - (* malloc failed: the loop stops at once, the result is NULL *)
    subst p.
    forward_loop (PROP () LOCAL (temp _copy nullval; gvars gv; temp _source source; temp _n (Vlong (Int64.repr n)))
        SEP (mem_mgr gv; data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) source))
      break: (PROP () LOCAL (temp _copy nullval; gvars gv)
        SEP (mem_mgr gv; data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) source)).
    + entailer!.
    + forward_if (PROP () LOCAL (temp _t'2 (Vint Int.zero); temp _copy nullval; gvars gv; temp _source source;
                                 temp _n (Vlong (Int64.repr n)))
                  SEP (mem_mgr gv; data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) source)).
      * congruence.
      * forward. entailer!.
      * forward_if. { contradiction. } forward. entailer!.
    + forward. Exists nullval. entailer!.
  - (* the block: after i rounds its first i bytes are those of the source *)
    Intros.
    forward_loop (EX i: Z, PROP (0 <= i <= n)
        LOCAL (temp _i (Vlong (Int64.repr i)); temp _copy p; gvars gv; temp _source source;
               temp _n (Vlong (Int64.repr n)))
        SEP (mem_mgr gv; malloc_token Ews (tarray tuchar n) p;
             data_at Ews (tarray tuchar n) (map Vubyte (sublist 0 i bs) ++ Zrepeat Vundef (n - i)) p;
             data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) source))
      continue: (EX i: Z, PROP (0 <= i < n)
        LOCAL (temp _i (Vlong (Int64.repr i)); temp _copy p; gvars gv; temp _source source;
               temp _n (Vlong (Int64.repr n)))
        SEP (mem_mgr gv; malloc_token Ews (tarray tuchar n) p;
             data_at Ews (tarray tuchar n) (map Vubyte (sublist 0 (i + 1) bs) ++ Zrepeat Vundef (n - (i + 1))) p;
             data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) source))
      break: (PROP () LOCAL (temp _copy p; gvars gv)
        SEP (mem_mgr gv; malloc_token Ews (tarray tuchar n) p;
             data_at Ews (tarray tuchar n) (map Vubyte (sublist 0 n bs)) p;
             data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) source)).
    + Exists 0. entailer!. simpl app. rewrite data_at__eq. apply derives_refl.
    + Intros i.
      forward_if (PROP () LOCAL (temp _t'2 (Vint (if zlt i n then Int.one else Int.zero));
                                 temp _i (Vlong (Int64.repr i)); temp _copy p; gvars gv; temp _source source;
                                 temp _n (Vlong (Int64.repr n)))
        SEP (mem_mgr gv; malloc_token Ews (tarray tuchar n) p;
             data_at Ews (tarray tuchar n) (map Vubyte (sublist 0 i bs) ++ Zrepeat Vundef (n - i)) p;
             data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) source)).
      * forward. entailer!. destruct (zlt i n); reflexivity.
      * contradiction.
      * forward_if.
        -- destruct (zlt i n) as [Hi|Hi]; [| contradiction H2; reflexivity].
           forward.
           { rewrite Znth_map by lia. entailer!. pose proof (Byte.unsigned_range_2 (Znth i bs)); lia. }
           rewrite Znth_map by lia.
           forward.
           Exists i. entailer!.
           apply derives_refl'. f_equal.
           change (Vint (Int.repr (Byte.unsigned (Znth i bs)))) with (Vubyte (Znth i bs)).
           rewrite (sublist_split 0 i (i+1)) by lia. rewrite sublist_len_1 by lia. list_solve.
        -- destruct (zlt i n) as [Hi|Hi]; [exfalso; apply Int.one_not_zero; exact H2 |].
           forward.
           assert (i = n) by lia. subst i. rewrite Z.sub_diag. entailer!.
           rewrite Zrepeat_0, app_nil_r. cancel.
    + Intros i. forward. Exists (i + 1). entailer!.
    + forward. Exists p. rewrite if_false by auto. entailer!.
Qed.
