(* law transport_order (harness/transport_order.c): main's context, the cut of its
   body into segments and the states between them.

   main is proved against a SMALL context (ht4o_G0: its callees' specifications, the byte-only ones at main's world
   W_transport_order) and lifted into the whole program by the assembly (asm_lib.asm_body_lift).

   main = last_nonce = 0; have_auth = 0; rc_init(&rc); wm_init(&wm); nondet_bytes(key, 32); steps = draw_steps();
          for (i = 0; i < steps; i++) BODY;  wm_free(&wm); return 0;
   BODY (22 statements) is cut into four segments:
     L1 = 0..8   kind = nondet_u8() % 4; L = draw_size(); if (L > PTRDIFF_MAX - 32) break; enc_len; tot;
                 pkt = malloc(tot); pt_out = malloc(..); ref_pt = malloc(..); if (one is NULL) { 3 frees; break; }
     L2 = 9..13  nonce = (kind == 2 && have_auth) ? last_nonce : draw_nonce(wm.top); the 16-byte header
                 (le32_store x2, le64_store); the ciphertext: kinds 0/1/2 an authentic packet (pt = malloc(L), NULL:
                 3 frees + break; nondet_bytes(pt, L); chacha20poly1305_encrypt(pkt + 16, pt, L, NULL, 0, nonce, key);
                 free(pt); kind 1 flips one byte), kind 3 random bytes
     L3 = 14..17 rc_take(&snap, &rc); ok = chacha20poly1305_decrypt(pt_out, pkt + 16, enc_len, NULL, 0, nonce, key);
                 ref_ok = ref_aead_decrypt(ref_pt, ...same...); CHECK(ok == ref_ok)
     L4 = 18..21 if (!ok) CHECK(rc_same(&snap, &rc)); else { pred = wm_accepts(&wm, nonce);
                 r = wg_counter_validate(&rc, nonce); CHECK(r == pred); if (r) { CHECK(bytes_eq(pt_out, ref_pt,
                 enc_len - 16)); if (!wm_commit(&wm, nonce)) { 3 frees; break; } } CHECK(rc.counter == wm.top);
                 have_auth = 1; last_nonce = nonce; }  free(pkt); free(pt_out); free(ref_pt);
   The loop state: the replay counter rc = (top, bm), the shadow model wm = (top, S) with the counter piece's
   invariant cnt_inv top S bm (counter_spec.v: S plays the role of the accepted list L, pruned as hcnt_prune),
   have_auth, last_nonce. *)
Require WgNoise.proof.assembly.asm_env.
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
Require Export WgNoise.proof.harness.transport_order.ht4o_wm_spec.
Require WgNoise.contracts.x_transport_order.

#[local] Existing Instance W_transport_order.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* main's specification and context                                       *)
(* ---------------------------------------------------------------------- *)

Definition ht4o_mp : ident := TO._x_transport_order__minusp.

Definition ht4o_post : (ident -> val) -> environ -> mpred := fun _ _ => TT.

Definition ht4o_main_spec : ident * funspec :=
  (TO._main, QPmain_spec_ext' WgNoise.contracts.x_transport_order.whole_prog tt ht4o_post).

(* the varspecs of the whole program (literal) *)
Definition ht4o_V : varspecs :=
  ltac:(let x := eval vm_compute in (QPvarspecs WgNoise.contracts.x_transport_order.whole_prog) in exact x).

(* main's callees, in the order of their first call *)
Definition ht4o_G0 : funspecs :=
  [ht4o_rc_init_spec; ht4o_wm_init_spec; @asm_env.nondet_bytes_spec W_transport_order; ht4o_draw_steps_spec;
   nondet_u8_spec; ht4_draw_size_spec;
   (_quickproof_malloc, @malloc_spec' W_transport_order); (_quickproof_free, @free_spec' W_transport_order);
   ht4o_draw_nonce_spec; @ht4_le32_store_spec W_transport_order; nondet_u32_spec;
   @ht4_le64_store_spec W_transport_order; @ht4_encrypt_spec W_transport_order; nondet_size_spec;
   ht4o_rc_take_spec; @ht4_decrypt_spec W_transport_order; ref_aead_decrypt_spec_n W_transport_order ht4o_mp;
   ht4_check_failed_spec; ht4o_rc_same_spec; ht4o_wm_accepts_spec; wg_counter_validate_spec;
   @ht4_bytes_eq_spec W_transport_order; ht4o_wm_commit_spec; ht4o_wm_free_spec].

Definition ht4o_Delta : tycontext := func_tycontext TO.f_main ht4o_V ht4o_G0 [].

Definition ht4o_R (gv: globals) : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (ht4o_post gv)) (stackframe_of TO.f_main).

(* ---------------------------------------------------------------------- *)
(* Cutting statement lists (as law replay's hrp3 lemmas)                    *)
(* ---------------------------------------------------------------------- *)

Fixpoint ht4o_seqs (l: list statement) (rest: statement) : statement :=
  match l with [] => rest | a :: l' => Ssequence a (ht4o_seqs l' rest) end.

Fixpoint ht4o_seql (l: list statement) : statement :=
  match l with [] => Sskip | [a] => a | a :: l' => Ssequence a (ht4o_seql l') end.

Fixpoint ht4o_flat (s: statement) : list statement :=
  match s with Ssequence a b => a :: ht4o_flat b | _ => [s] end.

Lemma ht4o_unfold_seql l : l <> [] ->
  unfold_Ssequence (ht4o_seql l) = concat (map unfold_Ssequence l).
Proof.
  induction l as [|a l IH]; intros Hl; [congruence |].
  destruct l as [|b l']; simpl.
  - rewrite app_nil_r; reflexivity.
  - simpl in IH. rewrite IH by discriminate. reflexivity.
Qed.

Lemma ht4o_unfold_seqs l rest :
  unfold_Ssequence (ht4o_seqs l rest) = concat (map unfold_Ssequence l) ++ unfold_Ssequence rest.
Proof.
  induction l as [|a l IH]; simpl; [reflexivity |]. rewrite IH, app_assoc. reflexivity.
Qed.

Lemma ht4o_overridePost2 Q Q' R : overridePost Q (overridePost Q' R) = overridePost Q R.
Proof. destruct R; reflexivity. Qed.

Lemma ht4o_semax_cut {Espec: OracleKind} {cs: compspecs} Delta P Q R l rest :
  l <> [] ->
  semax Delta P (ht4o_seql l) (overridePost Q R) -> semax Delta Q rest R ->
  semax Delta P (ht4o_seqs l rest) R.
Proof.
  intros Hl H1 H2.
  apply (semax_unfold_Ssequence (Ssequence (ht4o_seql l) rest)).
  - simpl. rewrite ht4o_unfold_seql, ht4o_unfold_seqs by auto. reflexivity.
  - eapply semax_seq; eauto.
Qed.

(* main's body is  S1; return 0  with S1 = these 9 statements (the loop is statement 6, the last a return) *)
Definition ht4o_stmts : list statement :=
  ltac:(let x := eval cbv beta iota delta [ht4o_flat TO.f_main fn_body] in
        (match fn_body TO.f_main with Ssequence s _ => ht4o_flat s | s => [s] end) in exact x).

Lemma ht4o_stmts_length : length ht4o_stmts = 9%nat.
Proof. reflexivity. Qed.

Definition ht4o_l (i n: nat) : list statement := firstn n (skipn i ht4o_stmts).

Definition ht4o_loop := ltac:(let x := eval cbv beta iota delta [nth ht4o_stmts] in (nth 6 ht4o_stmts Sskip) in exact x).

Definition ht4o_body : statement :=
  ltac:(let x := eval cbv beta iota delta [ht4o_loop] in
        (match ht4o_loop with Ssequence _ (Sloop (Ssequence _ b) _) => b | _ => Sskip end) in exact x).
Definition ht4o_bstmts : list statement :=
  ltac:(let x := eval cbv beta iota delta [ht4o_flat ht4o_body] in (ht4o_flat ht4o_body) in exact x).

Lemma ht4o_bstmts_length : length ht4o_bstmts = 22%nat.
Proof. reflexivity. Qed.

Definition ht4o_bl (i n: nat) : list statement := firstn n (skipn i ht4o_bstmts).

Definition ht4o_segL1 := ltac:(let x := eval cbv beta iota delta [ht4o_bl ht4o_seql firstn skipn ht4o_bstmts] in (ht4o_seql (ht4o_bl 0 9)) in exact x).
Definition ht4o_segL2 := ltac:(let x := eval cbv beta iota delta [ht4o_bl ht4o_seql firstn skipn ht4o_bstmts] in (ht4o_seql (ht4o_bl 9 5)) in exact x).
Definition ht4o_segL3 := ltac:(let x := eval cbv beta iota delta [ht4o_bl ht4o_seql firstn skipn ht4o_bstmts] in (ht4o_seql (ht4o_bl 14 4)) in exact x).
Definition ht4o_segL4 := ltac:(let x := eval cbv beta iota delta [ht4o_bl ht4o_seql firstn skipn ht4o_bstmts] in (ht4o_seql (ht4o_bl 18 4)) in exact x).

Lemma ht4o_body_eq :
  fn_body TO.f_main =
  Ssequence (ht4o_seqs (ht4o_l 0 6) (ht4o_seqs (ht4o_l 6 1) (ht4o_seql (ht4o_l 7 2))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint))).
Proof. reflexivity. Qed.

Lemma ht4o_loop_eq : ht4o_seql (ht4o_l 6 1) = ht4o_loop.
Proof. reflexivity. Qed.

Lemma ht4o_loop_shape :
  ht4o_loop =
  Ssequence (Sset TO._i (Ecast (Econst_int (Int.repr 0) tint) tulong))
    (Sloop
       (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar TO._i tulong) (Etempvar TO._steps tulong) tint) Sskip Sbreak)
          (ht4o_seqs (ht4o_bl 0 9) (ht4o_seqs (ht4o_bl 9 5) (ht4o_seqs (ht4o_bl 14 4) (ht4o_seql (ht4o_bl 18 4))))))
       (Sset TO._i (Ebinop Oadd (Etempvar TO._i tulong) (Econst_int (Int.repr 1) tint) tulong))).
Proof. reflexivity. Qed.

Lemma ht4o_segs_eq :
  ht4o_segL1 = ht4o_seql (ht4o_bl 0 9) /\ ht4o_segL2 = ht4o_seql (ht4o_bl 9 5) /\
  ht4o_segL3 = ht4o_seql (ht4o_bl 14 4) /\ ht4o_segL4 = ht4o_seql (ht4o_bl 18 4).
Proof. repeat split. Qed.

(* ---------------------------------------------------------------------- *)
(* The run's fixed part and the loop's state                               *)
(* ---------------------------------------------------------------------- *)

(* the globals, main's four local variables, the key K, steps *)
Record ht4o_fix := mkTFix {
  f_gv: globals; f_rc: val; f_wm: val; f_snap: val; f_key: val; f_K: list byte; f_steps: Z }.

(* the replay counter and the shadow model (top, the accepted set S, the bitmap bm), have_auth, last_nonce *)
Record ht4o_dyn := mkTDyn { y_top: Z; y_S: list Z; y_bm: list Z; y_have: bool; y_ln: Z }.

Definition ht4o_fix_ok (F: ht4o_fix) : Prop :=
  Zlength (f_K F) = 32 /\ 0 <= f_steps F <= Int64.max_unsigned.

Definition ht4o_inv (Y: ht4o_dyn) : Prop :=
  cnt_inv (y_top Y) (y_S Y) (y_bm Y) /\ 0 <= y_ln Y <= Int64.max_unsigned.

Definition ht4o_lvars (F: ht4o_fix) : list localdef :=
  [lvar TO._rc ht4o_trc (f_rc F); lvar TO._wm ht4o_twm (f_wm F); lvar TO._snap ht4o_tsnap (f_snap F);
   lvar TO._key (tarray tuchar 32) (f_key F); gvars (f_gv F)].

Definition ht4o_temps (F: ht4o_fix) (Y: ht4o_dyn) (i: Z) : list localdef :=
  [temp TO._i (Vlong (Int64.repr i)); temp TO._steps (Vlong (Int64.repr (f_steps F)));
   temp TO._last_nonce (Vlong (Int64.repr (y_ln Y)));
   temp TO._have_auth (Vint (if y_have Y then Int.one else Int.zero))].

(* the persistent memory (the snapshot rc_snap excepted): rc, wm, key, the globals the AEADs read, mem_mgr *)
Definition ht4o_world (F: ht4o_fix) (Y: ht4o_dyn) (FR: mpred) : list mpred :=
  [data_at Tsh ht4o_trc (ht4o_rc (y_top Y) (y_bm Y)) (f_rc F); ht4o_wm Tsh (y_top Y) (y_S Y) (f_wm F);
   data_at Tsh (tarray tuchar 32) (map Vubyte (f_K F)) (f_key F);
   zero_page (f_gv F); ht4_minusp ht4o_mp (f_gv F); mem_mgr (f_gv F); FR].

(* the loop state at iteration i (Pi: the bound on i) *)
Definition ht4o_St (F: ht4o_fix) (FR: mpred) (Pi: Prop) (i: Z) (Y: ht4o_dyn) : environ -> mpred :=
  PROPx [Pi; ht4o_fix_ok F; ht4o_inv Y]
  (LOCALx (ht4o_temps F Y i ++ ht4o_lvars F)
  (SEPx (data_at_ Tsh ht4o_tsnap (f_snap F) :: ht4o_world F Y FR))).

(* the loop invariant (before the test i < steps), and the state at the end of an
   iteration (before i++) = at the start of the body (after the test) *)
Definition ht4o_Inv (F: ht4o_fix) (FR: mpred) : environ -> mpred :=
  EX i: Z, EX Y: ht4o_dyn, ht4o_St F FR (0 <= i <= f_steps F) i Y.
Definition ht4o_Icont (F: ht4o_fix) (FR: mpred) (i: Z) : environ -> mpred :=
  EX Y: ht4o_dyn, ht4o_St F FR (0 <= i < f_steps F) i Y.

(* the state at a break (malloc failed or L too large): the loop is left; only memory matters (wm_free, return):
   rc and the snapshot any contents, wm any model *)
Definition ht4o_Brk (F: ht4o_fix) (FR: mpred) : environ -> mpred :=
  EX top: Z, EX S: list Z,
  PROPx [] (LOCALx (ht4o_lvars F)
  (SEPx [data_at_ Tsh ht4o_tsnap (f_snap F); data_at_ Tsh ht4o_trc (f_rc F); ht4o_wm Tsh top S (f_wm F);
         data_at Tsh (tarray tuchar 32) (map Vubyte (f_K F)) (f_key F);
         zero_page (f_gv F); ht4_minusp ht4o_mp (f_gv F); mem_mgr (f_gv F); FR])).

(* ---------------------------------------------------------------------- *)
(* The states between the segments                                         *)
(* ---------------------------------------------------------------------- *)

(* enc_len: kind 3 with L < 16 keeps L (no room for a tag), else L + 16 *)
Definition ht4o_enc (kind L: Z) : Z := if andb (Z.eqb kind 3) (Z.ltb L 16) then L else L + 16.

(* the sizes of the plaintext buffers pt_out, ref_pt *)
Definition ht4o_plen (enc: Z) : Z := Z.max 0 (enc - 16).

(* a malloc'd byte buffer of n bytes with contents v *)
Definition ht4o_buf (n: Z) (v: list val) (p: val) : mpred :=
  (malloc_token Ews (tarray tuchar n) p * data_at Ews (tarray tuchar n) v p)%logic.

(* the facts on kind and L *)
Definition ht4o_kL (kind L: Z) : Prop := 0 <= kind < 4 /\ 0 <= L <= Int64.max_signed - 32.

(* the temps of an iteration (L1 onwards) *)
Definition ht4o_tB (kind L: Z) (pkt po rp: val) : list localdef :=
  [temp TO._kind (Vint (Int.repr kind)); temp TO._L (Vlong (Int64.repr L));
   temp TO._enc_len (Vlong (Int64.repr (ht4o_enc kind L)));
   temp TO._pkt pkt; temp TO._pt_out po; temp TO._ref_pt rp].

(* after L1: kind, L drawn (L within the guard), the three buffers allocated (non-NULL), uninitialised *)
Definition ht4o_PL1 (F: ht4o_fix) (FR: mpred) (i: Z) : environ -> mpred :=
  EX Y: ht4o_dyn, EX kind: Z, EX L: Z, EX pkt: val, EX po: val, EX rp: val,
  PROPx [0 <= i < f_steps F; ht4o_fix_ok F; ht4o_inv Y; ht4o_kL kind L]
  (LOCALx (ht4o_tB kind L pkt po rp ++ ht4o_temps F Y i ++ ht4o_lvars F)
  (SEPx (data_at_ Tsh ht4o_tsnap (f_snap F) ::
         ht4o_buf (16 + ht4o_enc kind L) (Zrepeat Vundef (16 + ht4o_enc kind L)) pkt ::
         ht4o_buf (ht4o_plen (ht4o_enc kind L)) (Zrepeat Vundef (ht4o_plen (ht4o_enc kind L))) po ::
         ht4o_buf (ht4o_plen (ht4o_enc kind L)) (Zrepeat Vundef (ht4o_plen (ht4o_enc kind L))) rp ::
         ht4o_world F Y FR))).

(* after L2: the nonce, pkt = the 16-byte header hdr (any values) ++ the ciphertext ct (ANY enc_len bytes: the law
   only compares the kernel's and the reference's decryption of the same bytes) *)
Definition ht4o_PL2 (F: ht4o_fix) (FR: mpred) (i: Z) : environ -> mpred :=
  EX Y: ht4o_dyn, EX kind: Z, EX L: Z, EX pkt: val, EX po: val, EX rp: val,
  EX nonce: Z, EX hdr: list val, EX ct: list byte,
  PROPx [0 <= i < f_steps F; ht4o_fix_ok F; ht4o_inv Y; ht4o_kL kind L; 0 <= nonce <= Int64.max_unsigned;
         Zlength hdr = 16; Zlength ct = ht4o_enc kind L]
  (LOCALx (temp TO._nonce (Vlong (Int64.repr nonce)) :: ht4o_tB kind L pkt po rp ++ ht4o_temps F Y i ++
           ht4o_lvars F)
  (SEPx (data_at_ Tsh ht4o_tsnap (f_snap F) ::
         ht4o_buf (16 + ht4o_enc kind L) (hdr ++ map Vubyte ct) pkt ::
         ht4o_buf (ht4o_plen (ht4o_enc kind L)) (Zrepeat Vundef (ht4o_plen (ht4o_enc kind L))) po ::
         ht4o_buf (ht4o_plen (ht4o_enc kind L)) (Zrepeat Vundef (ht4o_plen (ht4o_enc kind L))) rp ::
         ht4o_world F Y FR))).

(* the decryption's verdict and a plaintext buffer after it (the plaintext, or untouched) *)
Definition ht4o_dec (F: ht4o_fix) (nonce: Z) (ct: list byte) : option (list byte) :=
  aead_dec (f_K F) nonce [] ct.
Definition ht4o_okv (d: option (list byte)) : val :=
  Vint (match d with Some _ => Int.one | None => Int.zero end).
Definition ht4o_ptv (d: option (list byte)) (n: Z) : list val :=
  match d with Some pt => map Vubyte pt | None => Zrepeat Vundef n end.

(* after L3: snap = rc's copy; ok = ref_ok = the model's verdict (the CHECK passed); pt_out and ref_pt both hold
   the plaintext on acceptance, are untouched otherwise *)
Definition ht4o_PL3 (F: ht4o_fix) (FR: mpred) (i: Z) : environ -> mpred :=
  EX Y: ht4o_dyn, EX kind: Z, EX L: Z, EX pkt: val, EX po: val, EX rp: val,
  EX nonce: Z, EX hdr: list val, EX ct: list byte,
  PROPx [0 <= i < f_steps F; ht4o_fix_ok F; ht4o_inv Y; ht4o_kL kind L; 0 <= nonce <= Int64.max_unsigned;
         Zlength hdr = 16; Zlength ct = ht4o_enc kind L]
  (LOCALx (temp TO._ok (ht4o_okv (ht4o_dec F nonce ct)) :: temp TO._ref_ok (ht4o_okv (ht4o_dec F nonce ct)) ::
           temp TO._nonce (Vlong (Int64.repr nonce)) :: ht4o_tB kind L pkt po rp ++ ht4o_temps F Y i ++
           ht4o_lvars F)
  (SEPx (data_at Tsh ht4o_tsnap (ht4o_snap (y_top Y) (y_bm Y)) (f_snap F) ::
         ht4o_buf (16 + ht4o_enc kind L) (hdr ++ map Vubyte ct) pkt ::
         ht4o_buf (ht4o_plen (ht4o_enc kind L))
           (ht4o_ptv (ht4o_dec F nonce ct) (ht4o_plen (ht4o_enc kind L))) po ::
         ht4o_buf (ht4o_plen (ht4o_enc kind L))
           (ht4o_ptv (ht4o_dec F nonce ct) (ht4o_plen (ht4o_enc kind L))) rp ::
         ht4o_world F Y FR))).

(* main's post (TT) weakened to the canonical form forward needs for a return *)
Lemma ht4o_post_canon {Espec: OracleKind} Delta P c Q gv F :
  semax Delta P c (overridePost Q (frame_ret_assert (function_body_ret_assert tint (PROP () LOCAL () SEP (TT))) F)) ->
  semax Delta P c (overridePost Q (frame_ret_assert (function_body_ret_assert tint (ht4o_post gv)) F)).
Proof.
  intros H. eapply semax_post; [| | | | apply H]; intros; simpl; intros rho; apply andp_left2;
    try apply derives_refl.
  apply sepcon_derives; [| apply derives_refl]. revert rho. apply bind_ret_derives. intros rho. apply TT_right.
Qed.
