(* main of harness/transport_len.c: its specification context, the
   initial globals, the segments of the body and the states between them.

   main is proved at the law's world W_transport_len (it evaluates sizeof(struct message_data)); the functions it
   calls are imported at W_transport_len: the shared common.h specifications of ht4c_spec.v / ht4r_spec.v
   (cs-generic), the kernel AEAD entries of ht4a_aead.v (any length: the concrete piece aead_piece3b, aead_model's
   aead_enc / aead_dec), wg_validate_header_len (dh4_spec.v), the external world (asm_env.env_specs).  The assembly
   relates them to the bodies' instances by funspec_sub (byte arrays). *)
Require WgNoise.proof.assembly.asm_env.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require WgNoise.units.DataHeader.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_dec3.
Require Import WgNoise.proof.harness.common4t.ht4_worlds.
Require Import WgNoise.proof.harness.common4t.ht4c_spec.
Require Import WgNoise.proof.harness.common4t.ht4r_spec.
Require Import WgNoise.proof.harness.common4t.ht4a_aead.
Require Import WgNoise.proof.data_header.dh4_spec.
Require WgNoise.contracts.x_transport_len.
Require WgNoise.harness.x_transport_len.code.

#[local] Existing Instance W_transport_len.
Local Open Scope Z_scope.

Module TLC := WgNoise.harness.x_transport_len.code.

(* ---------------------------------------------------------------------- *)
(* main's specification and context                                       *)
(* ---------------------------------------------------------------------- *)

(* rp_final's static minusp in this harness *)
Definition htl5_mp : ident := TLC._x_transport_len__minusp.

(* the varspecs of the whole program (literal) *)
Definition htl5_V : varspecs :=
  ltac:(let x := eval vm_compute in (QPvarspecs WgNoise.contracts.x_transport_len.whole_prog) in exact x).

(* main: the precondition is fixed (main_pre of the whole program), the postcondition anything *)
Definition htl5_post : (ident -> val) -> environ -> mpred := fun _ _ => TT.

Definition htl5_main_spec : ident * funspec :=
  (TLC._main, QPmain_spec_ext' WgNoise.contracts.x_transport_len.whole_prog tt htl5_post).

(* what main calls, at W_transport_len *)
Definition htl5_imports : funspecs :=
  @asm_env.env_specs W_transport_len ++
  [ht4_check_failed_spec; ht4_draw_size_spec; ht4_draw_u64_spec; ht4_le32_store_spec; ht4_bytes_eq_spec;
   wg_validate_header_len_spec; ht4_encrypt_spec; ht4_decrypt_spec;
   ref_aead_decrypt_spec_n W_transport_len htl5_mp].

Definition htl5_Gprog : funspecs := htl5_imports ++ [htl5_main_spec].

(* ---------------------------------------------------------------------- *)
(* u32 arrays are the same in every compspecs (minusp)                     *)
(* ---------------------------------------------------------------------- *)

Lemma htl5_align_tuint_cs (ce1 ce2: composite_env) n z :
  align_compatible_rec ce1 (tarray tuint n) z -> align_compatible_rec ce2 (tarray tuint n) z.
Proof.
  intros H. apply align_compatible_rec_Tarray. intros i Hi.
  eapply align_compatible_rec_Tarray_inv in H; [| exact Hi].
  inv H. econstructor; eauto.
Qed.

Lemma htl5_field_compatible_tuint_cs {cs1 cs2: compspecs} n p :
  @field_compatible cs1 (tarray tuint n) [] p <-> @field_compatible cs2 (tarray tuint n) [] p.
Proof.
  unfold field_compatible, align_compatible, size_compatible; simpl.
  split; intros (? & ? & ? & ? & ?); repeat split; auto;
  destruct p; auto.
  all: first [ exact (htl5_align_tuint_cs (@cenv_cs cs1) (@cenv_cs cs2) _ _ ltac:(eassumption))
             | exact (htl5_align_tuint_cs (@cenv_cs cs2) (@cenv_cs cs1) _ _ ltac:(eassumption)) ].
Qed.

Lemma htl5_data_at_tuint_cs {cs1 cs2: compspecs} sh n (v: list val) p :
  @data_at cs1 sh (tarray tuint n) v p = @data_at cs2 sh (tarray tuint n) v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext. apply htl5_field_compatible_tuint_cs.
Qed.

(* the minusp resource as ref_aead_decrypt_spec_n states it (at W_prim_aead) *)
Definition htl5_minusp (gv: globals) : mpred := @ht4_minusp W_prim_aead htl5_mp gv.

(* ---------------------------------------------------------------------- *)
(* The initial globals: keep zero_page and minusp                          *)
(* ---------------------------------------------------------------------- *)

Lemma htl5_InitGPred_filter (f: ident * globdef (fundef function) type -> bool) al gv :
  InitGPred al gv |-- (InitGPred (filter f al) gv * TT)%logic.
Proof.
  induction al as [|a al IH]; simpl.
  - unfold InitGPred; simpl. cancel.
  - unfold InitGPred in *; simpl. destruct (f a); simpl.
    + rewrite sepcon_assoc. apply sepcon_derives; auto.
    + eapply derives_trans; [apply sepcon_derives; [apply TT_right | apply IH] |].
      rewrite (sepcon_comm (fold_right _ _ _)), <- sepcon_assoc, TT_sepcon_TT. cancel.
Qed.

Definition htl5_keep (x: ident * globdef (fundef function) type) : bool :=
  Pos.eqb (fst x) htl5_mp || Pos.eqb (fst x) _quickproof_zero_page.

Definition htl5_vardefs :=
  ltac:(let x := eval vm_compute in
    (filter htl5_keep (Vardefs WgNoise.contracts.x_transport_len.whole_prog)) in exact x).

Lemma htl5_vardefs_eq :
  filter htl5_keep (Vardefs WgNoise.contracts.x_transport_len.whole_prog) = htl5_vardefs.
Proof. vm_compute. reflexivity. Qed.

Lemma htl5_init_globals gv :
  globals_ok gv ->
  InitGPred (Vardefs WgNoise.contracts.x_transport_len.whole_prog) gv |-- (zero_page gv * htl5_minusp gv * TT)%logic.
Proof.
  intros Hgv. eapply derives_trans; [apply (htl5_InitGPred_filter htl5_keep) |].
  rewrite htl5_vardefs_eq. apply sepcon_derives; [| apply derives_refl].
  change (InitGPred htl5_vardefs gv |-- (fun g => zero_page g * htl5_minusp g)%logic gv).
  eapply InitGPred_process_globvars; auto.
  let Delta := fresh "Delta" in let Delta' := fresh "Delta'" in
  set (Delta' := vardefs_tycontext _);
  set (Delta := @abbreviate tycontext Delta');
  change Delta' with Delta;
  hnf in Delta'; simpl in Delta'; subst Delta'.
  simpl vardefs_to_globvars.
  eapply derives_trans; [process_globals | ].
  clear Delta. apply finish_process_globvars'. unfold fold_right_sepcon at 1.
  simpl readonly2share. rewrite sepcon_emp.
  match goal with |- data_at ?sh (tarray tuint 17) ?l ?p * _ |-- _ =>
    replace l with (map Vint hrp_minusp) by
      (vm_compute; repeat match goal with |- cons _ _ = cons _ _ => f_equal
                                     | |- Vint _ = Vint _ => f_equal; apply Int.mkint_eq; reflexivity end) end.
  rewrite sepcon_comm.
  unfold zero_page, htl5_minusp, ht4_minusp. apply sepcon_derives.
  - rewrite zero_val_tarray. replace (zero_val tuchar) with (Vubyte Byte.zero) by (rewrite zero_val_eq; reflexivity).
    match goal with |- data_at _ _ _ (gv ?i) |-- data_at _ _ _ (gv ?j) =>
      replace i with j by reflexivity end.
    apply derives_refl.
  - rewrite (@htl5_data_at_tuint_cs W_transport_len W_prim_aead). apply derives_refl.
Qed.

(* ---------------------------------------------------------------------- *)
(* Cutting main's body into segments                                       *)
(* ---------------------------------------------------------------------- *)

Fixpoint htl5_seqs (l: list statement) (rest: statement) : statement :=
  match l with [] => rest | a :: l' => Ssequence a (htl5_seqs l' rest) end.

Fixpoint htl5_seql (l: list statement) : statement :=
  match l with [] => Sskip | [a] => a | a :: l' => Ssequence a (htl5_seql l') end.

Fixpoint htl5_flat_seq (s: statement) : list statement :=
  match s with Ssequence a b => a :: htl5_flat_seq b | _ => [s] end.

Lemma htl5_unfold_seql l : l <> [] ->
  unfold_Ssequence (htl5_seql l) = concat (map unfold_Ssequence l).
Proof.
  induction l as [|a l IH]; intros Hl; [congruence |].
  destruct l as [|b l']; simpl.
  - rewrite app_nil_r; reflexivity.
  - simpl in IH. rewrite IH by discriminate. reflexivity.
Qed.

Lemma htl5_unfold_seqs l rest :
  unfold_Ssequence (htl5_seqs l rest) = concat (map unfold_Ssequence l) ++ unfold_Ssequence rest.
Proof.
  induction l as [|a l IH]; simpl; [reflexivity |]. rewrite IH, app_assoc. reflexivity.
Qed.

Lemma htl5_overridePost2 Q Q' R : overridePost Q (overridePost Q' R) = overridePost Q R.
Proof. destruct R; reflexivity. Qed.

Lemma htl5_semax_cut {Espec: OracleKind} {cs: compspecs} Delta P Q R l rest :
  l <> [] ->
  semax Delta P (htl5_seql l) (overridePost Q R) -> semax Delta Q rest R ->
  semax Delta P (htl5_seqs l rest) R.
Proof.
  intros Hl H1 H2.
  apply (semax_unfold_Ssequence (Ssequence (htl5_seql l) rest)).
  - simpl. rewrite htl5_unfold_seql, htl5_unfold_seqs by auto. reflexivity.
  - eapply semax_seq; eauto.
Qed.

(* main's body is  S1; return 0  with S1 = the 30 statements below *)
Definition htl5_stmts : list statement :=
  ltac:(let x := eval cbv beta iota delta [htl5_flat_seq TLC.f_main fn_body] in
        (match fn_body TLC.f_main with Ssequence s _ => htl5_flat_seq s | s => [s] end) in exact x).

Lemma htl5_stmts_length : length htl5_stmts = 30%nat.
Proof. reflexivity. Qed.

Definition htl5_sub (i n: nat) : statement := htl5_seql (firstn n (skipn i htl5_stmts)).
Definition htl5_l (i n: nat) : list statement := firstn n (skipn i htl5_stmts).

(* the segments:
   A = 0..4    nondet key, nonce = draw_u64(), tot (switch on nondet_u8() % 4; return above PTRDIFF_MAX - 32),
               type (switch on nondet_u8() % 4)
   B = 5..8    pkt = malloc(tot) (NULL: return), nondet_bytes(pkt, tot), if (tot >= 4) le32_store(pkt, type)
   C = 9..12   hl = wg_validate_header_len(type, tot), expect, CHECK(hl == expect),
               if (type != MESSAGE_DATA || hl == 0) { free(pkt); return 0; }
   D = 13..17  enc_len = tot - 16, CHECK(enc_len >= 16), pt_len = enc_len - 16, authentic = nondet_u8() & 1,
               if (authentic) { pt = malloc(pt_len) (NULL: free(pkt), return); nondet_bytes(pt, pt_len);
                                chacha20poly1305_encrypt(pkt + 16, pt, pt_len, NULL, 0, nonce, key); free(pt); }
   E = 18..20  pt_out = malloc(pt_len), ref_pt = malloc(pt_len), if either is NULL { free x3; return 0; }
   F = 21..29  ok = chacha20poly1305_decrypt(pt_out, pkt + 16, enc_len, NULL, 0, nonce, key),
               ref_ok = ref_aead_decrypt(ref_pt, pkt + 16, enc_len, NULL, 0, nonce, key), CHECK(ok == ref_ok),
               if (ok) CHECK(bytes_eq(pt_out, ref_pt, pt_len)), if (authentic) CHECK(ok), free x3, return 0 *)
Definition htl5_segA := ltac:(let x := eval cbv beta iota delta [htl5_sub htl5_seql firstn skipn htl5_stmts] in (htl5_sub 0 5) in exact x).
Definition htl5_segB := ltac:(let x := eval cbv beta iota delta [htl5_sub htl5_seql firstn skipn htl5_stmts] in (htl5_sub 5 4) in exact x).
Definition htl5_segC := ltac:(let x := eval cbv beta iota delta [htl5_sub htl5_seql firstn skipn htl5_stmts] in (htl5_sub 9 4) in exact x).
Definition htl5_segD := ltac:(let x := eval cbv beta iota delta [htl5_sub htl5_seql firstn skipn htl5_stmts] in (htl5_sub 13 5) in exact x).
Definition htl5_segE := ltac:(let x := eval cbv beta iota delta [htl5_sub htl5_seql firstn skipn htl5_stmts] in (htl5_sub 18 3) in exact x).
Definition htl5_segF := ltac:(let x := eval cbv beta iota delta [htl5_sub htl5_seql firstn skipn htl5_stmts] in (htl5_sub 21 9) in exact x).

Lemma htl5_body_eq :
  fn_body TLC.f_main =
  Ssequence
    (htl5_seqs (htl5_l 0 5) (htl5_seqs (htl5_l 5 4) (htl5_seqs (htl5_l 9 4)
      (htl5_seqs (htl5_l 13 5) (htl5_seqs (htl5_l 18 3) (htl5_seql (htl5_l 21 9)))))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint))).
Proof. reflexivity. Qed.

Lemma htl5_segs_eq :
  htl5_segA = htl5_seql (htl5_l 0 5) /\ htl5_segB = htl5_seql (htl5_l 5 4) /\
  htl5_segC = htl5_seql (htl5_l 9 4) /\ htl5_segD = htl5_seql (htl5_l 13 5) /\
  htl5_segE = htl5_seql (htl5_l 18 3) /\ htl5_segF = htl5_seql (htl5_l 21 9).
Proof. repeat split. Qed.

(* ---------------------------------------------------------------------- *)
(* The states between the segments                                         *)
(* ---------------------------------------------------------------------- *)

Definition htl5_Delta : tycontext := func_tycontext TLC.f_main htl5_V htl5_Gprog [].

Definition htl5_R (gv: globals) : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (htl5_post gv)) (stackframe_of TLC.f_main).

(* the local key array and the globals *)
Definition htl5_lv (gv: globals) (vk: val) : list localdef :=
  [lvar TLC._key (tarray tuchar 32) vk; gvars gv].

(* the facts on the drawn values *)
Definition htl5_ranges (key: list byte) (nonce tot: Z) : Prop :=
  Zlength key = 32 /\ 0 <= nonce <= Int64.max_unsigned /\ 0 <= tot <= Int64.max_signed - 32.

(* a malloc'd byte buffer of len bytes with contents v *)
Definition htl5_buf (len: Z) (v: list val) (p: val) : mpred :=
  (malloc_token Ews (tarray tuchar len) p * data_at Ews (tarray tuchar len) v p)%logic.

(* the authentic payload: when au <> 0 the encrypted_data region [16, tot) is the encryption of some message of
   tot - 32 bytes under (key, nonce), without associated data *)
Definition htl5_auth (au: Z) (key: list byte) (nonce tot: Z) (pk: list byte) : Prop :=
  au <> 0 -> exists m, Zlength m = tot - 32 /\ sublist 16 tot pk = aead_enc key nonce [] m.

(* before segment A (after the prologue) *)
Definition htl5_P0 (gv: globals) (vk: val) (FR: mpred) : environ -> mpred :=
  PROPx [] (LOCALx (htl5_lv gv vk)
  (SEPx [data_at_ Tsh (tarray tuchar 32) vk; mem_mgr gv; zero_page gv; htl5_minusp gv; FR])).

(* after A: key, nonce, tot (<= PTRDIFF_MAX - 32), type drawn *)
Definition htl5_PA (gv: globals) (vk: val) (FR: mpred) : environ -> mpred :=
  EX key: list byte, EX nonce: Z, EX tot: Z, EX type: Z,
  PROPx [htl5_ranges key nonce tot; 0 <= type <= Int.max_unsigned]
  (LOCALx ([temp TLC._nonce (Vlong (Int64.repr nonce)); temp TLC._tot (Vlong (Int64.repr tot));
            temp TLC._type (Vint (Int.repr type))] ++ htl5_lv gv vk)
  (SEPx [data_at Tsh (tarray tuchar 32) (map Vubyte key) vk; mem_mgr gv; zero_page gv; htl5_minusp gv; FR])).

(* after B: the packet buffer pkt of exactly tot bytes (non-NULL), its bytes pk *)
Definition htl5_PB (gv: globals) (vk: val) (FR: mpred) : environ -> mpred :=
  EX key: list byte, EX nonce: Z, EX tot: Z, EX type: Z, EX pkt: val, EX pk: list byte,
  PROPx [htl5_ranges key nonce tot; 0 <= type <= Int.max_unsigned; Zlength pk = tot]
  (LOCALx ([temp TLC._pkt pkt; temp TLC._nonce (Vlong (Int64.repr nonce)); temp TLC._tot (Vlong (Int64.repr tot));
            temp TLC._type (Vint (Int.repr type))] ++ htl5_lv gv vk)
  (SEPx [data_at Tsh (tarray tuchar 32) (map Vubyte key) vk; htl5_buf tot (map Vubyte pk) pkt;
         mem_mgr gv; zero_page gv; htl5_minusp gv; FR])).

(* after C: the gate admitted a data packet: tot >= MESSAGE_MINIMUM_LENGTH = 32 *)
Definition htl5_PC (gv: globals) (vk: val) (FR: mpred) : environ -> mpred :=
  EX key: list byte, EX nonce: Z, EX tot: Z, EX pkt: val, EX pk: list byte,
  PROPx [htl5_ranges key nonce tot; 32 <= tot; Zlength pk = tot]
  (LOCALx ([temp TLC._pkt pkt; temp TLC._nonce (Vlong (Int64.repr nonce)); temp TLC._tot (Vlong (Int64.repr tot))]
           ++ htl5_lv gv vk)
  (SEPx [data_at Tsh (tarray tuchar 32) (map Vubyte key) vk; htl5_buf tot (map Vubyte pk) pkt;
         mem_mgr gv; zero_page gv; htl5_minusp gv; FR])).

(* after D: enc_len, pt_len, authentic; an authentic packet's region [16, tot) is a real ciphertext *)
Definition htl5_PD (gv: globals) (vk: val) (FR: mpred) : environ -> mpred :=
  EX key: list byte, EX nonce: Z, EX tot: Z, EX pkt: val, EX pk: list byte, EX au: Z,
  PROPx [htl5_ranges key nonce tot; 32 <= tot; Zlength pk = tot; 0 <= au <= 1; htl5_auth au key nonce tot pk]
  (LOCALx ([temp TLC._pkt pkt; temp TLC._nonce (Vlong (Int64.repr nonce));
            temp TLC._enc_len (Vlong (Int64.repr (tot - 16))); temp TLC._pt_len (Vlong (Int64.repr (tot - 32)));
            temp TLC._authentic (Vint (Int.repr au))] ++ htl5_lv gv vk)
  (SEPx [data_at Tsh (tarray tuchar 32) (map Vubyte key) vk; htl5_buf tot (map Vubyte pk) pkt;
         mem_mgr gv; zero_page gv; htl5_minusp gv; FR])).

(* after E: the two output buffers of pt_len = tot - 32 bytes (non-NULL), uninitialised *)
Definition htl5_PE (gv: globals) (vk: val) (FR: mpred) : environ -> mpred :=
  EX key: list byte, EX nonce: Z, EX tot: Z, EX pkt: val, EX pk: list byte, EX au: Z, EX pto: val, EX rpt: val,
  PROPx [htl5_ranges key nonce tot; 32 <= tot; Zlength pk = tot; 0 <= au <= 1; htl5_auth au key nonce tot pk]
  (LOCALx ([temp TLC._pt_out pto; temp TLC._ref_pt rpt; temp TLC._pkt pkt; temp TLC._nonce (Vlong (Int64.repr nonce));
            temp TLC._enc_len (Vlong (Int64.repr (tot - 16))); temp TLC._pt_len (Vlong (Int64.repr (tot - 32)));
            temp TLC._authentic (Vint (Int.repr au))] ++ htl5_lv gv vk)
  (SEPx [data_at Tsh (tarray tuchar 32) (map Vubyte key) vk; htl5_buf tot (map Vubyte pk) pkt;
         htl5_buf (tot - 32) (Zrepeat Vundef (tot - 32)) pto; htl5_buf (tot - 32) (Zrepeat Vundef (tot - 32)) rpt;
         mem_mgr gv; zero_page gv; htl5_minusp gv; FR])).

(* main's post (TT) weakened to the canonical form forward needs for a return *)
Lemma htl5_post_canon {Espec: OracleKind} {cs: compspecs} Delta P c Q gv F :
  semax Delta P c (overridePost Q (frame_ret_assert (function_body_ret_assert tint (PROP () LOCAL () SEP (TT))) F)) ->
  semax Delta P c (overridePost Q (frame_ret_assert (function_body_ret_assert tint (htl5_post gv)) F)).
Proof.
  intros H. eapply semax_post; [| | | | apply H]; intros; simpl; intros rho; apply andp_left2;
    try apply derives_refl.
  apply sepcon_derives; [| apply derives_refl]. revert rho. apply bind_ret_derives. intros rho. apply TT_right.
Qed.
