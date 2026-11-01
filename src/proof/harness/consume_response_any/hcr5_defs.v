(* law consume_response_any: main's body cut into
   phases, and the states between them.

   Conventions of the states (all phases):
   - main runs in the world compspecs W := W_consume_response_any (Delta hcr5_Delta).  The SEP items are kept in
     the compspecs of the specifications that consume them: the protocol objects through prot_repr3's predicates
     (device_rep, peers_rep, itable, ptable, resp_rep: Noise.CS inside), the shim with EXACT warnings
     (`shim_state4 gv S hcr5_w0`: no refcount_t warning ever happens in this law), the harness structs m_identity
     / m_state / m_response as `@data_at(_) HCS`, the snapshots dev_snap / shim_snap as `@data_at(_) CKS`
     (common4), the local `peers` (struct hnode * ) as `@data_at(_) W` (hnodes_add4 has it at CKS: convert with
     hcr5_conv_hnodep_v), the node list as `hnodes_rep4 W` (common4), the kents as `kents_rep W` (common4), byte
     buffers as hbytes / hout (HCS).  The prologue (hcr5_main.v) converts the stack frame (W) to these forms.
   - main's body = S1; return 0 with S1 = the 18 statements of hcr5_stmts (the last one is `return 0`):
       P1 =  0..8   peers = NULL, boot clock, wg_noise_init, raw keys, setup_device(&wa ..), the identities,
                    nb = hnodes_add(&peers, &wa, ib.pub, 0)
       P2 =  9..10  n = draw_steps(); the loop adding n peers
       P3 = 11      the loop over the nodes: hs_randomize, peer_randomize_rest, maybe wg_index_hashtable_insert
       PK = 12      kes = kents_add(&ita, peers, NULL, 1)
       P5 = 13      msg = malloc(sizeof *msg)
       P6 = 14      if (msg != NULL) { ... }: the then-branch is cut into Q1a .. Q5 (hcr5_tstmts, 19 statements):
         Q1a =  0..2   fill_resp, mode, the mode-0 block (receiver index from the table)
         Q1b =  3      the mode-1/2 block (B's response built by the model, mode 2: one byte changed)
         Q2  =  4..11  resp_img(img), boot clock, hnodes_snap, kents_snap, dev_take, head0 = ita.head,
                       shim_take, ret = wg_noise_handshake_consume_response(msg, &wa)
         Q3  = 12..13  the harness's model: target
         Q4  = 14..16  resp_img(img_after), CHECK(image), CHECK(dev_same && head0 && kents_same && shim_same)
         Q5  = 17..18  the CHECKs on target / ret (wg_peer_put, hnodes_same_except, pr_same), free(msg)
       P7 = 15..17  kents_free(kes), hnodes_free(peers), return 0
   - The states: hcr5_S0 (prologue), hcr5_SA (after P1, P2 and P3: the same invariant), hcr5_SK (after PK),
     hcr5_S5 (after P5), hcr5_SE (after P6); inside P6: hcr5_S5n (msg <> NULL), hcr5_SQ1a, hcr5_SQ1b, hcr5_SQ2,
     hcr5_SQ3, hcr5_SQ4 (then hcr5_SE).  P7 ends in FF (it returns).
   - The peers: PS (the protocol's list, in public-key-chain order = the node list's order, both pushed at the
     head), NS (the harness's nodes: addresses and peers; the node CONTENTS are a second list NS' in the world).
     The index table T: its pool is the kents' keypair entries (KE, most recent first) followed by the peers'
     handshake entries (PS order), `hcr5_pool` (hcr5_model.v); any subset of the entries is hashed.  The kents'
     entries belong to any peers; the peers' keypair slots are NULL or kents (kents_add with fill).
   - FR: an opaque frame (TT * has_ext), carried along. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_cut.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_model.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_spec.
Require WgNoise.contracts.x_consume_response_any.
Require WgNoise.harness.x_consume_response_any.code.
Local Open Scope logic.

Notation W := W_consume_response_any.

(* ---------------------------------------------------------------------- *)
(* The hypotheses of the phase lemmas                                      *)
(* ---------------------------------------------------------------------- *)

(* the statement of prot_rep_lemmas3 (proved in the base: hcr5_rep_ok in the assembly; a hypothesis of the
   phases, as in v1) *)
Section Rep.
#[local] Existing Instance Noise.CS.
Definition hcr5_rep : Prop :=
  (forall sh m M, init_rep sh m M |-- bytes_at sh (init_bytes M) m) /\
  (forall sh m M, field_compatible t_init [] m -> im_ok M ->
     bytes_at sh (init_bytes M) m |-- init_rep sh m M) /\
  (forall sh m M, resp_rep sh m M |-- bytes_at sh (resp_bytes M) m) /\
  (forall sh m M, field_compatible t_resp [] m -> rm_ok M ->
     bytes_at sh (resp_bytes M) m |-- resp_rep sh m M) /\
  (forall sht tab T a sh E, writable_share sh ->
     itable sht tab T * entry_out sh a E |-- itable sht tab (t_add T a sh E)) /\
  (forall sht tab T a sh E, sfind (t_D T) a = Some (sh, E) -> ~ In a (t_L T) ->
     itable sht tab T |-- itable sht tab (t_free T a) * entry_out sh a E) /\
  (forall sh p P E n h, peer_rep sh p P * entry_at sh (hs_addr p) E n h |-- @data_at_ Noise.CS sh t_peer p) /\
  (forall CSw k K E n h, keypair_rep CSw k K * entry_at Ews k E n h |--
     @malloc_token CSw Ews (tarray tuchar SIZEOF_KEYPAIR) k *
     @data_at_ Noise.CS Ews (tarray tuchar SIZEOF_KEYPAIR) k).
End Rep.

Section Defs.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Definition hcr5_hyps : Prop :=
  x25519_props x25519 /\ aead_props aead_enc aead_dec /\ xaead_props xaead_enc xaead_dec /\ hcr5_rep.

(* ---------------------------------------------------------------------- *)
(* main's context                                                          *)
(* ---------------------------------------------------------------------- *)

Definition hcr5_Gprog : funspecs :=
  hcr5_imports x25519 aead_enc aead_dec xaead_enc xaead_dec W ++ hcr5_G.
Definition hcr5_Delta : tycontext := func_tycontext HR5.f_main hcr5_V hcr5_Gprog [].

Definition hcr5_R (gv: globals) : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (hcr5_post gv)) (@stackframe_of W HR5.f_main).

End Defs.

(* ---------------------------------------------------------------------- *)
(* Cutting main's body                                                     *)
(* ---------------------------------------------------------------------- *)

Lemma hcr5_unfold_seql l : l <> [] ->
  unfold_Ssequence (hcr5_seql l) = concat (map unfold_Ssequence l).
Proof.
  induction l as [|a l IH]; intros Hl; [congruence |].
  destruct l as [|b l']; simpl.
  - rewrite app_nil_r; reflexivity.
  - simpl in IH. rewrite IH by discriminate. reflexivity.
Qed.

Lemma hcr5_unfold_seqs l rest :
  unfold_Ssequence (hcr5_seqs l rest) = concat (map unfold_Ssequence l) ++ unfold_Ssequence rest.
Proof.
  induction l as [|a l IH]; simpl; [reflexivity |]. rewrite IH, app_assoc. reflexivity.
Qed.

Lemma hcr5_overridePost2 Q Q' R : overridePost Q (overridePost Q' R) = overridePost Q R.
Proof. destruct R; reflexivity. Qed.

Lemma hcr5_semax_cut {Espec: OracleKind} {cs: compspecs} Delta P Q R l rest :
  l <> [] ->
  semax Delta P (hcr5_seql l) (overridePost Q R) -> semax Delta Q rest R ->
  semax Delta P (hcr5_seqs l rest) R.
Proof.
  intros Hl H1 H2.
  apply (semax_unfold_Ssequence (Ssequence (hcr5_seql l) rest)).
  - simpl. rewrite hcr5_unfold_seql, hcr5_unfold_seqs by auto. reflexivity.
  - eapply semax_seq; eauto.
Qed.

(* a list cut into two consecutive non-empty pieces *)
Lemma hcr5_seql_app {Espec: OracleKind} {cs: compspecs} Delta P Q R l1 l2 :
  l1 <> [] -> l2 <> [] ->
  semax Delta P (hcr5_seql l1) (overridePost Q R) -> semax Delta Q (hcr5_seql l2) R ->
  semax Delta P (hcr5_seql (l1 ++ l2)) R.
Proof.
  intros H1 H2 S1 S2.
  assert (H12: l1 ++ l2 <> []) by (destruct l1; [congruence | discriminate]).
  apply (semax_unfold_Ssequence (Ssequence (hcr5_seql l1) (hcr5_seql l2))).
  - simpl. rewrite (hcr5_unfold_seql _ H12), (hcr5_unfold_seql _ H1), (hcr5_unfold_seql _ H2), map_app, concat_app.
    reflexivity.
  - eapply semax_seq; eauto.
Qed.

Lemma hcr5_stmts_length : length hcr5_stmts = 18%nat.
Proof. reflexivity. Qed.

Definition hcr5_l (i n: nat) : list statement := firstn n (skipn i hcr5_stmts).

Definition hcr5_P1 := ltac:(let x := eval cbv beta iota delta [hcr5_l hcr5_seql firstn skipn hcr5_stmts] in (hcr5_seql (hcr5_l 0 9)) in exact x).
Definition hcr5_P2 := ltac:(let x := eval cbv beta iota delta [hcr5_l hcr5_seql firstn skipn hcr5_stmts] in (hcr5_seql (hcr5_l 9 2)) in exact x).
Definition hcr5_P3 := ltac:(let x := eval cbv beta iota delta [hcr5_l hcr5_seql firstn skipn hcr5_stmts] in (hcr5_seql (hcr5_l 11 1)) in exact x).
Definition hcr5_PK := ltac:(let x := eval cbv beta iota delta [hcr5_l hcr5_seql firstn skipn hcr5_stmts] in (hcr5_seql (hcr5_l 12 1)) in exact x).
Definition hcr5_P5 := ltac:(let x := eval cbv beta iota delta [hcr5_l hcr5_seql firstn skipn hcr5_stmts] in (hcr5_seql (hcr5_l 13 1)) in exact x).
Definition hcr5_P6 := ltac:(let x := eval cbv beta iota delta [hcr5_l hcr5_seql firstn skipn hcr5_stmts] in (hcr5_seql (hcr5_l 14 1)) in exact x).
Definition hcr5_P7 := ltac:(let x := eval cbv beta iota delta [hcr5_l hcr5_seql firstn skipn hcr5_stmts] in (hcr5_seql (hcr5_l 15 3)) in exact x).

Lemma hcr5_body_eq :
  fn_body HR5.f_main =
  Ssequence
    (hcr5_seqs (hcr5_l 0 9) (hcr5_seqs (hcr5_l 9 2) (hcr5_seqs (hcr5_l 11 1) (hcr5_seqs (hcr5_l 12 1)
      (hcr5_seqs (hcr5_l 13 1) (hcr5_seqs (hcr5_l 14 1) (hcr5_seql (hcr5_l 15 3))))))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint))).
Proof. reflexivity. Qed.

Lemma hcr5_phases_eq :
  hcr5_P1 = hcr5_seql (hcr5_l 0 9) /\ hcr5_P2 = hcr5_seql (hcr5_l 9 2) /\
  hcr5_P3 = hcr5_seql (hcr5_l 11 1) /\ hcr5_PK = hcr5_seql (hcr5_l 12 1) /\
  hcr5_P5 = hcr5_seql (hcr5_l 13 1) /\ hcr5_P6 = hcr5_seql (hcr5_l 14 1) /\
  hcr5_P7 = hcr5_seql (hcr5_l 15 3).
Proof. repeat split. Qed.

(* P6 = if (msg != NULL) { then-branch } (else nothing); the then-branch's 19 statements *)
Definition hcr5_cond : expr :=
  ltac:(let x := eval cbv beta iota delta [hcr5_P6] in
        (match hcr5_P6 with Sifthenelse c _ _ => c | _ => Econst_int Int.zero tint end) in exact x).

Lemma hcr5_tstmts_length : length hcr5_tstmts = 19%nat.
Proof. reflexivity. Qed.

Definition hcr5_tl (i n: nat) : list statement := firstn n (skipn i hcr5_tstmts).

Definition hcr5_Q1a := ltac:(let x := eval cbv beta iota delta [hcr5_tl hcr5_seql firstn skipn hcr5_tstmts] in (hcr5_seql (hcr5_tl 0 3)) in exact x).
Definition hcr5_Q1b := ltac:(let x := eval cbv beta iota delta [hcr5_tl hcr5_seql firstn skipn hcr5_tstmts] in (hcr5_seql (hcr5_tl 3 1)) in exact x).
Definition hcr5_Q2 := ltac:(let x := eval cbv beta iota delta [hcr5_tl hcr5_seql firstn skipn hcr5_tstmts] in (hcr5_seql (hcr5_tl 4 8)) in exact x).
Definition hcr5_Q3 := ltac:(let x := eval cbv beta iota delta [hcr5_tl hcr5_seql firstn skipn hcr5_tstmts] in (hcr5_seql (hcr5_tl 12 2)) in exact x).
Definition hcr5_Q4 := ltac:(let x := eval cbv beta iota delta [hcr5_tl hcr5_seql firstn skipn hcr5_tstmts] in (hcr5_seql (hcr5_tl 14 3)) in exact x).
Definition hcr5_Q5 := ltac:(let x := eval cbv beta iota delta [hcr5_tl hcr5_seql firstn skipn hcr5_tstmts] in (hcr5_seql (hcr5_tl 17 2)) in exact x).

Lemma hcr5_P6_eq :
  hcr5_P6 =
  Sifthenelse hcr5_cond
    (hcr5_seqs (hcr5_tl 0 3) (hcr5_seqs (hcr5_tl 3 1) (hcr5_seqs (hcr5_tl 4 8) (hcr5_seqs (hcr5_tl 12 2)
      (hcr5_seqs (hcr5_tl 14 3) (hcr5_seql (hcr5_tl 17 2)))))))
    Sskip.
Proof. reflexivity. Qed.

Lemma hcr5_qphases_eq :
  hcr5_Q1a = hcr5_seql (hcr5_tl 0 3) /\ hcr5_Q1b = hcr5_seql (hcr5_tl 3 1) /\
  hcr5_Q2 = hcr5_seql (hcr5_tl 4 8) /\ hcr5_Q3 = hcr5_seql (hcr5_tl 12 2) /\
  hcr5_Q4 = hcr5_seql (hcr5_tl 14 3) /\ hcr5_Q5 = hcr5_seql (hcr5_tl 17 2).
Proof. repeat split. Qed.

(* ---------------------------------------------------------------------- *)
(* The locals and the globals                                              *)
(* ---------------------------------------------------------------------- *)

(* the addresses of main's 19 local variables *)
Record hcr5_loc := mkLoc5 {
  l_wa: val; l_ita: val; l_pta: val; l_ia: val; l_ib: val; l_rawa: val; l_rawb: val; l_pub: val;
  l_img: val; l_imga: val; l_peers: val; l_ds: val; l_ss: val; l_st: val; l_mr: val; l_cur: val;
  l_eraw: val; l_ei: val; l_before: val }.

Definition hcr5_lvars (gv: globals) (L: hcr5_loc) : list localdef :=
  [lvar HR5._wa t_dev (l_wa L); lvar HR5._ita t_itab (l_ita L); lvar HR5._pta t_ptab (l_pta L);
   lvar HR5._ia t_mident (l_ia L); lvar HR5._ib t_mident (l_ib L);
   lvar HR5._raw_a (tarray tuchar 32) (l_rawa L); lvar HR5._raw_b (tarray tuchar 32) (l_rawb L);
   lvar HR5._pub (tarray tuchar 32) (l_pub L);
   lvar HR5._img (tarray tuchar 92) (l_img L); lvar HR5._img_after (tarray tuchar 92) (l_imga L);
   lvar HR5._peers (tptr t_hnode4) (l_peers L);
   lvar HR5._ds t_devsnap (l_ds L); lvar HR5._ss t_shimsnap (l_ss L);
   lvar HR5._st t_mstate (l_st L); lvar HR5._mr t_mresp (l_mr L); lvar HR5._cur t_mstate (l_cur L);
   lvar HR5._eraw (tarray tuchar 32) (l_eraw L); lvar HR5._ei (tarray tuchar 32) (l_ei L);
   lvar HR5._before t_mstate (l_before L);
   gvars gv].

(* the harness's constant (common.h's M_BASEPOINT, renamed in this unit) *)
Definition hcr5_consts (gv: globals) : mpred :=
  hc_const gv HR5._x_consume_response_any__M_BASEPOINT basepoint9.

(* the shim's state at the start (all globals zero) and the refcount_t warnings (zero, and never raised) *)
Definition hcr5_shim0 : shim :=
  mkShim Int64.zero Int64.zero Int64.zero zeros32 zeros32 Int.zero Int64.zero Int64.zero Int64.zero false
         Int64.zero false.
Definition hcr5_w0 : list int64 := repeat Int64.zero 5.

(* the globals of a state: allocator, shim (warnings hcr5_w0), noise.c's globals (no keypair is ever created by
   the protocol: keypair_counter stays 0), the read-only tables, the harness's constant *)
Definition hcr5_globs (gv: globals) (S: shim) (FR: mpred) : list mpred :=
  [mem_mgr gv; shim_state4 gv S hcr5_w0; noise_globals gv Int64.zero; wg_consts gv; hcr5_consts gv; FR].

(* the scratch locals, any contents: pub, img_after, st, mr, cur, eraw, ei, before (img is listed apart) *)
Definition hcr5_scr (L: hcr5_loc) : list mpred :=
  [hout Tsh 32 (l_pub L); hout Tsh 92 (l_imga L);
   @data_at_ HCS Tsh t_mstate (l_st L); @data_at_ HCS Tsh t_mresp (l_mr L);
   @data_at_ HCS Tsh t_mstate (l_cur L);
   hout Tsh 32 (l_eraw L); hout Tsh 32 (l_ei L); @data_at_ HCS Tsh t_mstate (l_before L)].

(* the whole-state snapshots ds (dev_snap) and ss (shim_snap): not taken / taken (device D with first peer h,
   shim S with the warnings hcr5_w0) *)
Definition hcr5_snaps0 (L: hcr5_loc) : list mpred :=
  [@data_at_ CKS Tsh t_devsnap (l_ds L); @data_at_ CKS Tsh t_shimsnap (l_ss L)].
Definition hcr5_snaps (L: hcr5_loc) (D: device) (h: val) (S: shim) : list mpred :=
  [@data_at CKS Tsh t_devsnap (devsnap_val D h) (l_ds L);
   @data_at CKS Tsh t_shimsnap (shimsnap_val S hcr5_w0) (l_ss L)].

(* a malloc'd object (the token at the world) *)
Definition hcr5_tok (t: type) (p: val) : mpred := @malloc_token W Ews t p.

(* ---------------------------------------------------------------------- *)
(* The peers, the nodes and the kents                                      *)
(* ---------------------------------------------------------------------- *)

(* the head of the node list / of the kents' list *)
Definition hcr5_head (NS: list hnode4) : val := match NS with [] => nullval | N :: _ => hn_addr N end.
Definition hcr5_khead (KE: list kent4) : val := match KE with [] => nullval | e :: _ => ke_addr e end.

(* the node of the peer at a (the first one; the peers' addresses are distinct), or NULL *)
Fixpoint hcr5_nfind (NS: list hnode4) (a: val) : val :=
  match NS with
  | [] => nullval
  | N :: NS' => if eq_dec (hn_p N) a then hn_addr N else hcr5_nfind NS' a
  end.

(* every peer of A: malloc'd (share Ews, a pointer), of device wa, with A's static identity, field lengths, a
   reference count below INT_MAX (draw_peer_refs), keypair slots NULL or kents (KA: the kents' addresses) *)
Definition hcr5_pok (L: hcr5_loc) (KA: list val) (x: val * share * peer) : Prop :=
  match x with (a, sh, P) =>
    sh = Ews /\ isptr a /\ p_device P = l_wa L /\ hs_sid (p_hs P) = id_addr (l_wa L) /\ hs_ok (p_hs P) /\
    0 < Int.unsigned (p_refs P) < 2147483647 /\
    Forall (fun v => v = nullval \/ In v KA) [p_cur P; p_prev P; p_next P]
  end.

(* the lists: peers PS (chain from head, distinct addresses), nodes NS (same peers, same order), nb = B's node
   or NULL *)
Definition hcr5_list_ok (L: hcr5_loc) (KA: list val) (NS: list hnode4) (PS: list (val * share * peer))
  (head nb: val) : Prop :=
  Forall (hcr5_pok L KA) PS /\ peers_wf PS /\ pk_chain head PS /\ hnodes_peers4 NS PS /\
  NoDup (map peer_addr4 PS) /\ (nb = nullval \/ In nb (map hn_addr NS)).

(* the kents' addresses *)
Definition hcr5_ka (KE: list kent4) : list val := map ke_addr KE.

Section Run.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).

(* A after setup_device *)
Definition hcr5_DAL (R: hcr5_run) (L: hcr5_loc) : device := hcr5_DA x25519 R (l_wa L) (l_ita L) (l_pta L).

(* the objects that live from the setup to the end: A's device and tables, the identities, the raw keys, the
   local `peers` (the head of NS), the node list (contents NS') *)
Definition hcr5_world (R: hcr5_run) (L: hcr5_loc) (NS NS': list hnode4) (head: val) (T: tstate)
  : list mpred :=
  [device_rep Tsh (l_wa L) (hcr5_DAL R L); itable Tsh (l_ita L) T; ptable Tsh (l_pta L) head;
   @data_at HCS Tsh t_mident (mident_val (hcr5_IA x25519 R)) (l_ia L);
   @data_at HCS Tsh t_mident (mident_val (hcr5_IB x25519 R)) (l_ib L);
   hbytes Tsh (r5_rawa R) (l_rawa L); hbytes Tsh (r5_rawb R) (l_rawb L);
   @data_at W Tsh (tptr t_hnode4) (hcr5_head NS) (l_peers L);
   hnodes_rep4 W (hcr5_head NS) NS'].

(* the harness's model's target node *)
Definition hcr5_tnode (NS: list hnode4) (tg: option (val * peer * list byte * list byte)) : val :=
  match tg with Some (a, _, _, _) => hcr5_nfind NS a | None => nullval end.

(* st after the target block: on acceptance the model's state (ck, h) *)
Definition hcr5_st_rep (tg: option (val * peer * list byte * list byte)) (st: val) : mpred :=
  match tg with
  | Some (_, _, ck, h) => @data_at HCS Tsh t_mstate (mstate_val ck h) st
  | None => @data_at_ HCS Tsh t_mstate st
  end.

(* the kernel's result *)
Definition hcr5_res (R: hcr5_run) (L: hcr5_loc) (T: tstate) (PS: list (val * share * peer)) (M: resp_msg)
  : option (val * peer) :=
  cre_res x25519 aead_dec (hcr5_DAL R L) T PS M.

(* the model's result *)
Definition hcr5_tg (R: hcr5_run) (T: tstate) (PS: list (val * share * peer)) (M: resp_msg)
  : option (val * peer * list byte * list byte) :=
  hcr5_tgt x25519 aead_dec (hcr5_IA x25519 R) T PS M.

End Run.

(* the snapshots the harness takes before the call, of the peers PS (in node order) *)
Definition hcr5_sns (T: tstate) (PS: list (val * share * peer)) : list hsnap :=
  map (fun x => match x with (p, _, P) => hs_snap_cur T p P end) PS.
Definition hcr5_rs (PS: list (val * share * peer)) : list int :=
  map (fun x => match x with (_, _, P) => p_refs P end) PS.
Definition hcr5_prs (PS: list (val * share * peer)) : list peer :=
  map (fun x => match x with (_, _, P) => P end) PS.

(* the return (P7): the device back to its struct; the index table and the peers back to the table's struct,
   each peer's whole struct at the world (as hnodes_free needs them) and each kent's entry (as kents_free needs
   them) (pure separation logic from hcr5_rep; hcr5_close.v proves it) *)
Definition hcr5_closeH : Prop :=
  (forall sh wg D, device_rep sh wg D |-- @data_at_ Noise.CS sh t_dev wg) /\
  (forall tab KE PS NS T,
     hcr5_pool (hcr5_ka KE) PS T -> hnodes_peers4 NS PS ->
     Forall (fun x : val * share * peer => match x with (_, sh, _) => sh = Ews end) PS ->
     itable Tsh tab T * peers_rep PS |--
     @data_at_ Noise.CS Tsh t_itab tab * iter_sepcon (fun N => @data_at_ W Ews t_peer (hn_p N)) NS *
     iter_sepcon (fun e => @data_at_ Noise.CS Ews t_entry_s (ke_addr e)) KE).

(* ---------------------------------------------------------------------- *)
(* The states                                                              *)
(* ---------------------------------------------------------------------- *)

Section States.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).

(* after the prologue: the stack frame converted, the initial globals *)
Definition hcr5_S0 (gv: globals) (L: hcr5_loc) (FR: mpred) : environ -> mpred :=
  PROPx []
  (LOCALx (hcr5_lvars gv L)
  (SEPx ([@data_at_ Noise.CS Tsh t_dev (l_wa L); @data_at_ Noise.CS Tsh t_itab (l_ita L);
          @data_at_ Noise.CS Tsh t_ptab (l_pta L);
          @data_at_ HCS Tsh t_mident (l_ia L); @data_at_ HCS Tsh t_mident (l_ib L);
          hout Tsh 32 (l_rawa L); hout Tsh 32 (l_rawb L); @data_at_ W Tsh (tptr t_hnode4) (l_peers L);
          hout Tsh 92 (l_img L);
          mem_mgr gv; shim_state4 gv hcr5_shim0 hcr5_w0; noise_globals_raw gv zeros32 zeros32 Int64.zero;
          wg_consts gv; hcr5_consts gv; FR] ++ hcr5_snaps0 L ++ hcr5_scr L))).

(* after P1 (and after P2, P3: the same invariant): A set up, its peers (B's first if its allocation succeeded;
   any number of others; randomized, rest randomized and some hashed after P3), nb = B's node or NULL, no kent *)
Definition hcr5_SA (gv: globals) (L: hcr5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hcr5_run, EX S: shim, EX NS: list hnode4, EX PS: list (val * share * peer), EX head: val, EX nb: val,
  EX T: tstate,
  PROPx [hcr5_run_ok R; hcr5_list_ok L [] NS PS head nb; hcr5_pool [] PS T]
  (LOCALx ([temp HR5._nb nb] ++ hcr5_lvars gv L)
  (SEPx (hcr5_world x25519 R L NS NS head T ++
         [peers_rep PS; hout Tsh 92 (l_img L)] ++ hcr5_globs gv S FR ++ hcr5_snaps0 L ++ hcr5_scr L))).

(* after PK: the kents KE (any keypairs of any peers, their entries in the table, possibly in the slots) *)
Definition hcr5_SK (gv: globals) (L: hcr5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hcr5_run, EX S: shim, EX NS: list hnode4, EX PS: list (val * share * peer), EX head: val, EX nb: val,
  EX T: tstate, EX KE: list kent4,
  PROPx [hcr5_run_ok R; hcr5_list_ok L (hcr5_ka KE) NS PS head nb; hcr5_pool (hcr5_ka KE) PS T]
  (LOCALx ([temp HR5._nb nb; temp HR5._kes (hcr5_khead KE)] ++ hcr5_lvars gv L)
  (SEPx (hcr5_world x25519 R L NS NS head T ++
         [peers_rep PS; hout Tsh 92 (l_img L); kents_rep W (hcr5_khead KE) KE] ++
         hcr5_globs gv S FR ++ hcr5_snaps0 L ++ hcr5_scr L))).

(* the message buffer after malloc: NULL, or a token and uninitialised memory *)
Definition hcr5_mbuf (m: val) : mpred :=
  if eq_dec m nullval then emp else (hcr5_tok t_resp m * @data_at_ Noise.CS Ews t_resp m).

(* after P5: msg = malloc(..) *)
Definition hcr5_S5 (gv: globals) (L: hcr5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hcr5_run, EX S: shim, EX NS: list hnode4, EX PS: list (val * share * peer), EX head: val, EX nb: val,
  EX T: tstate, EX KE: list kent4, EX m: val,
  PROPx [hcr5_run_ok R; hcr5_list_ok L (hcr5_ka KE) NS PS head nb; hcr5_pool (hcr5_ka KE) PS T]
  (LOCALx ([temp HR5._nb nb; temp HR5._kes (hcr5_khead KE); temp HR5._msg m] ++ hcr5_lvars gv L)
  (SEPx (hcr5_world x25519 R L NS NS head T ++
         [peers_rep PS; hout Tsh 92 (l_img L); kents_rep W (hcr5_khead KE) KE; hcr5_mbuf m] ++
         hcr5_globs gv S FR ++ hcr5_snaps0 L ++ hcr5_scr L))).

(* the then-branch's start: msg <> NULL *)
Definition hcr5_S5n (gv: globals) (L: hcr5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hcr5_run, EX S: shim, EX NS: list hnode4, EX PS: list (val * share * peer), EX head: val, EX nb: val,
  EX T: tstate, EX KE: list kent4, EX m: val,
  PROPx [hcr5_run_ok R; hcr5_list_ok L (hcr5_ka KE) NS PS head nb; hcr5_pool (hcr5_ka KE) PS T; m <> nullval]
  (LOCALx ([temp HR5._nb nb; temp HR5._kes (hcr5_khead KE); temp HR5._msg m] ++ hcr5_lvars gv L)
  (SEPx (hcr5_world x25519 R L NS NS head T ++
         [peers_rep PS; hout Tsh 92 (l_img L); kents_rep W (hcr5_khead KE) KE;
          hcr5_tok t_resp m; @data_at_ Noise.CS Ews t_resp m] ++
         hcr5_globs gv S FR ++ hcr5_snaps0 L ++ hcr5_scr L))).

(* after Q1a: msg holds ANY well-formed response M; mode = nondet_u8() % 3 *)
Definition hcr5_SQ1a (gv: globals) (L: hcr5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hcr5_run, EX S: shim, EX NS: list hnode4, EX PS: list (val * share * peer), EX head: val, EX nb: val,
  EX T: tstate, EX KE: list kent4, EX m: val, EX M: resp_msg, EX mode: Z,
  PROPx [hcr5_run_ok R; hcr5_list_ok L (hcr5_ka KE) NS PS head nb; hcr5_pool (hcr5_ka KE) PS T; m <> nullval;
         rm_ok M; 0 <= mode < 3]
  (LOCALx ([temp HR5._nb nb; temp HR5._kes (hcr5_khead KE); temp HR5._msg m;
            temp HR5._mode (Vint (Int.repr mode))] ++ hcr5_lvars gv L)
  (SEPx (hcr5_world x25519 R L NS NS head T ++
         [peers_rep PS; hout Tsh 92 (l_img L); kents_rep W (hcr5_khead KE) KE;
          hcr5_tok t_resp m; resp_rep Ews m M] ++
         hcr5_globs gv S FR ++ hcr5_snaps0 L ++ hcr5_scr L))).

(* after Q1b: msg holds ANY well-formed response M (the mode block's result) *)
Definition hcr5_SQ1b (gv: globals) (L: hcr5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hcr5_run, EX S: shim, EX NS: list hnode4, EX PS: list (val * share * peer), EX head: val, EX nb: val,
  EX T: tstate, EX KE: list kent4, EX m: val, EX M: resp_msg,
  PROPx [hcr5_run_ok R; hcr5_list_ok L (hcr5_ka KE) NS PS head nb; hcr5_pool (hcr5_ka KE) PS T; m <> nullval;
         rm_ok M]
  (LOCALx ([temp HR5._kes (hcr5_khead KE); temp HR5._msg m] ++ hcr5_lvars gv L)
  (SEPx (hcr5_world x25519 R L NS NS head T ++
         [peers_rep PS; hout Tsh 92 (l_img L); kents_rep W (hcr5_khead KE) KE;
          hcr5_tok t_resp m; resp_rep Ews m M] ++
         hcr5_globs gv S FR ++ hcr5_snaps0 L ++ hcr5_scr L))).

(* after Q2: img = M's image; the nodes hold their peers' snapshots, the kents theirs, ds the device and its
   public-key table's first peer, head0 the table's first entry, ss the shim (all taken before the call, the
   boot clock drawn: any shim S); the peers are the kernel's result; ret = the returned peer *)
Definition hcr5_SQ2 (gv: globals) (L: hcr5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hcr5_run, EX S: shim, EX NS: list hnode4, EX PS: list (val * share * peer), EX head: val, EX nb: val,
  EX T: tstate, EX KE: list kent4, EX m: val, EX M: resp_msg,
  PROPx [hcr5_run_ok R; hcr5_list_ok L (hcr5_ka KE) NS PS head nb; hcr5_pool (hcr5_ka KE) PS T; m <> nullval;
         rm_ok M]
  (LOCALx ([temp HR5._kes (hcr5_khead KE); temp HR5._msg m; temp HR5._head0 (hd nullval (t_L T));
            temp HR5._ret (peer_result (hcr5_res x25519 aead_dec R L T PS M))] ++
           hcr5_lvars gv L)
  (SEPx (hcr5_world x25519 R L NS (hnodes_snapped4 T NS PS) head T ++
         [peers_rep (peers_after PS (hcr5_res x25519 aead_dec R L T PS M));
          hbytes Tsh (resp_bytes M) (l_img L); kents_rep W (hcr5_khead KE) (map (kent_snapped T) KE);
          hcr5_tok t_resp m; resp_rep Ews m M] ++
         hcr5_globs gv S FR ++ hcr5_snaps L (hcr5_DAL x25519 R L) head S ++ hcr5_scr L))).

(* after Q3: target = the harness's model's node; st = its state on acceptance *)
Definition hcr5_SQ3 (gv: globals) (L: hcr5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hcr5_run, EX S: shim, EX NS: list hnode4, EX PS: list (val * share * peer), EX head: val, EX nb: val,
  EX T: tstate, EX KE: list kent4, EX m: val, EX M: resp_msg,
  PROPx [hcr5_run_ok R; hcr5_list_ok L (hcr5_ka KE) NS PS head nb; hcr5_pool (hcr5_ka KE) PS T; m <> nullval;
         rm_ok M]
  (LOCALx ([temp HR5._kes (hcr5_khead KE); temp HR5._msg m; temp HR5._head0 (hd nullval (t_L T));
            temp HR5._ret (peer_result (hcr5_res x25519 aead_dec R L T PS M));
            temp HR5._target (hcr5_tnode NS (hcr5_tg x25519 aead_dec R T PS M))] ++
           hcr5_lvars gv L)
  (SEPx (hcr5_world x25519 R L NS (hnodes_snapped4 T NS PS) head T ++
         [peers_rep (peers_after PS (hcr5_res x25519 aead_dec R L T PS M));
          hbytes Tsh (resp_bytes M) (l_img L); kents_rep W (hcr5_khead KE) (map (kent_snapped T) KE);
          hcr5_tok t_resp m; resp_rep Ews m M;
          hcr5_st_rep (hcr5_tg x25519 aead_dec R T PS M) (l_st L)] ++
         hcr5_globs gv S FR ++ hcr5_snaps L (hcr5_DAL x25519 R L) head S ++
         [hout Tsh 32 (l_pub L); hout Tsh 92 (l_imga L);
          @data_at_ HCS Tsh t_mresp (l_mr L); @data_at_ HCS Tsh t_mstate (l_cur L);
          hout Tsh 32 (l_eraw L); hout Tsh 32 (l_ei L); @data_at_ HCS Tsh t_mstate (l_before L)]))).

(* after Q4: the image and the whole-state frame checked (img_after = M's image) *)
Definition hcr5_SQ4 (gv: globals) (L: hcr5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hcr5_run, EX S: shim, EX NS: list hnode4, EX PS: list (val * share * peer), EX head: val, EX nb: val,
  EX T: tstate, EX KE: list kent4, EX m: val, EX M: resp_msg,
  PROPx [hcr5_run_ok R; hcr5_list_ok L (hcr5_ka KE) NS PS head nb; hcr5_pool (hcr5_ka KE) PS T; m <> nullval;
         rm_ok M]
  (LOCALx ([temp HR5._kes (hcr5_khead KE); temp HR5._msg m;
            temp HR5._ret (peer_result (hcr5_res x25519 aead_dec R L T PS M));
            temp HR5._target (hcr5_tnode NS (hcr5_tg x25519 aead_dec R T PS M))] ++
           hcr5_lvars gv L)
  (SEPx (hcr5_world x25519 R L NS (hnodes_snapped4 T NS PS) head T ++
         [peers_rep (peers_after PS (hcr5_res x25519 aead_dec R L T PS M));
          hbytes Tsh (resp_bytes M) (l_img L); kents_rep W (hcr5_khead KE) (map (kent_snapped T) KE);
          hcr5_tok t_resp m; resp_rep Ews m M;
          hcr5_st_rep (hcr5_tg x25519 aead_dec R T PS M) (l_st L)] ++
         hcr5_globs gv S FR ++ hcr5_snaps L (hcr5_DAL x25519 R L) head S ++
         [hout Tsh 32 (l_pub L); hbytes Tsh (resp_bytes M) (l_imga L);
          @data_at_ HCS Tsh t_mresp (l_mr L); @data_at_ HCS Tsh t_mstate (l_cur L);
          hout Tsh 32 (l_eraw L); hout Tsh 32 (l_ei L); @data_at_ HCS Tsh t_mstate (l_before L)]))).

(* after P6 (both branches): the message is gone; the peers PS (any, same addresses), the nodes NS' (any
   snapshots), the kents KE (any snapshots), the table's pool as before *)
Definition hcr5_SE (gv: globals) (L: hcr5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hcr5_run, EX S: shim, EX NS: list hnode4, EX NS': list hnode4, EX PS: list (val * share * peer),
  EX head: val, EX T: tstate, EX KE: list kent4,
  PROPx [hcr5_run_ok R; hnodes_peers4 NS' PS; peers_wf PS; hcr5_pool (hcr5_ka KE) PS T;
         Forall (fun x : val * share * peer => match x with (_, sh, _) => sh = Ews end) PS]
  (LOCALx ([temp HR5._kes (hcr5_khead KE)] ++ hcr5_lvars gv L)
  (SEPx (hcr5_world x25519 R L NS NS' head T ++
         [peers_rep PS; hout Tsh 92 (l_img L); kents_rep W (hcr5_khead KE) KE] ++
         hcr5_globs gv S FR ++ hcr5_snaps0 L ++ hcr5_scr L))).

End States.

(* main's post (TT) weakened to the canonical form forward needs for a return *)
Lemma hcr5_post_canon {Espec: OracleKind} {cs: compspecs} Delta P c Q gv F :
  semax Delta P c (overridePost Q (frame_ret_assert (function_body_ret_assert tint (PROP () LOCAL () SEP (TT))) F)) ->
  semax Delta P c (overridePost Q (frame_ret_assert (function_body_ret_assert tint (hcr5_post gv)) F)).
Proof.
  intros H. eapply semax_post; [| | | | apply H]; intros; simpl; intros rho; apply andp_left2;
    try apply derives_refl.
  apply sepcon_derives; [| apply derives_refl]. revert rho. apply bind_ret_derives. intros rho. apply TT_right.
Qed.
