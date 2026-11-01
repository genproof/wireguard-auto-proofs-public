(* law prim_aead: check_decrypt_any, segment C (nondet_bytes(d2), bytes_copy(d2_before, d2), ok = kernel decrypt, rok = reference decrypt).
   the cut and the states: haead_cda_body3_defs.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.harness.prim_aead.haead_spec3.
Require Import WgNoise.proof.harness.prim_aead.haead_lemmas3.
Require WgNoise.harness.x_prim_aead.code.
Require Import WgNoise.proof.harness.prim_aead.haead_cda_body3_defs.

#[local] Existing Instance W_prim_aead.
Local Open Scope Z_scope.

(* nondet_bytes' result as bytes *)
Lemma cdaC_bytes_Vubyte (bs: list Z) :
  Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  map (fun b => Vint (Int.repr b)) bs = map Vubyte (map Byte.repr bs).
Proof.
  induction 1; simpl; auto. f_equal; auto.
  unfold Vubyte. rewrite Byte.unsigned_repr by (unfold Byte.max_unsigned in *; lia). reflexivity.
Qed.

(* exact byte array <-> the kernel AEAD's prim_bytes (emp when empty) *)
Lemma cdaC_prim (sh: share) (l: list byte) (p: val) :
  data_at sh (tarray tuchar (Zlength l)) (map Vubyte l) p =
  (prim_bytes sh l p * (if Z.eq_dec (Zlength l) 0 then data_at sh (tarray tuchar (Zlength l)) (map Vubyte l) p else emp))%logic.
Proof.
  unfold prim_bytes. destruct (Z.eq_dec (Zlength l) 0).
  - rewrite emp_sepcon; auto.
  - rewrite sepcon_emp; auto.
Qed.

Lemma cdaC_prim_back (sh: share) (l: list byte) (p: val) :
  (prim_bytes sh l p * (if Z.eq_dec (Zlength l) 0 then data_at sh (tarray tuchar (Zlength l)) (map Vubyte l) p else emp))%logic
  |-- data_at sh (tarray tuchar (Zlength l)) (map Vubyte l) p.
Proof. rewrite <- cdaC_prim. apply derives_refl. Qed.

Lemma cda_C_ok {Espec: OracleKind} (x: Z) (ksh: share) (kp: val) (key: list byte) (nonce: Z) (xsh: share) (xp: val) (xnonce: list byte)
  (ash: share) (ad: val) (a: list byte) (csh: share) (cp: val) (ct: list byte) (gv: globals) (c: list byte) (c2 d2 db rd2: val) (rest: statement) :
  readable_share ksh -> readable_share xsh -> readable_share ash -> readable_share csh ->
  Int.min_signed <= x <= Int.max_signed -> Zlength key = 32 -> 0 <= nonce <= Int64.max_unsigned ->
  Zlength xnonce = 24 -> Zlength a <= Int64.max_signed -> 16 <= Zlength ct <= Int64.max_signed ->
  (forall bs, semax cda_Delta (cda_P3 x ksh kp key nonce xsh xp xnonce ash ad a csh cp ct gv c c2 d2 db rd2 bs) rest (cda_R x ksh kp key nonce xsh xp xnonce ash ad a csh cp ct gv)) ->
  semax cda_Delta (cda_P2 x ksh kp key nonce xsh xp xnonce ash ad a csh cp ct gv c c2 d2 db rd2) (cda_seqs cda_lC rest) (cda_R x ksh kp key nonce xsh xp xnonce ash ad a csh cp ct gv).
Proof.
intros. unfold cda_lC; simpl cda_seqs. unfold cda_Delta, cda_P2, cda_R. simplify_func_tycontext. abbreviate_semax.
Intros. set (n := Z.max 0 (Zlength c - 16)).
assert (Hn: 0 <= n <= Int64.max_unsigned) by (unfold n; rep_lia).
forward_call (d2, n, Ews).
Intros bs.
rewrite (cdaC_bytes_Vubyte bs) by auto. set (bb := map Byte.repr bs).
assert (Hbb: Zlength bb = n) by (unfold bb; rewrite Zlength_map; auto). clearbody bb. clear dependent bs.
rewrite <- Hbb. forward_call (Ews, db, Ews, d2, bb).
rewrite (cdaC_prim Ews c c2), (cdaC_prim ash a ad). Intros.
destruct (Int.eq (Int.repr x) Int.zero) eqn:Ex.
- apply int_eq_e in Ex.
  apply -> seq_assoc; apply semax_if_seq. forward_if.
  { contradiction. }
  forward_call (Ews, d2, map Vubyte bb, Ews, c2, c, ash, ad, a, nonce, ksh, kp, key, gv).
  { rewrite Zlength_map; cancel. }
  { rewrite Zlength_map; lia. }
  remember (aead_dec key nonce a c) as d eqn:Hd. rewrite Zlength_map.
  forward.
  sep_apply (cdaC_prim_back Ews c c2). sep_apply (cdaC_prim_back ash a ad).
  change (data_at_ Ews (tarray tuchar (Zlength bb)) rd2) with (data_at Ews (tarray tuchar (Zlength bb)) (Zrepeat Vundef (Zlength bb)) rd2).
  apply -> seq_assoc; apply semax_if_seq. forward_if.
  { contradiction. }
  forward_call (Ews, rd2, Zrepeat Vundef (Zlength bb), Ews, c2, c, ash, ad, a, nonce, ksh, kp, key, gv).
  { rewrite Zlength_Zrepeat by lia; cancel. }
  { rewrite Zlength_Zrepeat by lia; lia. }
  rewrite <- Hd, Zlength_Zrepeat by lia.
  forward.
  eapply semax_pre; [| apply (H9 bb)].
  unfold cda_P3, cda_dec, cda_rout, cda_out. rewrite Ex, Int.eq_true, <- Hd, Hbb. unfold n.
  destruct d; entailer!.
- assert (Hx: Int.repr x <> Int.zero) by (intro E; rewrite E, Int.eq_true in Ex; discriminate).
  apply -> seq_assoc; apply semax_if_seq. forward_if; [| contradiction].
  forward_call (Ews, d2, map Vubyte bb, Ews, c2, c, ash, ad, a, xsh, xp, xnonce, ksh, kp, key, gv).
  { rewrite Zlength_map; cancel. }
  { rewrite Zlength_map; lia. }
  remember (xaead_dec key xnonce a c) as d eqn:Hd. rewrite Zlength_map.
  forward.
  sep_apply (cdaC_prim_back Ews c c2). sep_apply (cdaC_prim_back ash a ad).
  change (data_at_ Ews (tarray tuchar (Zlength bb)) rd2) with (data_at Ews (tarray tuchar (Zlength bb)) (Zrepeat Vundef (Zlength bb)) rd2).
  apply -> seq_assoc; apply semax_if_seq. forward_if; [| contradiction].
  forward_call (Ews, rd2, Zrepeat Vundef (Zlength bb), Ews, c2, c, ash, ad, a, xsh, xp, xnonce, ksh, kp, key, gv).
  { rewrite Zlength_Zrepeat by lia; cancel. }
  { rewrite Zlength_Zrepeat by lia; lia. }
  rewrite <- Hd, Zlength_Zrepeat by lia.
  forward.
  eapply semax_pre; [| apply (H9 bb)].
  unfold cda_P3, cda_dec, cda_rout, cda_out. rewrite Ex, <- Hd, Hbb. unfold n.
  destruct d; entailer!.
Qed.

