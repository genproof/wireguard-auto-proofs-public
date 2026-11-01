(* law keypairs: the statements of main's segments, of the context lifting, of the
   initial globals and of the law's own piece as Props, so that main's glue and the
   assembly are proved from them as HYPOTHESES (the segment lemmas hkp5_seg*_ok, hkp5_bridge_ok, hkp5_init_globals,
   hkp5_*_body discharge them in keypairs_safe5). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Export WgNoise.proof.harness.keypairs.hkp5_op1.
Require Export WgNoise.proof.harness.keypairs.hkp5_spec.
Require WgNoise.contracts.x_keypairs.

#[local] Existing Instance W_keypairs.
Local Open Scope logic.

(* the loop's segments (hkp5_segL0.v, hkp5_segOp*.v, hkp5_segLC.v) *)
Definition hkp5_S_L0 : Prop := forall (Espec: OracleKind) x25519 (F: hkp5_fix) V steps FR i R,
  semax (hkp5_Delta hkp5_G_L0) (hkp5_Icont x25519 F V steps FR i) hkp5_segL0
    (overridePost (EX op: Z, hkp5_PL0 x25519 F V steps FR i op) R).

Definition hkp5_S_op (n: Z) (G: funspecs) (s: statement) : Prop :=
  forall (Espec: OracleKind) x25519 (F: hkp5_fix) V steps FR i R,
  hkp5_model_facts -> x25519_props x25519 ->
  semax (hkp5_Delta G) (hkp5_PL0 x25519 F V steps FR i n) s (loop1_ret_assert (hkp5_Icont x25519 F V steps FR i) R).

Definition hkp5_S_Op45 : Prop := forall (Espec: OracleKind) x25519 (F: hkp5_fix) V steps FR i op R,
  hkp5_model_facts -> x25519_props x25519 -> op = 4 \/ op = 5 ->
  semax (hkp5_Delta hkp5_G_Op45) (hkp5_PL0 x25519 F V steps FR i op) hkp5_sOp45
    (loop1_ret_assert (hkp5_Icont x25519 F V steps FR i) R).

Definition hkp5_S_Op1a : Prop := forall (Espec: OracleKind) x25519 (F: hkp5_fix) V steps (O: hkp5_oth) FR i R,
  hkp5_model_facts -> hkp5_oth_ok F V O ->
  semax (hkp5_Delta (hkp5_G_Op1a x25519)) (hkp5_PL0 x25519 F V steps (hkp5_othR x25519 F V O * FR) i 1) hkp5_op1_a
    (overridePost (hkp5_PL0 x25519 F V steps (hkp5_othR x25519 F V O * FR) i 1)
       (loop1_ret_assert (hkp5_Icont x25519 F V steps (hkp5_othR x25519 F V O * FR) i) R)).

Definition hkp5_S_LC : Prop := forall (Espec: OracleKind) x25519 (F: hkp5_fix) V steps (O: hkp5_oth) FR i R,
  hkp5_oth_ok F V O ->
  semax (hkp5_Delta (hkp5_G_LC x25519)) (hkp5_Icont x25519 F V steps (hkp5_othR x25519 F V O * FR) i) hkp5_segLC
    (loop1_ret_assert (hkp5_Icont x25519 F V steps (hkp5_othR x25519 F V O * FR) i) R).

(* the prologue and the end (hkp5_segA.v, hkp5_segF.v) *)
Definition hkp5_S_A : Prop := forall (Espec: OracleKind) x25519 (F: hkp5_fix) (FR: mpred) R,
  x25519_props x25519 ->
  semax (hkp5_Delta (hkp5_G_A x25519)) (hkp5_P0 F FR) hkp5_segA (overridePost (hkp5_PA x25519 F FR) R).

Definition hkp5_S_F : Prop := forall (Espec: OracleKind) x25519 (F: hkp5_fix) V steps (O: hkp5_oth) (FR: mpred),
  hkp5_model_facts -> x25519_props x25519 -> hkp5_oth_ok F V O ->
  semax (hkp5_Delta (hkp5_G_F x25519)) (hkp5_Inv x25519 F V steps (hkp5_othR x25519 F V O * FR)) hkp5_segF
    (overridePost FF (hkp5_R (f_gv F))).

(* the context lifting (hkp5_bridge.v) and the initial globals (hkp5_glob.v) *)
Definition hkp5_S_bridge : Prop := forall x25519 aead_enc aead_dec xaead_enc xaead_dec,
  Forall (fun G => tycontext_sub (hkp5_Delta G)
                     (func_tycontext KC.f_main hkp5_V (hkp5_Gmain x25519 aead_enc aead_dec xaead_enc xaead_dec) []))
    [hkp5_G_L0; hkp5_G_Op0; hkp5_G_Op1b; hkp5_G_Op2; hkp5_G_Op3; hkp5_G_Op7; hkp5_G_Op45; hkp5_G_Op6;
     hkp5_G_LC x25519; hkp5_G_Op1a x25519; hkp5_G_A x25519; hkp5_G_F x25519].

Definition hkp5_S_glob : Prop := forall gv,
  globals_ok gv ->
  InitGPred (Vardefs WgNoise.contracts.x_keypairs.whole_prog) gv
  |-- (shim_state4 gv hkp5_S0 (Zrepeat Int64.zero 5) * noise_globals_raw gv zeros32 zeros32 Int64.zero *
       wg_consts gv *
       (data_at_ Ews (tptr t_mk5) (gv KC._live) * data_at_ Ews (tptr t_mk5) (gv KC._s_prev) *
        data_at_ Ews (tptr t_mk5) (gv KC._s_cur) * data_at_ Ews (tptr t_mk5) (gv KC._s_next) *
        data_at_ Ews tulong (gv KC._m_frees) * data_at_ Ews (tarray tulong 5) (gv KC._m_warn) *
        data_at_ Ews (tarray tulong 5) (gv KC._warn0) * data_at_ Ews (Tstruct KC._hs_snap noattr) (gv KC._hsm) *
        data_at_ Ews (Tstruct KC._pr_snap noattr) (gv KC._prm) * data_at_ Ews tuint (gv KC._prefs) *
        data_at_ Ews (Tstruct KC._dev_snap noattr) (gv KC._dsm) *
        data_at_ Ews (tptr (Tstruct KC._hnode noattr)) (gv KC._others) *
        data_at_ Ews (tptr (Tstruct KC._kent noattr)) (gv KC._kes)) * TT)%logic.

(* all of main's parts *)
Definition hkp5_parts : Prop :=
  hkp5_model_facts /\ hkp5_S_L0 /\ hkp5_S_op 0 hkp5_G_Op0 hkp5_sOp0 /\
  hkp5_S_op 1 hkp5_G_Op1b hkp5_op1_b /\ hkp5_S_Op1a /\ hkp5_S_op 2 hkp5_G_Op2 hkp5_sOp2 /\
  hkp5_S_op 3 hkp5_G_Op3 hkp5_sOp3 /\ hkp5_S_op 7 hkp5_G_Op7 hkp5_sOp7 /\ hkp5_S_Op45 /\
  hkp5_S_op 6 hkp5_G_Op6 hkp5_sOp6 /\ hkp5_S_LC /\ hkp5_S_A /\ hkp5_S_F /\ hkp5_S_bridge /\ hkp5_S_glob.

(* ---------------------------------------------------------------------- *)
(* The law's own piece                                                     *)
(* ---------------------------------------------------------------------- *)

(* the harness unit at the world's compspecs, with the whole program's varspecs (as v1's u_hkp4) *)
Definition u_hkp5 : unit_ctx := mk_unit W_keypairs hkp5_V KC.prog.

(* its functions mk_unlink, m_get, m_put, rest_same, warn_same, check_all, pick_live, pick_held, main *)
Definition hkp5_piece_stmt : Prop :=
  forall x25519 aead_enc aead_dec xaead_enc xaead_dec,
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  piece_ok [u_hkp5] (hkp5_imports x25519 aead_enc aead_dec xaead_enc xaead_dec) (hkp5_G x25519).
