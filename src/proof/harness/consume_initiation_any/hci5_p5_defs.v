(* law consume_initiation_any: the states inside P5 and its cut
   into segments A = statements 15..17 (fill_init, mode, the mode block), B = 18 (the replay boundary), C = 19
   (init_img). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_cut.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_model.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_globals.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_spec.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_defs.
Require WgNoise.harness.x_consume_initiation_any.code.
Local Open Scope logic.

(* the condition `mode != 0 && na != NULL` (statements 17 and 18) *)
Definition hci5_p5_c (md: int) (na: val) : bool :=
  if Int.eq md Int.zero then false else if eq_dec na nullval then false else true.

(* the local ts after the mode block: 12 bytes (m_tai64n's) when the block ran, else any contents *)
Definition hci5_p5_tsrep (c: bool) (ts: val) : mpred :=
  if c then EX t: list byte, !! (Zlength t = 12) && hbytes Tsh t ts else hout Tsh 12 ts.

(* hci5_scr with ts given by tsr *)
Definition hci5_p5_scr (L: hci5_loc) (tsr: mpred) : list mpred :=
  [hout Tsh 32 (l_pub L); tsr; hout Tsh 148 (l_imga L);
   @data_at_ HCS Tsh t_mcinit (l_ci L); @data_at_ HCS Tsh t_minit (l_mi L);
   hout Tsh 32 (l_eraw L); hout Tsh 32 (l_ss1 L); hout Tsh 32 (l_ss2 L)].

Section States.
Variable x25519: list byte -> list byte -> list byte.

(* after statement 17: msg holds ANY well-formed initiation M, mode = md *)
Definition hci5_p5_Q17 (gv: globals) (L: hci5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hci5_run, EX S: shim, EX w: list int64, EX NS: list hnode4, EX PS: list (val * share * peer),
  EX T: tstate, EX head: val, EX na: val, EX KE: list kent4, EX m: val, EX M: init_msg, EX md: int,
  PROPx [hci5_run_ok R; hci5_inv x25519 R L NS PS KE T head na; im_ok M]
  (LOCALx ([temp HC._mode (Vint md); temp HC._na na; temp HC._kes (hci5_khead KE); temp HC._msg m] ++
           hci5_lvars gv L)
  (SEPx (hci5_world x25519 R L NS NS T head ++
         [peers_rep PS; kents_rep W (hci5_khead KE) KE; hout Tsh 148 (l_img L);
          hci5_tok t_init m; init_rep Ews m M] ++
         hci5_globs gv S w FR ++ hci5_snaps0 L ++
         hci5_p5_scr L (hci5_p5_tsrep (hci5_p5_c md na) (l_ts L))))).

(* after statement 18: A's latest timestamp may have moved (PS: the peers after it) *)
Definition hci5_p5_Q18 (gv: globals) (L: hci5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hci5_run, EX S: shim, EX w: list int64, EX NS: list hnode4, EX PS: list (val * share * peer),
  EX T: tstate, EX head: val, EX na: val, EX KE: list kent4, EX m: val, EX M: init_msg,
  PROPx [hci5_run_ok R; hci5_inv x25519 R L NS PS KE T head na; im_ok M]
  (LOCALx ([temp HC._na na; temp HC._kes (hci5_khead KE); temp HC._msg m] ++ hci5_lvars gv L)
  (SEPx (hci5_world x25519 R L NS NS T head ++
         [peers_rep PS; kents_rep W (hci5_khead KE) KE; hout Tsh 148 (l_img L);
          hci5_tok t_init m; init_rep Ews m M] ++
         hci5_globs gv S w FR ++ hci5_snaps0 L ++ hci5_scr L))).

End States.

(* the cut *)
Lemma hci5_p5_cut : hci5_P5 = hci5_seql (hci5_l 15 3 ++ hci5_l 18 1 ++ hci5_l 19 1).
Proof. reflexivity. Qed.
