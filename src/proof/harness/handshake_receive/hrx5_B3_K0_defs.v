(* law handshake_receive, phase B3, branch kind 0: the cut of
   hrx5_B3_K0 (13 statements) into segments.
   - KA = stmts 0..5 (len = draw_size(); bump; len > 0xffffffff -> continue; buf = malloc(len); NULL -> continue;
     nondet_bytes(buf, len)): hrx5_B3_P 0 -> hrx5_K0_M
   - KI = stmt 6 (maybe K's initiation / response at the front of buf): hrx5_K0_M -> hrx5_K0_M, cut further into
       KI1 (the initiation block: fill_init(&t); k_initiation; t.header.type = 1; init_img(buf, &t)):
           hrx5_K0_Mc (nk <> NULL /\ 148 < len) -> hrx5_K0_M
       KI2 (the response block: fill_resp(&t__1); k_response(&t__1, &nk->p->handshake, &itd, &id);
            t__1.header.type = 2; resp_img(buf, &t__1)):
           hrx5_K0_Mc (nk <> NULL /\ 92 < len) -> hrx5_K0_M
   - KT = stmt 7 (maybe a type word: le32_store(buf, draw_type(1 + nondet_u8() % 4))): hrx5_K0_M -> hrx5_K0_M
   - KC = stmt 8 (maybe macs: draw_macs(buf, len, mk1, wd.cookie_checker.secret, &skb)): hrx5_K0_M -> hrx5_K0_M
   - KZ = stmts 9..12 (img = malloc(len); NULL -> free(buf), continue; bytes_copy(img, buf, len); skb.data = buf):
     hrx5_K0_M -> hrx5_B3_Q
   Every segment's ret_assert is hrx5_RB (continue = hrx5_SC). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_world.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_cut.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_model.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_spec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mspec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mci.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mcr.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_hmodel.
Require WgNoise.contracts.x_handshake_receive.
Require WgNoise.harness.x_handshake_receive.code.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B3_defs.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* the statements                                                          *)
(* ---------------------------------------------------------------------- *)

Definition hrx5_k0_l (i n: nat) : list statement := firstn n (skipn i (hrx5_flat hrx5_B3_K0)).

Definition hrx5_K0_A : statement :=
  ltac:(let x := eval cbv beta iota delta [hrx5_k0_l hrx5_seql firstn skipn hrx5_flat hrx5_B3_K0] in
        (hrx5_seql (hrx5_k0_l 0 6)) in exact x).
Definition hrx5_K0_I : statement :=
  ltac:(let x := eval cbv beta iota delta [hrx5_k0_l hrx5_seql firstn skipn hrx5_flat hrx5_B3_K0] in
        (hrx5_seql (hrx5_k0_l 6 1)) in exact x).
Definition hrx5_K0_T : statement :=
  ltac:(let x := eval cbv beta iota delta [hrx5_k0_l hrx5_seql firstn skipn hrx5_flat hrx5_B3_K0] in
        (hrx5_seql (hrx5_k0_l 7 1)) in exact x).
Definition hrx5_K0_C : statement :=
  ltac:(let x := eval cbv beta iota delta [hrx5_k0_l hrx5_seql firstn skipn hrx5_flat hrx5_B3_K0] in
        (hrx5_seql (hrx5_k0_l 8 1)) in exact x).
Definition hrx5_K0_Z : statement :=
  ltac:(let x := eval cbv beta iota delta [hrx5_k0_l hrx5_seql firstn skipn hrx5_flat hrx5_B3_K0] in
        (hrx5_seql (hrx5_k0_l 9 4)) in exact x).

(* KI = (conditions); if (t'39) KI1 else ((conditions 2); if (t'36) KI2) *)
Definition hrx5_K0_Ic1 : statement :=
  ltac:(let x := eval unfold hrx5_K0_I in hrx5_K0_I in
        match x with Ssequence ?a (Sifthenelse _ _ _) => exact a end).
Definition hrx5_K0_I1 : statement :=
  ltac:(let x := eval unfold hrx5_K0_I in hrx5_K0_I in
        match x with Ssequence _ (Sifthenelse _ ?a _) => exact a end).
Definition hrx5_K0_Ic2 : statement :=
  ltac:(let x := eval unfold hrx5_K0_I in hrx5_K0_I in
        match x with Ssequence _ (Sifthenelse _ _ (Ssequence ?a (Sifthenelse _ _ _))) => exact a end).
Definition hrx5_K0_I2 : statement :=
  ltac:(let x := eval unfold hrx5_K0_I in hrx5_K0_I in
        match x with Ssequence _ (Sifthenelse _ _ (Ssequence _ (Sifthenelse _ ?a _))) => exact a end).

Lemma hrx5_K0_I_eq :
  hrx5_K0_I = Ssequence hrx5_K0_Ic1
                (Sifthenelse (Etempvar HRM._t'39 tint) hrx5_K0_I1
                   (Ssequence hrx5_K0_Ic2 (Sifthenelse (Etempvar HRM._t'36 tint) hrx5_K0_I2 Sskip))).
Proof. reflexivity. Qed.

(* the branch as the five segments *)
Lemma hrx5_K0_eq {Espec: OracleKind} {cs: compspecs} Delta P R :
  semax Delta P (Ssequence hrx5_K0_A (Ssequence hrx5_K0_I (Ssequence hrx5_K0_T
                   (Ssequence hrx5_K0_C hrx5_K0_Z)))) R ->
  semax Delta P hrx5_B3_K0 R.
Proof.
  intros H. refine (semax_unfold_Ssequence _ _ _ P R Delta H). reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* the state between the segments                                          *)
(* ---------------------------------------------------------------------- *)

Section States.
Variable x25519: list byte -> list byte -> list byte.

(* the packet buffer buf = dp (malloc'd, len = |B| bytes B: never a handshake length, below 2^32), the rest as in
   hrx5_B3_P 0; c: a condition on nk and len (the guards of KI1 / KI2) *)
Definition hrx5_K0_Mc (c: val -> Z -> Prop) (gv: globals) (L: hrx5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hrx5_run, EX sec: list byte, EX birth: int64, EX S: shim, EX w: list int64, EX NS: list hnode4,
  EX PS: list (val * share * peer), EX T: tstate, EX head: val, EX nk: val, EX KE: list kent4, EX st: Z,
  EX i: Z, EX kc: int64, EX lul: int64, EX q: int, EX proto: Z, EX ip4: list byte, EX ip6: list byte,
  EX port: list byte, EX B: list byte, EX dp: val,
  PROPx [hrx5_base_ok R sec birth S; hrx5_inv x25519 R L NS PS KE T head nk; 0 <= st <= Int64.max_unsigned;
         0 <= i < st; obj_ok (OBuf B); malloc_compatible (Zlength B) dp; c nk (Zlength B)]
  (LOCALx (hrx5_ltemps nk KE st i S lul ++
           [temp HM._mi nullval; temp HM._mr nullval; temp HM._mc nullval; temp HM._buf dp;
            temp HM._len (Vlong (Int64.repr (Zlength B))); temp HM._kind (Vint (Int.repr 0));
            temp HM._acc_init (Vint Int.zero); temp HM._acc_resp (Vint Int.zero); temp HM._target nullval] ++
           hrx5_lvars gv L)
  (SEPx (hrx5_wcore x25519 R L sec birth T head PS ++
         hrx5_rest x25519 R L NS KE ++ hrx5_globs gv S w kc FR ++
         [lul_rep gv lul; @data_at_ HRX Ews t_rxlog (gv HM._wg_shim_rx); qlen_rep gv q;
          hrx5_skb_part L proto ip4 ip6 port; obj_rep dp (OBuf B)] ++ hrx5_scr L))).

Definition hrx5_K0_M := hrx5_K0_Mc (fun _ _ => True).
Definition hrx5_K0_M1 := hrx5_K0_Mc (fun nk n => nk <> nullval /\ 148 < n).
Definition hrx5_K0_M2 := hrx5_K0_Mc (fun nk n => nk <> nullval /\ 92 < n).

End States.
