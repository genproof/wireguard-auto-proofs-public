(* law handshake_receive, phase B3, branch kind 2: the cut of
   hrx5_B3_K2 (12 statements) into segments.
   - SA = stmts 0..3 (mr = malloc(92); img = malloc(92); NULL -> free both, continue; len = 92):
     hrx5_B3_P 2 -> hrx5_K2_A (mr, img: data_at_)
   - SF = stmt 4 (fill_resp(mr)): hrx5_K2_A -> hrx5_K2_F (mr = M)
   - SK = stmt 5 (if (nk != NULL && (nondet_u8() & 1)) k_response(mr, &nk->p->handshake, &itd, &id)):
     hrx5_K2_F -> hrx5_K2_F (mr = some M', the world possibly changed)
   - ST = stmts 6..7 (mr->header.type = draw_type(2); resp_img(img, mr)): hrx5_K2_F -> hrx5_K2_B (img = resp_bytes M)
   - SC = stmt 8 (draw_macs(img, len, mk1, wd.cookie_checker.secret, &skb)): hrx5_K2_B -> hrx5_K2_C (img = IMG with
     IMG's first 60 bytes those of resp_bytes M)
   - SZ = stmts 9..11 (the macs copied back into mr; skb.data = mr): hrx5_K2_C -> hrx5_B3_Q
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_conv.
#[local] Existing Instance W_handshake_receive.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B3_defs.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* the statements                                                          *)
(* ---------------------------------------------------------------------- *)

Definition hrx5_k2_l (i n: nat) : list statement := firstn n (skipn i (hrx5_flat hrx5_B3_K2)).

Definition hrx5_K2_SA : statement :=
  ltac:(let x := eval cbv beta iota delta [hrx5_k2_l hrx5_seql firstn skipn hrx5_flat hrx5_B3_K2] in
        (hrx5_seql (hrx5_k2_l 0 4)) in exact x).
Definition hrx5_K2_SF : statement :=
  ltac:(let x := eval cbv beta iota delta [hrx5_k2_l hrx5_seql firstn skipn hrx5_flat hrx5_B3_K2] in
        (hrx5_seql (hrx5_k2_l 4 1)) in exact x).
Definition hrx5_K2_SK : statement :=
  ltac:(let x := eval cbv beta iota delta [hrx5_k2_l hrx5_seql firstn skipn hrx5_flat hrx5_B3_K2] in
        (hrx5_seql (hrx5_k2_l 5 1)) in exact x).
Definition hrx5_K2_ST : statement :=
  ltac:(let x := eval cbv beta iota delta [hrx5_k2_l hrx5_seql firstn skipn hrx5_flat hrx5_B3_K2] in
        (hrx5_seql (hrx5_k2_l 6 2)) in exact x).
Definition hrx5_K2_SC : statement :=
  ltac:(let x := eval cbv beta iota delta [hrx5_k2_l hrx5_seql firstn skipn hrx5_flat hrx5_B3_K2] in
        (hrx5_seql (hrx5_k2_l 8 1)) in exact x).
Definition hrx5_K2_SZ : statement :=
  ltac:(let x := eval cbv beta iota delta [hrx5_k2_l hrx5_seql firstn skipn hrx5_flat hrx5_B3_K2] in
        (hrx5_seql (hrx5_k2_l 9 3)) in exact x).

(* the branch as the six segments *)
Lemma hrx5_K2_eq {Espec: OracleKind} {cs: compspecs} Delta P R :
  semax Delta P (Ssequence hrx5_K2_SA (Ssequence hrx5_K2_SF (Ssequence hrx5_K2_SK (Ssequence hrx5_K2_ST
    (Ssequence hrx5_K2_SC hrx5_K2_SZ))))) R ->
  semax Delta P hrx5_B3_K2 R.
Proof.
  intros H. refine (semax_unfold_Ssequence _ _ _ P R Delta H). reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* the states between the segments                                         *)
(* ---------------------------------------------------------------------- *)

Section States.
Variable x25519: list byte -> list byte -> list byte.

(* the struct mr and the image img (both malloc'd, 92 bytes), with a message M and image bytes IMG satisfying c,
   their contents X; the rest as in hrx5_B3_P 2 *)
Definition hrx5_K2_St (c: resp_msg -> list byte -> Prop) (X: val -> val -> resp_msg -> list byte -> mpred)
  (gv: globals) (L: hrx5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hrx5_run, EX sec: list byte, EX birth: int64, EX S: shim, EX w: list int64, EX NS: list hnode4,
  EX PS: list (val * share * peer), EX T: tstate, EX head: val, EX nk: val, EX KE: list kent4, EX st: Z,
  EX i: Z, EX kc: int64, EX lul: int64, EX q: int, EX proto: Z, EX ip4: list byte, EX ip6: list byte,
  EX port: list byte, EX mr: val, EX img: val, EX M: resp_msg, EX IMG: list byte,
  PROPx [hrx5_base_ok R sec birth S; hrx5_inv x25519 R L NS PS KE T head nk; 0 <= st <= Int64.max_unsigned;
         0 <= i < st; malloc_compatible 92 mr; c M IMG]
  (LOCALx (hrx5_ltemps nk KE st i S lul ++
           [temp HM._mi nullval; temp HM._mr mr; temp HM._mc nullval; temp HM._buf nullval;
            temp HM._img img; temp HM._len (Vlong (Int64.repr 92)); temp HM._kind (Vint (Int.repr 2));
            temp HM._acc_init (Vint Int.zero); temp HM._acc_resp (Vint Int.zero); temp HM._target nullval] ++
           hrx5_lvars gv L)
  (SEPx (hrx5_wcore x25519 R L sec birth T head PS ++
         hrx5_rest x25519 R L NS KE ++ hrx5_globs gv S w kc FR ++
         [lul_rep gv lul; @data_at_ HRX Ews t_rxlog (gv HM._wg_shim_rx); qlen_rep gv q;
          hrx5_skb_part L proto ip4 ip6 port; X mr img M IMG] ++ hrx5_scr L))).

(* after SA: both allocated, any contents *)
Definition hrx5_K2_XA (mr img: val) (M: resp_msg) (IMG: list byte) : mpred :=
  @malloc_token W Ews t_resp mr * @data_at_ W Ews t_resp mr *
  @malloc_token W Ews (tarray tuchar 92) img * @data_at_ W Ews (tarray tuchar 92) img.
(* after SF and SK: mr holds M, img any *)
Definition hrx5_K2_XF (mr img: val) (M: resp_msg) (IMG: list byte) : mpred :=
  @malloc_token W Ews t_resp mr * resp_rep Ews mr M *
  @malloc_token W Ews (tarray tuchar 92) img * @data_at_ W Ews (tarray tuchar 92) img.
(* after ST and SC: mr holds M, img holds IMG *)
Definition hrx5_K2_XM (mr img: val) (M: resp_msg) (IMG: list byte) : mpred :=
  @malloc_token W Ews t_resp mr * resp_rep Ews mr M *
  @malloc_token W Ews (tarray tuchar 92) img * hbytes Ews IMG img.

Definition hrx5_K2_A := hrx5_K2_St (fun _ _ => True) hrx5_K2_XA.
Definition hrx5_K2_F := hrx5_K2_St (fun M _ => rm_ok M) hrx5_K2_XF.
Definition hrx5_K2_B := hrx5_K2_St (fun M IMG => rm_ok M /\ IMG = resp_bytes M) hrx5_K2_XM.
Definition hrx5_K2_C :=
  hrx5_K2_St (fun M IMG => rm_ok M /\ Zlength IMG = 92 /\ sublist 0 60 IMG = sublist 0 60 (resp_bytes M))
    hrx5_K2_XM.

End States.
