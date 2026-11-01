(* law handshake_receive, phase B3, branch kind 3: the cut of
   hrx5_B3_K3 (the cookie-reply branch, 10 top statements) into segments.
   - SA = stmts 0..3 (mc = malloc(t_cmsg); img = malloc(64); NULL -> free both, continue; len = 64):
     hrx5_B3_P 3 -> hrx5_K3_A (mc, img: data_at_)
   - SF = stmt 4 (fill_cookie_msg(mc)): hrx5_K3_A -> hrx5_K3_F (mc holds a message M, cm_ok M; img data_at_)
   - SW = stmt 5 (if (itd.head != NULL && nondet_u8() & 1) { k = nondet_size(); walk e over itd's list;
     mc->receiver_index = e->index; }): hrx5_K3_F -> hrx5_K3_F
   - SP = stmt 6 (if (peers != NULL && nondet_u8() & 1) { x = hnodes_pick(peers); h = &x->p->handshake; insert h's
     entry if not hashed; mc->receiver_index = h->entry.index; x->p->latest_cookie.have_sent_mac1 = true;
     nondet_bytes(ck, 16); xchacha20poly1305_encrypt(...) }): hrx5_K3_F -> hrx5_K3_F (the world may change: every
     world variable is existential in hrx5_K3_F, hrx5_inv / hrx5_base_ok must be re-established, hrx5_B3_lem_stmt)
   - SZ = stmts 7..9 (mc->header.type = draw_type(3); cookie_img(img, mc); skb.data = mc): hrx5_K3_F -> hrx5_B3_Q
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

Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* the statements                                                          *)
(* ---------------------------------------------------------------------- *)

Definition hrx5_k3_l (i n: nat) : list statement := firstn n (skipn i (hrx5_flat hrx5_B3_K3)).

Definition hrx5_K3_SA : statement :=
  ltac:(let x := eval cbv beta iota delta [hrx5_k3_l hrx5_seql firstn skipn hrx5_flat hrx5_B3_K3] in
        (hrx5_seql (hrx5_k3_l 0 4)) in exact x).
Definition hrx5_K3_SF : statement :=
  ltac:(let x := eval cbv beta iota delta [hrx5_k3_l hrx5_seql firstn skipn hrx5_flat hrx5_B3_K3] in
        (hrx5_seql (hrx5_k3_l 4 1)) in exact x).
Definition hrx5_K3_SW : statement :=
  ltac:(let x := eval cbv beta iota delta [hrx5_k3_l hrx5_seql firstn skipn hrx5_flat hrx5_B3_K3] in
        (hrx5_seql (hrx5_k3_l 5 1)) in exact x).
Definition hrx5_K3_SP : statement :=
  ltac:(let x := eval cbv beta iota delta [hrx5_k3_l hrx5_seql firstn skipn hrx5_flat hrx5_B3_K3] in
        (hrx5_seql (hrx5_k3_l 6 1)) in exact x).
Definition hrx5_K3_SZ : statement :=
  ltac:(let x := eval cbv beta iota delta [hrx5_k3_l hrx5_seql firstn skipn hrx5_flat hrx5_B3_K3] in
        (hrx5_seql (hrx5_k3_l 7 3)) in exact x).

(* the branch as the five segments *)
Lemma hrx5_K3_eq {Espec: OracleKind} {cs: compspecs} Delta P R :
  semax Delta P (Ssequence hrx5_K3_SA (Ssequence hrx5_K3_SF (Ssequence hrx5_K3_SW
    (Ssequence hrx5_K3_SP hrx5_K3_SZ)))) R ->
  semax Delta P hrx5_B3_K3 R.
Proof.
  intros H. refine (semax_unfold_Ssequence _ _ _ P R Delta H). reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* the states between the segments                                         *)
(* ---------------------------------------------------------------------- *)

Section States.
Variable x25519: list byte -> list byte -> list byte.

(* the struct mc and the image img (both malloc'd, 64 bytes), with a message M satisfying c, their contents X;
   the rest as in hrx5_B3_P 3 (the world existential) *)
Definition hrx5_K3_St (c: cookie_msg -> Prop) (X: val -> val -> cookie_msg -> mpred)
  (gv: globals) (L: hrx5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hrx5_run, EX sec: list byte, EX birth: int64, EX S: shim, EX w: list int64, EX NS: list hnode4,
  EX PS: list (val * share * peer), EX T: tstate, EX head: val, EX nk: val, EX KE: list kent4, EX st: Z,
  EX i: Z, EX kc: int64, EX lul: int64, EX q: int, EX proto: Z, EX ip4: list byte, EX ip6: list byte,
  EX port: list byte, EX mc: val, EX img: val, EX M: cookie_msg,
  PROPx [hrx5_base_ok R sec birth S; hrx5_inv x25519 R L NS PS KE T head nk; 0 <= st <= Int64.max_unsigned;
         0 <= i < st; malloc_compatible 64 mc; c M]
  (LOCALx (hrx5_ltemps nk KE st i S lul ++
           [temp HM._mi nullval; temp HM._mr nullval; temp HM._mc mc; temp HM._buf nullval;
            temp HM._img img; temp HM._len (Vlong (Int64.repr 64)); temp HM._kind (Vint (Int.repr 3));
            temp HM._acc_init (Vint Int.zero); temp HM._acc_resp (Vint Int.zero); temp HM._target nullval] ++
           hrx5_lvars gv L)
  (SEPx (hrx5_wcore x25519 R L sec birth T head PS ++
         hrx5_rest x25519 R L NS KE ++ hrx5_globs gv S w kc FR ++
         [lul_rep gv lul; @data_at_ HRX Ews t_rxlog (gv HM._wg_shim_rx); qlen_rep gv q;
          hrx5_skb_part L proto ip4 ip6 port; X mc img M] ++ hrx5_scr L))).

(* after SA: both allocated, any contents *)
Definition hrx5_K3_XA (mc img: val) (M: cookie_msg) : mpred :=
  @malloc_token W Ews t_cmsg mc * @data_at_ W Ews t_cmsg mc *
  @malloc_token W Ews (tarray tuchar 64) img * @data_at_ W Ews (tarray tuchar 64) img.
(* after SF, SW, SP: mc holds M, img any *)
Definition hrx5_K3_XF (mc img: val) (M: cookie_msg) : mpred :=
  @malloc_token W Ews t_cmsg mc * cmsg_rep Ews mc M *
  @malloc_token W Ews (tarray tuchar 64) img * @data_at_ W Ews (tarray tuchar 64) img.

Definition hrx5_K3_A := hrx5_K3_St (fun _ => True) hrx5_K3_XA.
Definition hrx5_K3_F := hrx5_K3_St cm_ok hrx5_K3_XF.

End States.
