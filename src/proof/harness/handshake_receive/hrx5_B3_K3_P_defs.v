(* law handshake_receive, phase B3, branch kind 3, segment P: the cut of hrx5_K3_SP into the guard (mine), P1 and P2, and the states between them.
   - hrx5_K3_SP = Ssequence hrx5_K3P_G (Sifthenelse hrx5_K3P_c hrx5_K3P_body Sskip)   (hrx5_K3P_SP_eq)
     G = `t'369 = peers; if (t'369 != NULL) { t'69 = nondet_u8(); t'68 = (bool)(t'69 & 1) } else t'68 = 0`
   - body = P1 ; P2  (hrx5_K3P_body_split)
     P1 = `t'368 = peers; t'67 = hnodes_pick(t'368); x = t'67; t'367 = x->p; h = &t'367->handshake;
           t'366 = h->entry.hashed; if (!t'366) wg_index_hashtable_insert(&itd, &h->entry);
           t'365 = h->entry.index; mc->receiver_index = t'365`
     P2 = `t'364 = x->p; t'364->latest_cookie.have_sent_mac1 = 1; nondet_bytes(ck, 16); t'362 = x->p;
           t'363 = x->p; xchacha20poly1305_encrypt(mc->encrypted_cookie, ck, 16, t'362->latest_cookie.last_mac1_sent,
           16, mc->nonce, t'363->latest_cookie.cookie_decryption_key)`
   - hrx5_K3P_st ... pl tl = the body of hrx5_K3_St (hrx5_B3_K3_defs.v) for FIXED values, PROPs pl, extra temps tl in
     front; hrx5_K3_F = EX .., hrx5_K3P_st .. (hrx5_K3P_props ..) [] (hrx5_K3P_F_eq).
   - P1 (hrx5_K3P_1_stmt): from st (props) [] (any world with NS <> []) to EX S1 T1 idx j P,
     st S1 T1 (M with receiver idx) (props ++ [j in range; sfind PS (hn_p (Znth j NS)) = Some (Ews, P)])
     [temp x (hn_addr (Znth j NS)); temp h (hs_addr (hn_p (Znth j NS)))]
   - P2 (hrx5_K3P_2_stmt): from that state to hrx5_K3_F (ret hrx5_RB). *)
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B3_K3_defs.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* the statements                                                          *)
(* ---------------------------------------------------------------------- *)

Definition hrx5_K3P_G : statement :=
  ltac:(let x := eval cbv delta [hrx5_K3_SP] in hrx5_K3_SP in
        match x with Ssequence ?g _ => exact g end).
Definition hrx5_K3P_c : expr :=
  ltac:(let x := eval cbv delta [hrx5_K3_SP] in hrx5_K3_SP in
        match x with Ssequence _ (Sifthenelse ?c _ _) => exact c end).
Definition hrx5_K3P_body : statement :=
  ltac:(let x := eval cbv delta [hrx5_K3_SP] in hrx5_K3_SP in
        match x with Ssequence _ (Sifthenelse _ ?b _) => exact b end).
Definition hrx5_K3P_S1 : statement :=
  ltac:(let x := eval cbv delta [hrx5_K3P_body] in hrx5_K3P_body in
        match x with Ssequence ?a (Ssequence ?b (Ssequence ?c (Ssequence ?d _))) =>
          exact (Ssequence a (Ssequence b (Ssequence c d))) end).
Definition hrx5_K3P_S2 : statement :=
  ltac:(let x := eval cbv delta [hrx5_K3P_body] in hrx5_K3P_body in
        match x with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ ?r))) => exact r end).

Lemma hrx5_K3P_SP_eq : hrx5_K3_SP = Ssequence hrx5_K3P_G (Sifthenelse hrx5_K3P_c hrx5_K3P_body Sskip).
Proof. reflexivity. Qed.

Lemma hrx5_K3P_body_split {Espec: OracleKind} {cs: compspecs} Delta P R :
  semax Delta P (Ssequence hrx5_K3P_S1 hrx5_K3P_S2) R -> semax Delta P hrx5_K3P_body R.
Proof.
  intros H. refine (semax_unfold_Ssequence _ _ _ P R Delta H). reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* the states                                                              *)
(* ---------------------------------------------------------------------- *)

Section States.
Variable x25519: list byte -> list byte -> list byte.

(* the PROPs of hrx5_K3_F *)
Definition hrx5_K3P_props (R: hrx5_run) (L: hrx5_loc) (sec: list byte) (birth: int64) (S: shim)
  (NS: list hnode4) (PS: list (val * share * peer)) (KE: list kent4) (T: tstate) (head nk: val) (st i: Z)
  (mc: val) (M: cookie_msg) : list Prop :=
  [hrx5_base_ok R sec birth S; hrx5_inv x25519 R L NS PS KE T head nk; 0 <= st <= Int64.max_unsigned;
   0 <= i < st; malloc_compatible 64 mc; cm_ok M].

(* the body of hrx5_K3_St for fixed values (X = hrx5_K3_XF), PROPs pl, extra temps tl in front *)
Definition hrx5_K3P_st (gv: globals) (L: hrx5_loc) (FR: mpred) (R: hrx5_run) (sec: list byte) (birth: int64)
  (S: shim) (w: list int64) (NS: list hnode4) (PS: list (val * share * peer)) (T: tstate) (head nk: val)
  (KE: list kent4) (st i: Z) (kc lul: int64) (q: int) (proto: Z) (ip4 ip6 port: list byte) (mc img: val)
  (M: cookie_msg) (pl: list Prop) (tl: list localdef) : environ -> mpred :=
  PROPx pl
  (LOCALx (tl ++ hrx5_ltemps nk KE st i S lul ++
           [temp HM._mi nullval; temp HM._mr nullval; temp HM._mc mc; temp HM._buf nullval;
            temp HM._img img; temp HM._len (Vlong (Int64.repr 64)); temp HM._kind (Vint (Int.repr 3));
            temp HM._acc_init (Vint Int.zero); temp HM._acc_resp (Vint Int.zero); temp HM._target nullval] ++
           hrx5_lvars gv L)
  (SEPx (hrx5_wcore x25519 R L sec birth T head PS ++
         hrx5_rest x25519 R L NS KE ++ hrx5_globs gv S w kc FR ++
         [lul_rep gv lul; @data_at_ HRX Ews t_rxlog (gv HM._wg_shim_rx); qlen_rep gv q;
          hrx5_skb_part L proto ip4 ip6 port; hrx5_K3_XF mc img M] ++ hrx5_scr L))).

Lemma hrx5_K3P_F_eq gv L FR :
  hrx5_K3_F x25519 gv L FR =
  EX R: hrx5_run, EX sec: list byte, EX birth: int64, EX S: shim, EX w: list int64, EX NS: list hnode4,
  EX PS: list (val * share * peer), EX T: tstate, EX head: val, EX nk: val, EX KE: list kent4, EX st: Z,
  EX i: Z, EX kc: int64, EX lul: int64, EX q: int, EX proto: Z, EX ip4: list byte, EX ip6: list byte,
  EX port: list byte, EX mc: val, EX img: val, EX M: cookie_msg,
  hrx5_K3P_st gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port mc img M
    (hrx5_K3P_props R L sec birth S NS PS KE T head nk st i mc M) [].
Proof. reflexivity. Qed.

End States.

(* the message with the receiver index idx *)
Definition hrx5_K3P_rcv (M: cookie_msg) (idx: int) : cookie_msg :=
  mkCM (cm_type M) idx (cm_nonce M) (cm_enc M).

(* the peer after `have_sent_mac1 = true` *)
Definition hrx5_K3P_peer (P: peer) : peer :=
  p_set_cookie P (mkCookie (ck_birth (p_cookie P)) (ck_valid (p_cookie P)) (ck_cookie (p_cookie P)) true
                    (ck_last_mac1 (p_cookie P)) (ck_dkey (p_cookie P)) (ck_mkey (p_cookie P))).

(* ---------------------------------------------------------------------- *)
(* the segment statements                                                  *)
(* ---------------------------------------------------------------------- *)

Section Segs.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

(* the state after P1 *)
Definition hrx5_K3P_Q1 (gv: globals) (L: hrx5_loc) (FR: mpred) (R: hrx5_run) (sec: list byte) (birth: int64)
  (S1: shim) (w: list int64) (NS: list hnode4) (PS: list (val * share * peer)) (T1: tstate) (head nk: val)
  (KE: list kent4) (st i: Z) (kc lul: int64) (q: int) (proto: Z) (ip4 ip6 port: list byte) (mc img: val)
  (M1: cookie_msg) (j: Z) (P: peer) : environ -> mpred :=
  hrx5_K3P_st x25519 gv L FR R sec birth S1 w NS PS T1 head nk KE st i kc lul q proto ip4 ip6 port mc img M1
    (hrx5_K3P_props x25519 R L sec birth S1 NS PS KE T1 head nk st i mc M1 ++
     [0 <= j < Zlength NS; sfind PS (hn_p (Znth j NS)) = Some (Ews, P)])
    [temp HM._x (hn_addr (Znth j NS)); temp HM._h (hs_addr (hn_p (Znth j NS)))].

Definition hrx5_K3P_1_stmt : Prop :=
  forall {Espec: OracleKind} gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port mc img M,
  hrx5_B3_lem_stmt x25519 ->
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  NS <> [] ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec)
    (hrx5_K3P_st x25519 gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port mc img M
       (hrx5_K3P_props x25519 R L sec birth S NS PS KE T head nk st i mc M) [])
    hrx5_K3P_S1
    (normal_ret_assert
      (EX S1: shim, EX T1: tstate, EX idx: int, EX j: Z, EX P: peer,
       hrx5_K3P_Q1 gv L FR R sec birth S1 w NS PS T1 head nk KE st i kc lul q proto ip4 ip6 port mc img
         (hrx5_K3P_rcv M idx) j P)).

Definition hrx5_K3P_2_stmt : Prop :=
  forall {Espec: OracleKind} gv L FR R sec birth S1 w NS PS T1 head nk KE st i kc lul q proto ip4 ip6 port mc img
    M1 j P,
  hrx5_B3_lem_stmt x25519 ->
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec)
    (hrx5_K3P_Q1 gv L FR R sec birth S1 w NS PS T1 head nk KE st i kc lul q proto ip4 ip6 port mc img M1 j P)
    hrx5_K3P_S2
    (overridePost (hrx5_K3_F x25519 gv L FR) (hrx5_RB x25519 gv L FR)).

End Segs.
