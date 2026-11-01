(* law handshake_receive: main's phase B8 =
   body statement 41, the four cases of CHECKs, cut by branch.

   hrx5_B8 = C1 ; if (t'233) BI else (C2 ; if (t'231) BR else (C3 ; if (t'229) BC else BE))
   with C1 / C2 / C3 the evaluations of `path == 1 && kind == k && acc` (acc = acc_init, acc_resp, target != NULL).
   hrx5_B8_Q = hrx5_S6 with every variable fixed (the 28 existentials, in the order of hrx5_S6). *)
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
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* the statements                                                          *)
(* ---------------------------------------------------------------------- *)

Definition hrx5_B8_C1 := ltac:(let x := eval cbv delta [hrx5_B8] in hrx5_B8 in
  match x with Ssequence ?c _ => exact c end).
Definition hrx5_B8_I := ltac:(let x := eval cbv delta [hrx5_B8] in hrx5_B8 in
  match x with Ssequence _ (Sifthenelse _ ?a _) => exact a end).
Definition hrx5_B8_C2 := ltac:(let x := eval cbv delta [hrx5_B8] in hrx5_B8 in
  match x with Ssequence _ (Sifthenelse _ _ (Ssequence ?c _)) => exact c end).
Definition hrx5_B8_R := ltac:(let x := eval cbv delta [hrx5_B8] in hrx5_B8 in
  match x with Ssequence _ (Sifthenelse _ _ (Ssequence _ (Sifthenelse _ ?a _))) => exact a end).
Definition hrx5_B8_C3 := ltac:(let x := eval cbv delta [hrx5_B8] in hrx5_B8 in
  match x with Ssequence _ (Sifthenelse _ _ (Ssequence _ (Sifthenelse _ _ (Ssequence ?c _)))) => exact c end).
Definition hrx5_B8_C := ltac:(let x := eval cbv delta [hrx5_B8] in hrx5_B8 in
  match x with Ssequence _ (Sifthenelse _ _ (Ssequence _ (Sifthenelse _ _ (Ssequence _ (Sifthenelse _ ?a _)))))
    => exact a end).
Definition hrx5_B8_E := ltac:(let x := eval cbv delta [hrx5_B8] in hrx5_B8 in
  match x with Ssequence _ (Sifthenelse _ _ (Ssequence _ (Sifthenelse _ _ (Ssequence _ (Sifthenelse _ _ ?a)))))
    => exact a end).

Lemma hrx5_B8_eq :
  hrx5_B8 = Ssequence hrx5_B8_C1
    (Sifthenelse (Etempvar HM._t'233 tint) hrx5_B8_I
       (Ssequence hrx5_B8_C2
          (Sifthenelse (Etempvar HM._t'231 tint) hrx5_B8_R
             (Ssequence hrx5_B8_C3 (Sifthenelse (Etempvar HM._t'229 tint) hrx5_B8_C hrx5_B8_E))))).
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* the state: hrx5_S6 with every variable fixed                            *)
(* ---------------------------------------------------------------------- *)

Section Q.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Definition hrx5_B8_Q (gv: globals) (L: hrx5_loc) (FR: mpred)
  (R: hrx5_run) (sec: list byte) (birth: int64) (S: shim) (w: list int64) (NS: list hnode4)
  (PS: list (val * share * peer)) (T: tstate) (head nk: val) (KE: list kent4) (st i: Z) (kc lul: int64) (q: int)
  (proto: Z) (ip4 ip6 port: list byte) (o: hrx5_obj) (dp img tg: val) (ai ar: Z) (d: rxdraw)
  : environ -> mpred :=
  let W0 := hrx5_W0 (hrx5_DL x25519 R L sec birth) T PS S w kc lul in
  let s := hrx5_skb dp o proto ip4 ip6 port in
  let W1 := rx_model x25519 aead_dec xaead_enc xaead_dec W0 q (l_skb L) s (obj_bytes o) d in
  PROPx [hrx5_base_ok R sec birth S; hrx5_inv x25519 R L NS PS KE T head nk; 0 <= st <= Int64.max_unsigned;
         0 <= i < st; obj_ok o; malloc_compatible (Zlength (obj_bytes o)) dp;
         hrx5_acc_ok x25519 aead_dec xaead_dec R NS PS T o (s_boot S) tg ai ar; rxdraw_ok T d]
  (LOCALx ([temp HM._nk nk; temp HM._kes (hrx5_khead KE); temp HM._steps (Vlong (Int64.repr st));
            temp HM._i (Vlong (Int64.repr i)); temp HM._now (Vlong (s_boot S));
            temp HM._m_lul (Vlong (rw_lul W1))] ++ hrx5_ptrs dp o ++
           [temp HM._img img; temp HM._len (Vlong (Int64.repr (Zlength (obj_bytes o))));
            temp HM._kind (Vint (Int.repr (obj_kind o)));
            temp HM._acc_init (Vint (Int.repr ai)); temp HM._acc_resp (Vint (Int.repr ar)); temp HM._target tg;
            temp HM._head0 (hd nullval (t_L T));
            temp HM._path (Vint (Int.repr (hrx5_path W0 q s (obj_bytes o) d)))] ++
           hrx5_lvars gv L)
  (SEPx ([rxw_rep W gv Tsh (l_wd L) head W1] ++
         hrx5_rest x25519 R L (hnodes_snapped4 T NS PS) (map (kent_snapped T) KE) ++
         hrx5_cglobs gv FR ++
         [qlen_rep gv q; skb_rep Tsh (l_skb L) s; obj_rep dp o; img_rep img (obj_bytes o)] ++
         hrx5_scr5 x25519 aead_dec xaead_dec R L T PS o (s_boot S) (devsnap_val (rw_D W1) head) S w s
           (hout Tsh 32 (l_secret L))))).

End Q.

(* the path of the packet (hrx5_path on the world before dispatch) *)
Definition hrx5_B8_path (x25519: list byte -> list byte -> list byte) (L: hrx5_loc) (R: hrx5_run)
  (sec: list byte) (birth: int64) (S: shim) (w: list int64) (PS: list (val * share * peer)) (T: tstate)
  (kc lul: int64) (q: int) (proto: Z) (ip4 ip6 port: list byte) (o: hrx5_obj) (dp: val) (d: rxdraw) : Z :=
  hrx5_path (hrx5_W0 (hrx5_DL x25519 R L sec birth) T PS S w kc lul) q (hrx5_skb dp o proto ip4 ip6 port)
    (obj_bytes o) d.

(* ---------------------------------------------------------------------- *)
(* the branch statements (children: hrx5_B8_<X>.v, `hrx5_B8_<X>_ok : hrx5_B8_<X>_stmt`)                  *)
(* ---------------------------------------------------------------------- *)

Definition hrx5_B8_branch (X: hrx5_obj -> Z -> Z -> Z -> val -> Prop) (stmt: statement) : Prop :=
  forall (Espec: OracleKind) x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR
    R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port o dp img tg ai ar d,
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  X o (hrx5_B8_path x25519 L R sec birth S w PS T kc lul q proto ip4 ip6 port o dp d) ai ar tg ->
  @semax W Espec (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec)
    (hrx5_B8_Q x25519 aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q
       proto ip4 ip6 port o dp img tg ai ar d)
    stmt (overridePost (hrx5_S8 x25519 gv L FR) (hrx5_RB x25519 gv L FR)).

(* initiation accepted: path 1, kind 1, acc_init *)
Definition hrx5_B8_isI (o: hrx5_obj) (path ai ar: Z) (tg: val) : Prop := path = 1 /\ obj_kind o = 1 /\ ai = 1.
(* response accepted: path 1, kind 2, acc_resp *)
Definition hrx5_B8_isR (o: hrx5_obj) (path ai ar: Z) (tg: val) : Prop := path = 1 /\ obj_kind o = 2 /\ ar = 1.
(* cookie reply accepted: path 1, kind 3, target not NULL *)
Definition hrx5_B8_isC (o: hrx5_obj) (path ai ar: Z) (tg: val) : Prop :=
  path = 1 /\ obj_kind o = 3 /\ tg <> nullval.
(* else: dropped, rejected, or a cookie reply sent *)
Definition hrx5_B8_isE (o: hrx5_obj) (path ai ar: Z) (tg: val) : Prop :=
  ~ hrx5_B8_isI o path ai ar tg /\ ~ hrx5_B8_isR o path ai ar tg /\ ~ hrx5_B8_isC o path ai ar tg.

Definition hrx5_B8_I_stmt : Prop := hrx5_B8_branch hrx5_B8_isI hrx5_B8_I.
Definition hrx5_B8_R_stmt : Prop := hrx5_B8_branch hrx5_B8_isR hrx5_B8_R.
Definition hrx5_B8_C_stmt : Prop := hrx5_B8_branch hrx5_B8_isC hrx5_B8_C.
Definition hrx5_B8_E_stmt : Prop := hrx5_B8_branch hrx5_B8_isE hrx5_B8_E.
