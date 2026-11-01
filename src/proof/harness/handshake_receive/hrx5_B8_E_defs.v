(* law handshake_receive: main's phase B8,
   branch E: the cut of the branch and its intermediate state.

   hrx5_B8_E = EA ; EB
     EA = if (path == 2) { CHECK(rx_only_cookie(1)); CHECK(wg_shim_rx.cookie_index == (kind == 1 ? mi->sender_index
          : mr->sender_index)) } else CHECK(rx_only_cookie(0))                                 Q1 -> Q1  (part A)
     EB = CHECK(hnodes_same_except(peers, NULL) && itd.head == head0 && kents_same(kes) && shim_same(&ss))
                                                                                          Q1 -> S8  (part B)
   Q1 = hrx5_B8_Q with the world after the packet explicit (hrx5_B8E_W): in branch E the device has only the
   checker's rotation (secret sec1 born birth1), the shim S1 only the draws (same clock, same counters and warnings
   as S), last_under_load lul1, the log rx0 or (path 2) rx_send_cookie rx0 of the message's sender index; the peers,
   the table, the slots (none), the warnings and keypair_counter are those before the packet.  The pure lemma (part
   P, hrx5_B8E_pure_stmt) shows that rx_model gives this world in branch E. *)
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_defs.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* the statements                                                          *)
(* ---------------------------------------------------------------------- *)

Definition hrx5_B8E_A := ltac:(let x := eval cbv delta [hrx5_B8_E] in hrx5_B8_E in
  match x with Ssequence ?a _ => exact a end).
Definition hrx5_B8E_B := ltac:(let x := eval cbv delta [hrx5_B8_E] in hrx5_B8_E in
  match x with Ssequence _ ?b => exact b end).

Lemma hrx5_B8E_eq : hrx5_B8_E = Ssequence hrx5_B8E_A hrx5_B8E_B.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* the world after the packet in branch E                                  *)
(* ---------------------------------------------------------------------- *)

(* the sender index of an initiation / response (the cookie reply's receiver index) *)
Definition hrx5_B8E_sidx (o: hrx5_obj) : int :=
  match o with OInit M => im_sender M | OResp M => rm_sender M | _ => Int.zero end.

(* the log after the packet: a cookie reply sent (path 2), else nothing *)
Definition hrx5_B8E_log (path: Z) (o: hrx5_obj) : rxlog :=
  if Z.eq_dec path 2 then rx_send_cookie rx0 (hrx5_B8E_sidx o) else rx0.

(* the world: D with the secret sec1 born birth1, the peers / table before, no slot keypair, the shim S1 *)
Definition hrx5_B8E_W (x25519: list byte -> list byte -> list byte) (R: hrx5_run) (L: hrx5_loc)
  (sec1: list byte) (birth1: int64) (T: tstate) (PS: list (val * share * peer)) (S1: shim) (w: list int64)
  (kc lul1: int64) (path: Z) (o: hrx5_obj) : rxw :=
  mkRW (hrx5_DL x25519 R L sec1 birth1) T PS [] S1 w kc lul1 (hrx5_B8E_log path o).

(* the pure part P: in branch E the receive model gives such a world.  (Hnn: the node addresses are not NULL,
   from hnodes_rep4; needed for a cookie reply: target = NULL means the harness's model found no peer.) *)
Definition hrx5_B8E_pure_stmt : Prop :=
  forall x25519 aead_enc aead_dec xaead_enc xaead_dec L R sec birth S w NS PS T head nk KE kc lul q proto ip4 ip6
    port o dp tg ai ar d,
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hrx5_base_ok R sec birth S -> hrx5_inv x25519 R L NS PS KE T head nk -> obj_ok o ->
  hrx5_acc_ok x25519 aead_dec xaead_dec R NS PS T o (s_boot S) tg ai ar -> rxdraw_ok T d ->
  ~ In nullval (map hn_addr NS) ->
  let path := hrx5_B8_path x25519 L R sec birth S w PS T kc lul q proto ip4 ip6 port o dp d in
  hrx5_B8_isE o path ai ar tg ->
  exists sec1 birth1 S1 lul1,
    rx_model x25519 aead_dec xaead_enc xaead_dec (hrx5_W0 (hrx5_DL x25519 R L sec birth) T PS S w kc lul) q
      (l_skb L) (hrx5_skb dp o proto ip4 ip6 port) (obj_bytes o) d =
      hrx5_B8E_W x25519 R L sec1 birth1 T PS S1 w kc lul1 path o /\
    hrx5_base_ok R sec1 birth1 S1 /\ s_boot S1 = s_boot S /\ shim_eqb S w S1 w = true /\
    0 <= path <= 2 /\ (path = 2 -> obj_kind o = 1 \/ obj_kind o = 2).

(* ---------------------------------------------------------------------- *)
(* the state Q1 (between parts A and B)                                    *)
(* ---------------------------------------------------------------------- *)

Section Q.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

(* hrx5_B8_Q with W1 = hrx5_B8E_W .. sec1 birth1 S1 lul1 path o and its facts; path the harness's path *)
Definition hrx5_B8E_Q1 (gv: globals) (L: hrx5_loc) (FR: mpred)
  (R: hrx5_run) (sec: list byte) (birth: int64) (S: shim) (w: list int64) (NS: list hnode4)
  (PS: list (val * share * peer)) (T: tstate) (head nk: val) (KE: list kent4) (st i: Z) (kc: int64) (q: int)
  (proto: Z) (ip4 ip6 port: list byte) (o: hrx5_obj) (dp img tg: val) (ai ar: Z)
  (sec1: list byte) (birth1: int64) (S1: shim) (lul1: int64) (path: Z) : environ -> mpred :=
  let s := hrx5_skb dp o proto ip4 ip6 port in
  PROPx [hrx5_base_ok R sec birth S; hrx5_base_ok R sec1 birth1 S1; s_boot S1 = s_boot S;
         shim_eqb S w S1 w = true; 0 <= path <= 2; path = 2 -> obj_kind o = 1 \/ obj_kind o = 2;
         hrx5_inv x25519 R L NS PS KE T head nk; 0 <= st <= Int64.max_unsigned;
         0 <= i < st; obj_ok o; malloc_compatible (Zlength (obj_bytes o)) dp]
  (LOCALx ([temp HM._nk nk; temp HM._kes (hrx5_khead KE); temp HM._steps (Vlong (Int64.repr st));
            temp HM._i (Vlong (Int64.repr i)); temp HM._now (Vlong (s_boot S));
            temp HM._m_lul (Vlong lul1)] ++ hrx5_ptrs dp o ++
           [temp HM._img img; temp HM._len (Vlong (Int64.repr (Zlength (obj_bytes o))));
            temp HM._kind (Vint (Int.repr (obj_kind o)));
            temp HM._acc_init (Vint (Int.repr ai)); temp HM._acc_resp (Vint (Int.repr ar)); temp HM._target tg;
            temp HM._head0 (hd nullval (t_L T));
            temp HM._path (Vint (Int.repr path))] ++
           hrx5_lvars gv L)
  (SEPx ([rxw_rep W gv Tsh (l_wd L) head (hrx5_B8E_W x25519 R L sec1 birth1 T PS S1 w kc lul1 path o)] ++
         hrx5_rest x25519 R L (hnodes_snapped4 T NS PS) (map (kent_snapped T) KE) ++
         hrx5_cglobs gv FR ++
         [qlen_rep gv q; skb_rep Tsh (l_skb L) s; obj_rep dp o; img_rep img (obj_bytes o)] ++
         hrx5_scr5 x25519 aead_dec xaead_dec R L T PS o (s_boot S)
           (devsnap_val (hrx5_DL x25519 R L sec1 birth1) head) S w s (hout Tsh 32 (l_secret L))))).

End Q.

(* the parts (children: hrx5_B8_E_<X>.v, `hrx5_B8E_<X>_ok : hrx5_B8E_<X>_stmt`) *)
Definition hrx5_B8E_part (post: forall (x25519: list byte -> list byte -> list byte)
    (aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte))
    (xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte)),
    globals -> hrx5_loc -> mpred -> hrx5_run -> list byte -> int64 -> shim -> list int64 -> list hnode4 ->
    list (val * share * peer) -> tstate -> val -> val -> list kent4 -> Z -> Z -> int64 -> int -> Z -> list byte ->
    list byte -> list byte -> hrx5_obj -> val -> val -> val -> Z -> Z -> list byte -> int64 -> shim -> int64 -> Z ->
    environ -> mpred) (stmt: statement) : Prop :=
  forall (Espec: OracleKind) x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR
    R sec birth S w NS PS T head nk KE st i kc q proto ip4 ip6 port o dp img tg ai ar sec1 birth1 S1 lul1 path,
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  @semax W Espec (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec)
    (hrx5_B8E_Q1 x25519 aead_dec xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc q proto ip4 ip6 port
       o dp img tg ai ar sec1 birth1 S1 lul1 path)
    stmt
    (overridePost (post x25519 aead_dec xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc q proto ip4 ip6
       port o dp img tg ai ar sec1 birth1 S1 lul1 path) (hrx5_RB x25519 gv L FR)).

(* part A: the log checks, back to Q1 *)
Definition hrx5_B8E_A_stmt : Prop := hrx5_B8E_part hrx5_B8E_Q1 hrx5_B8E_A.

(* part B: the whole-state check, to the loop's state hrx5_S8 (a new world: sec1 birth1 S1 w, the snapped nodes
   hnodes_snapped4 T NS PS and kents map (kent_snapped T) KE, lul1) *)
Definition hrx5_B8E_B_stmt : Prop :=
  hrx5_B8E_part (fun x25519 aead_dec xaead_dec gv L FR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
                   hrx5_S8 x25519 gv L FR) hrx5_B8E_B.
