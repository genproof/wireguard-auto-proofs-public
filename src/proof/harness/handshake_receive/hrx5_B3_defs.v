(* law handshake_receive, phase B3: the cut of B3 = body statements 18..20
   (kind = nondet_u8() % 4; the if-chain over the four kinds; skb.len = len) into the four branches of the if-chain.

   - hrx5_B3_Q   : S3 but skb.len not yet set (skb.data = the object's pointer dp, the len field any);
   - hrx5_B3_K k : the branch statement of kind k (from hrx5_B3 itself);
   - hrx5_B3_lem_stmt : pure lemmas of the invariant hrx5_inv; the branch
     lemmas take it as a HYPOTHESIS (so that each is proved on its own). *)
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

(* B3 = Ssequence (kind = nondet_u8() % 4) (Ssequence IF skb.len = len),
   IF = if (kind == 0) K0 else if (kind == 1) K1 else if (kind == 2) K2 else K3 *)
Definition hrx5_B3_draw : statement :=
  ltac:(let x := eval unfold hrx5_B3 in hrx5_B3 in
        match x with Ssequence ?a _ => exact a end).
Definition hrx5_B3_if : statement :=
  ltac:(let x := eval unfold hrx5_B3 in hrx5_B3 in
        match x with Ssequence _ (Ssequence ?a _) => exact a end).
Definition hrx5_B3_len : statement :=
  ltac:(let x := eval unfold hrx5_B3 in hrx5_B3 in
        match x with Ssequence _ (Ssequence _ ?a) => exact a end).
Definition hrx5_B3_K0 : statement :=
  ltac:(let x := eval unfold hrx5_B3_if in hrx5_B3_if in
        match x with Sifthenelse _ ?a _ => exact a end).
Definition hrx5_B3_K1 : statement :=
  ltac:(let x := eval unfold hrx5_B3_if in hrx5_B3_if in
        match x with Sifthenelse _ _ (Sifthenelse _ ?a _) => exact a end).
Definition hrx5_B3_K2 : statement :=
  ltac:(let x := eval unfold hrx5_B3_if in hrx5_B3_if in
        match x with Sifthenelse _ _ (Sifthenelse _ _ (Sifthenelse _ ?a _)) => exact a end).
Definition hrx5_B3_K3 : statement :=
  ltac:(let x := eval unfold hrx5_B3_if in hrx5_B3_if in
        match x with Sifthenelse _ _ (Sifthenelse _ _ (Sifthenelse _ _ ?a)) => exact a end).

Definition hrx5_B3_kind_test (k: Z) : expr :=
  Ebinop Oeq (Etempvar HM._kind tint) (Econst_int (Int.repr k) tint) tint.

Lemma hrx5_B3_eq : hrx5_B3 = Ssequence hrx5_B3_draw (Ssequence hrx5_B3_if hrx5_B3_len).
Proof. reflexivity. Qed.

Lemma hrx5_B3_if_eq :
  hrx5_B3_if = Sifthenelse (hrx5_B3_kind_test 0) hrx5_B3_K0
                 (Sifthenelse (hrx5_B3_kind_test 1) hrx5_B3_K1
                   (Sifthenelse (hrx5_B3_kind_test 2) hrx5_B3_K2 hrx5_B3_K3)).
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* the states                                                              *)
(* ---------------------------------------------------------------------- *)

(* the skb with its data set to dp, the len field any (skb.len is set after the if-chain) *)
Definition hrx5_B3_skbd (L: hrx5_loc) (dp: val) (proto: Z) (ip4 ip6 port: list byte) : mpred :=
  !! (0 <= proto <= 65535 /\ Zlength ip4 = 4 /\ Zlength ip6 = 16 /\ Zlength port = 2) &&
  EX lv: val,
    @data_at Cookie.CS Tsh t_skb (dp, (lv, (Vint (Int.repr proto), (bytes ip4, (bytes ip6, bytes port))))) (l_skb L).

Section States.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

(* the pre of branch k: hrx5_S2 with kind = k *)
Definition hrx5_B3_P (k: Z) (gv: globals) (L: hrx5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hrx5_run, EX sec: list byte, EX birth: int64, EX S: shim, EX w: list int64, EX NS: list hnode4,
  EX PS: list (val * share * peer), EX T: tstate, EX head: val, EX nk: val, EX KE: list kent4, EX st: Z,
  EX i: Z, EX kc: int64, EX lul: int64, EX q: int, EX proto: Z, EX ip4: list byte, EX ip6: list byte,
  EX port: list byte,
  PROPx [hrx5_base_ok R sec birth S; hrx5_inv x25519 R L NS PS KE T head nk; 0 <= st <= Int64.max_unsigned;
         0 <= i < st]
  (LOCALx (hrx5_ltemps nk KE st i S lul ++
           [temp HM._mi nullval; temp HM._mr nullval; temp HM._mc nullval; temp HM._buf nullval;
            temp HM._kind (Vint (Int.repr k));
            temp HM._acc_init (Vint Int.zero); temp HM._acc_resp (Vint Int.zero); temp HM._target nullval] ++
           hrx5_lvars gv L)
  (SEPx (hrx5_wcore x25519 R L sec birth T head PS ++
         hrx5_rest x25519 R L NS KE ++ hrx5_globs gv S w kc FR ++
         [lul_rep gv lul; @data_at_ HRX Ews t_rxlog (gv HM._wg_shim_rx); qlen_rep gv q;
          hrx5_skb_part L proto ip4 ip6 port] ++ hrx5_scr L))).

(* the post of every branch: hrx5_S3 but skb.len not set yet *)
Definition hrx5_B3_Q (gv: globals) (L: hrx5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hrx5_run, EX sec: list byte, EX birth: int64, EX S: shim, EX w: list int64, EX NS: list hnode4,
  EX PS: list (val * share * peer), EX T: tstate, EX head: val, EX nk: val, EX KE: list kent4, EX st: Z,
  EX i: Z, EX kc: int64, EX lul: int64, EX q: int, EX proto: Z, EX ip4: list byte, EX ip6: list byte,
  EX port: list byte, EX o: hrx5_obj, EX dp: val, EX img: val,
  PROPx [hrx5_base_ok R sec birth S; hrx5_inv x25519 R L NS PS KE T head nk; 0 <= st <= Int64.max_unsigned;
         0 <= i < st; obj_ok o; malloc_compatible (Zlength (obj_bytes o)) dp]
  (LOCALx (hrx5_ltemps nk KE st i S lul ++ hrx5_ptrs dp o ++
           [temp HM._img img; temp HM._len (Vlong (Int64.repr (Zlength (obj_bytes o))));
            temp HM._kind (Vint (Int.repr (obj_kind o)));
            temp HM._acc_init (Vint Int.zero); temp HM._acc_resp (Vint Int.zero); temp HM._target nullval] ++
           hrx5_lvars gv L)
  (SEPx (hrx5_wcore x25519 R L sec birth T head PS ++
         hrx5_rest x25519 R L NS KE ++ hrx5_globs gv S w kc FR ++
         [lul_rep gv lul; @data_at_ HRX Ews t_rxlog (gv HM._wg_shim_rx); qlen_rep gv q;
          hrx5_B3_skbd L dp proto ip4 ip6 port; obj_rep dp o; img_rep img (obj_bytes o)] ++
         hrx5_scr L))).

End States.

(* ---------------------------------------------------------------------- *)
(* the pure lemmas of the invariant (proved in hrx5_B3_lem.v)              *)
(* ---------------------------------------------------------------------- *)

Definition hrx5_B3_lem_stmt (x25519: list byte -> list byte -> list byte) : Prop :=
  (* a peer of PS updated, its invariant fields kept (pok, the public-key chain link) *)
  (forall R L NS PS KE T head nk p sh P P',
     hrx5_inv x25519 R L NS PS KE T head nk -> sfind PS p = Some (sh, P) ->
     hrx5_pok x25519 R L (p, sh, P') -> p_pknext P' = p_pknext P ->
     hrx5_inv x25519 R L NS (supd PS p P') KE T head nk) /\
  (* a peer's handshake entry (re)inserted into the table *)
  (forall R L NS PS KE T head nk p sh P idx,
     hrx5_inv x25519 R L NS PS KE T head nk -> sfind PS p = Some (sh, P) ->
     hrx5_inv x25519 R L NS PS KE (t_insert T (hs_addr p) idx) head nk) /\
  (* a node of NS: its peer is in PS (share Ews), its handshake entry in the table's pool *)
  (forall R L NS PS KE T head nk N,
     hrx5_inv x25519 R L NS PS KE T head nk -> In N NS ->
     exists P, sfind PS (hn_p N) = Some (Ews, P) /\ hrx5_pok x25519 R L (hn_p N, Ews, P) /\
               In (hs_addr (hn_p N)) (saddrs (t_D T))) /\
  (* nk is NULL or a node of NS *)
  (forall R L NS PS KE T head nk,
     hrx5_inv x25519 R L NS PS KE T head nk -> nk <> nullval -> exists N, In N NS /\ hn_addr N = nk) /\
  (* the shim's index draw keeps the base facts *)
  (forall R sec birth S idx, hrx5_base_ok R sec birth S -> hrx5_base_ok R sec birth (shim_u32 S idx)) /\
  (* the real clock's draw keeps the base facts *)
  (forall R sec birth S sec' ns, hrx5_base_ok R sec birth S ->
     hrx5_base_ok R sec birth (shim_set_real S sec' ns)).
