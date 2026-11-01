(* law handshake_receive, main's phase B4: the cut of B4 = body statements 21..25.
     A  = 21..24  tw = len >= 4 ? le32_load(img) : 0; fwd = ...; hnodes_snap(peers); kents_snap(kes)
                  hrx5_S3 -> hrx5_B4_S3b
     M  = 25      the harness's model block (one if / else if / else if): hrx5_B4_S3b -> hrx5_S4, proved per kind of
                  the packet object o: OInit (segment I), OResp (segment R), OCookie (segment C), OBuf (segment Z)
   The pre-state of M with every variable fixed is hrx5_B4_Q (the post hrx5_S4 is existential). *)
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
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

(* the statements *)
Definition hrx5_B4_A := ltac:(let x := eval cbv beta iota delta [hrx5_bl hrx5_seql firstn skipn hrx5_bstmts] in
  (hrx5_seql (hrx5_bl 21 4)) in exact x).
Definition hrx5_B4_M := ltac:(let x := eval cbv beta iota delta [hrx5_bl hrx5_seql firstn skipn hrx5_bstmts] in
  (hrx5_seql (hrx5_bl 25 1)) in exact x).

Lemma hrx5_B4_split : hrx5_bl 21 5 = hrx5_bl 21 4 ++ hrx5_bl 25 1.
Proof. reflexivity. Qed.

Lemma hrx5_B4_A_eq : hrx5_B4_A = hrx5_seql (hrx5_bl 21 4).
Proof. reflexivity. Qed.
Lemma hrx5_B4_M_eq : hrx5_B4_M = hrx5_seql (hrx5_bl 25 1).
Proof. reflexivity. Qed.

Section B4defs.
Variable x25519: list byte -> list byte -> list byte.

(* after A, every variable fixed: S3 with tw, fwd, the nodes and the kents snapped (on T, PS) *)
Definition hrx5_B4_Q (gv: globals) (L: hrx5_loc) (FR: mpred) (R: hrx5_run) (sec: list byte) (birth: int64)
  (S: shim) (w: list int64) (NS: list hnode4) (PS: list (val * share * peer)) (T: tstate) (head nk: val)
  (KE: list kent4) (st i: Z) (kc lul: int64) (q: int) (proto: Z) (ip4 ip6 port: list byte) (o: hrx5_obj)
  (dp img: val) : environ -> mpred :=
  PROPx [hrx5_base_ok R sec birth S; hrx5_inv x25519 R L NS PS KE T head nk; 0 <= st <= Int64.max_unsigned;
         0 <= i < st; obj_ok o; malloc_compatible (Zlength (obj_bytes o)) dp]
  (LOCALx (hrx5_ltemps nk KE st i S lul ++ hrx5_ptrs dp o ++
           [temp HM._img img; temp HM._len (Vlong (Int64.repr (Zlength (obj_bytes o))));
            temp HM._kind (Vint (Int.repr (obj_kind o)));
            temp HM._tw (Vint (if Z.leb 4 (Zlength (obj_bytes o)) then hrx5_tw (obj_bytes o) else Int.zero));
            temp HM._fwd (Vint (if hrx5_fwd (obj_bytes o) then Int.one else Int.zero));
            temp HM._acc_init (Vint Int.zero); temp HM._acc_resp (Vint Int.zero); temp HM._target nullval] ++
           hrx5_lvars gv L)
  (SEPx (hrx5_wcore x25519 R L sec birth T head PS ++
         hrx5_rest x25519 R L (hnodes_snapped4 T NS PS) (map (kent_snapped T) KE) ++
         hrx5_globs gv S w kc FR ++
         [lul_rep gv lul; @data_at_ HRX Ews t_rxlog (gv HM._wg_shim_rx); qlen_rep gv q;
          skb_rep Tsh (l_skb L) (hrx5_skb dp o proto ip4 ip6 port); obj_rep dp o; img_rep img (obj_bytes o)] ++
         hrx5_scr L))).

Definition hrx5_B4_S3b (gv: globals) (L: hrx5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hrx5_run, EX sec: list byte, EX birth: int64, EX S: shim, EX w: list int64, EX NS: list hnode4,
  EX PS: list (val * share * peer), EX T: tstate, EX head: val, EX nk: val, EX KE: list kent4, EX st: Z,
  EX i: Z, EX kc: int64, EX lul: int64, EX q: int, EX proto: Z, EX ip4: list byte, EX ip6: list byte,
  EX port: list byte, EX o: hrx5_obj, EX dp: val, EX img: val,
  hrx5_B4_Q gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port o dp img.

End B4defs.

(* the segments' statements (the children's targets) *)
Definition hrx5_B4_A_stmt : Prop :=
  forall {Espec: OracleKind} x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR,
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_S3 x25519 gv L FR) hrx5_B4_A
    (overridePost (hrx5_B4_S3b x25519 gv L FR) (hrx5_RB x25519 gv L FR)).

(* the model block for a packet object of kind k (sel o: o is of that kind) *)
Definition hrx5_B4_M_stmt (sel: hrx5_obj -> Prop) : Prop :=
  forall {Espec: OracleKind} x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR
    R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port o dp img,
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec -> sel o ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec)
    (hrx5_B4_Q x25519 gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port o dp img)
    hrx5_B4_M
    (overridePost (hrx5_S4 x25519 aead_dec xaead_dec gv L FR) (hrx5_RB x25519 gv L FR)).

Definition hrx5_isI (o: hrx5_obj) : Prop := match o with OInit _ => True | _ => False end.
Definition hrx5_isR (o: hrx5_obj) : Prop := match o with OResp _ => True | _ => False end.
Definition hrx5_isC (o: hrx5_obj) : Prop := match o with OCookie _ => True | _ => False end.
Definition hrx5_isZ (o: hrx5_obj) : Prop := match o with OBuf _ => True | _ => False end.

Definition hrx5_B4_I_stmt : Prop := hrx5_B4_M_stmt hrx5_isI.
Definition hrx5_B4_R_stmt : Prop := hrx5_B4_M_stmt hrx5_isR.
Definition hrx5_B4_C_stmt : Prop := hrx5_B4_M_stmt hrx5_isC.
Definition hrx5_B4_Z_stmt : Prop := hrx5_B4_M_stmt hrx5_isZ.
