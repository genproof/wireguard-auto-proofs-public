(* law cookie_reply, phase P5 (statements 36..44 of main) cut into three segments:
     A = 36..37  the rotation CHECKs (wg_shim_random_log / _prev), the CHECK of B's checker   S4 -> T1
     B = 38..40  m_cookie, k (m_label_key or bytes_set), the CHECK of the cookie key          T1 -> T2
     C = 41..44  the CHECK of the reply's header, xchacha20poly1305_encrypt, the CHECK of the
                 encrypted cookie, the CHECK msg == copy                                       T2 -> S5
   The states T1, T2 carry S5's fact hcy5_reply_ok (CK = B's cookie, CM = B's reply), temp secret_birth and the
   buffer secret (B's birthdate / secret after the rotation) and the snapshots da / db / sks / ss as in S4. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_cut.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_spec.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_defs.
Require WgNoise.harness.x_cookie_reply.code.
Local Open Scope logic.

(* the three segments *)
Definition hcy5_p5_A := ltac:(let x := eval cbv beta iota delta [hcy5_l hcy5_seql firstn skipn hcy5_stmts] in (hcy5_seql (hcy5_l 36 2)) in exact x).
Definition hcy5_p5_B := ltac:(let x := eval cbv beta iota delta [hcy5_l hcy5_seql firstn skipn hcy5_stmts] in (hcy5_seql (hcy5_l 38 3)) in exact x).
Definition hcy5_p5_C := ltac:(let x := eval cbv beta iota delta [hcy5_l hcy5_seql firstn skipn hcy5_stmts] in (hcy5_seql (hcy5_l 41 4)) in exact x).

Lemma hcy5_p5_eq : hcy5_P5 = hcy5_seqs (hcy5_l 36 2) (hcy5_seqs (hcy5_l 38 3) (hcy5_seql (hcy5_l 41 4))).
Proof. reflexivity. Qed.

Lemma hcy5_p5_segs_eq :
  hcy5_p5_A = hcy5_seql (hcy5_l 36 2) /\ hcy5_p5_B = hcy5_seql (hcy5_l 38 3) /\
  hcy5_p5_C = hcy5_seql (hcy5_l 41 4).
Proof. repeat split. Qed.

Section States.
Variable x25519: list byte -> list byte -> list byte.
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.

(* after A: the buffer secret / temp secret_birth hold B's secret / birthdate after the rotation (= the
   checker's), the shim any *)
Definition hcy5_p5_T1 (gv: globals) (L: hcy5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hcy5_run, EX S: shim, EX m: val, EX c: val, EX rp: val, EX Q: hcy5_pkt,
  EX nonce: list byte, EX rr: list byte, EX CK: list byte, EX CM: cookie_msg,
  PROPx [hcy5_reply_ok x25519 xaead_enc R L Q m nonce rr CK CM]
  (LOCALx ([temp HY._cns nullval; temp HY._len (Vlong (Int64.repr (q_n Q)));
            temp HY._msg m; temp HY._copy c; temp HY._reply rp;
            temp HY._index (Vint (q_index Q));
            temp HY._secret_birth (Vlong (cc_birth (hcy5_CC2 x25519 R L Q rr)))] ++ hcy5_lvars gv L)
  (SEPx (hcy5_aside0 x25519 R L ++ hcy5_bside x25519 R L (hcy5_CC2 x25519 R L Q rr) ++
         hcy5_bufs x25519 R L ++ hcy5_pbufs L Q m c rp ++
         [cmsg_rep Ews rp CM;
          hbytes Tsh (cc_secret (hcy5_CC2 x25519 R L Q rr)) (l_secret L); hout Tsh 32 (l_pub L);
          hout Tsh 16 (l_cookie L); hout Tsh 32 (l_k L); hout Tsh 32 (l_enc L); hout Tsh 64 (l_img L);
          hout Tsh 64 (l_img2 L); hout Tsh 16 (l_pt L);
          @data_at_ W Tsh t_devsnap (l_da L);
          @data_at CKS Tsh t_devsnap (devsnap_val (hcy5_DBc x25519 R L (hcy5_CC1 x25519 R L)) nullval) (l_db L);
          @data_at CKS Tsh t_skbsnap (skbsnap_val (hcy5_skb Q m)) (l_sks L);
          @data_at_ W Tsh t_shimsnap (l_ss L)] ++
         hcy5_globs gv S FR))).

(* after B: the buffer cookie holds B's cookie CK, the buffer k B's cookie encryption key *)
Definition hcy5_p5_T2 (gv: globals) (L: hcy5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hcy5_run, EX S: shim, EX m: val, EX c: val, EX rp: val, EX Q: hcy5_pkt,
  EX nonce: list byte, EX rr: list byte, EX CK: list byte, EX CM: cookie_msg,
  PROPx [hcy5_reply_ok x25519 xaead_enc R L Q m nonce rr CK CM]
  (LOCALx ([temp HY._cns nullval; temp HY._len (Vlong (Int64.repr (q_n Q)));
            temp HY._msg m; temp HY._copy c; temp HY._reply rp;
            temp HY._index (Vint (q_index Q));
            temp HY._secret_birth (Vlong (cc_birth (hcy5_CC2 x25519 R L Q rr)))] ++ hcy5_lvars gv L)
  (SEPx (hcy5_aside0 x25519 R L ++ hcy5_bside x25519 R L (hcy5_CC2 x25519 R L Q rr) ++
         hcy5_bufs x25519 R L ++ hcy5_pbufs L Q m c rp ++
         [cmsg_rep Ews rp CM; hbytes Tsh CK (l_cookie L); hout Tsh 64 (l_img L);
          hbytes Tsh (cc_secret (hcy5_CC2 x25519 R L Q rr)) (l_secret L);
          @data_at_ W Tsh t_devsnap (l_da L);
          @data_at CKS Tsh t_devsnap (devsnap_val (hcy5_DBc x25519 R L (hcy5_CC1 x25519 R L)) nullval) (l_db L);
          @data_at CKS Tsh t_skbsnap (skbsnap_val (hcy5_skb Q m)) (l_sks L);
          @data_at_ W Tsh t_shimsnap (l_ss L);
          hbytes Tsh (cc_ekey (hcy5_CC1 x25519 R L)) (l_k L);
          hout Tsh 32 (l_pub L); hout Tsh 32 (l_enc L); hout Tsh 64 (l_img2 L); hout Tsh 16 (l_pt L)] ++
         hcy5_globs gv S FR))).

End States.
