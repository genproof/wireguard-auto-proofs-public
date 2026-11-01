(* law cookie_mac, phase P7 (statements 82..86 of hck5_cut.v) cut into its five statements,
   and the two intermediate states.
   s82 = m_mac(mac1, wb.cookie_checker.message_mac1_key, 32, copy, len - 32)            S6  -> T1
   s83 = t' = bytes_eq(mac1, copy + len - 32, 16); the verdict if-chain                 T1  -> T2
   s84 = CHECK((int)r == verdict)                                                        T2  -> T2
   s85 = CHECK(wb.cookie_checker.secret_birthdate == secret_birth && bytes_eq(..secret..)) T2 -> T2
   s86 = CHECK(bytes_eq(msg, copy, len) && skb.data == msg && skb.len == len)            T2  -> S7
   v2: the states carry the A item hck5_A, the temps kes / head0 / refs0 and the snapshots hck5_snaps (untouched). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.cookie_mac.hck5_cut.
Require Import WgNoise.proof.harness.cookie_mac.hck5_spec.
Require Import WgNoise.proof.harness.cookie_mac.hck5_defs.
Require WgNoise.harness.x_cookie_mac.code.
Local Open Scope logic.

Definition hck5_p7_s82 := ltac:(let x := eval cbv beta iota delta [nth hck5_stmts] in (nth 82 hck5_stmts Sskip) in exact x).
Definition hck5_p7_s83 := ltac:(let x := eval cbv beta iota delta [nth hck5_stmts] in (nth 83 hck5_stmts Sskip) in exact x).
Definition hck5_p7_s84 := ltac:(let x := eval cbv beta iota delta [nth hck5_stmts] in (nth 84 hck5_stmts Sskip) in exact x).
Definition hck5_p7_s85 := ltac:(let x := eval cbv beta iota delta [nth hck5_stmts] in (nth 85 hck5_stmts Sskip) in exact x).
Definition hck5_p7_s86 := ltac:(let x := eval cbv beta iota delta [nth hck5_stmts] in (nth 86 hck5_stmts Sskip) in exact x).

Lemma hck5_p7_eq :
  hck5_P7 = Ssequence hck5_p7_s82 (Ssequence hck5_p7_s83 (Ssequence hck5_p7_s84 (Ssequence hck5_p7_s85 hck5_p7_s86))).
Proof. reflexivity. Qed.

Section States.
Variable x25519: list byte -> list byte -> list byte.

(* after s82: mac1 holds M1 = MAC(wb's mac1 key, msg[0..len-32)) (wb's checker after validate: snd VR) *)
Definition hck5_T1 (gv: globals) (L: hck5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hck5_run, EX S: shim, EX A: hck5_aval, EX m: val, EX c: val, EX Q: hck5_pkt, EX cmode: bool,
  EX C: cookie, EX ck: list byte, EX MSG1: list byte, EX C1: cookie,
  EX MSG2: list byte, EX corrupted: bool, EX chk: bool, EX rl: bool, EX r: list byte, EX VR: Z * checker,
  EX M1: list byte,
  PROPx [hck5_run_ok x25519 R; hck5_aok L A; hck5_pkt_ok Q;
         hck5_is ck (cookie_of (r_secret R) (hck5_skb Q m)); hck5_ck_ok R Q cmode C ck;
         hck5_is (MSG1, C1) (add_mac_model C (q_msg Q) (q_now Q)); Zlength MSG1 = q_n Q;
         hck5_after_val x25519 R L Q m cmode MSG1 MSG2 corrupted chk rl r VR S;
         hck5_is M1 (mac1_of (cc_mkey (snd VR)) MSG2); Zlength M1 = 16]
  (LOCALx ([temp HK._corrupted (Vint (if corrupted then Int.one else Int.zero));
            temp HK._honest_peer (Vint (if r_honest R then Int.one else Int.zero));
            temp HK._kes (a_kes A); temp HK._head0 (a_head0 A); temp HK._refs0 (Vint (p_refs (a_P A)));
            temp HK._len (Vlong (Int64.repr (q_n Q))); temp HK._msg m; temp HK._copy c;
            temp HK._now (Vlong (q_now Q));
            temp HK._cookie_mode (Vint (if cmode then Int.one else Int.zero));
            temp HK._check_cookie (Vint (if chk then Int.one else Int.zero));
            temp HK._secret_birth (Vlong (cc_birth (hck5_CC2 x25519 R L (q_now Q) cmode)));
            temp HK._r (Vint (Int.repr (fst VR)))] ++ hck5_lvars gv L)
  (SEPx ([hck5_A x25519 R L A] ++ hck5_bside x25519 R L ++ hck5_bufs x25519 R L ++
         [checker_rep Tsh (cc_addr (l_wb L)) (snd VR);
          cookie_rep Tsh (cookie_addr (l_p L)) C1;
          skb_rep Tsh (l_skb L) (hck5_skb Q m);
          hck5_tok (q_n Q) m; hbytes Ews MSG2 m; hck5_tok (q_n Q) c; hbytes Ews MSG2 c;
          hbytes Tsh (cc_secret (hck5_CC2 x25519 R L (q_now Q) cmode)) (l_secret L)] ++
         [hout Tsh 32 (l_k L); hbytes Tsh M1 (l_mac1 L); hout Tsh 16 (l_mac2 L); hout Tsh 16 (l_cookie L);
          @data_at_ CKS Tsh t_cksnap (l_cs L)] ++
         hck5_snaps x25519 R L A C1 (hck5_CC2 x25519 R L (q_now Q) cmode) S (Some (hck5_skb Q m)) ++
         hck5_globs gv S FR))).

(* after s83 (and s84, s85): verdict = fst VR (the harness's verdict is validate's), secret_birth / secret =
   B's checker's birthdate / secret after validate (snd VR); the scratch buffers any *)
Definition hck5_T2 (gv: globals) (L: hck5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hck5_run, EX S: shim, EX A: hck5_aval, EX m: val, EX c: val, EX Q: hck5_pkt, EX cmode: bool,
  EX C: cookie, EX ck: list byte, EX MSG1: list byte, EX C1: cookie,
  EX MSG2: list byte, EX corrupted: bool, EX chk: bool, EX rl: bool, EX r: list byte, EX VR: Z * checker,
  PROPx [hck5_run_ok x25519 R; hck5_aok L A; hck5_pkt_ok Q;
         hck5_is ck (cookie_of (r_secret R) (hck5_skb Q m)); hck5_ck_ok R Q cmode C ck;
         hck5_is (MSG1, C1) (add_mac_model C (q_msg Q) (q_now Q)); Zlength MSG1 = q_n Q;
         hck5_after_val x25519 R L Q m cmode MSG1 MSG2 corrupted chk rl r VR S]
  (LOCALx ([temp HK._corrupted (Vint (if corrupted then Int.one else Int.zero));
            temp HK._honest_peer (Vint (if r_honest R then Int.one else Int.zero));
            temp HK._kes (a_kes A); temp HK._head0 (a_head0 A); temp HK._refs0 (Vint (p_refs (a_P A)));
            temp HK._len (Vlong (Int64.repr (q_n Q))); temp HK._msg m; temp HK._copy c;
            temp HK._now (Vlong (q_now Q));
            temp HK._cookie_mode (Vint (if cmode then Int.one else Int.zero));
            temp HK._check_cookie (Vint (if chk then Int.one else Int.zero));
            temp HK._secret_birth (Vlong (cc_birth (snd VR)));
            temp HK._r (Vint (Int.repr (fst VR)));
            temp HK._verdict (Vint (Int.repr (fst VR)))] ++ hck5_lvars gv L)
  (SEPx ([hck5_A x25519 R L A] ++ hck5_bside x25519 R L ++ hck5_bufs x25519 R L ++
         [checker_rep Tsh (cc_addr (l_wb L)) (snd VR);
          cookie_rep Tsh (cookie_addr (l_p L)) C1;
          skb_rep Tsh (l_skb L) (hck5_skb Q m);
          hck5_tok (q_n Q) m; hbytes Ews MSG2 m; hck5_tok (q_n Q) c; hbytes Ews MSG2 c;
          hbytes Tsh (cc_secret (snd VR)) (l_secret L)] ++
         hck5_scr2 L ++
         hck5_snaps x25519 R L A C1 (hck5_CC2 x25519 R L (q_now Q) cmode) S (Some (hck5_skb Q m)) ++
         hck5_globs gv S FR))).

End States.
