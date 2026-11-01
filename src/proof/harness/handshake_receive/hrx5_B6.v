(* law handshake_receive: main's phase B6 = body statements 34..38: path, rotated, the harness's model of load / macs / path (rotation CHECK), ds's secret.
   From hrx5_S5 to hrx5_S6 (hrx5_defs.v; the cut: hrx5_cut.v). *)
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B6_pure.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B6_lem.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

(* remove the temp of identifier id from a LOCAL list *)
Ltac hrx5_b6_rm id Q :=
  lazymatch Q with
  | nil => constr:(@nil localdef)
  | temp id _ :: ?Q' => hrx5_b6_rm id Q'
  | ?a :: ?Q' => let r := hrx5_b6_rm id Q' in constr:(a :: r)
  end.

(* replace the SEP item `hbytes sh _ p` (the first one at p) by X *)
Ltac hrx5_b6_rep p X S :=
  lazymatch S with
  | ?F p :: ?S' => constr:(X :: S')
  | ?a :: ?S' => let r := hrx5_b6_rep p X S' in constr:(a :: r)
  end.

(* a closed hypothesis that is false after a case split on a boolean *)
Ltac hrx5_b6_lit x :=
  lazymatch x with
  | Int.one => idtac | Int.zero => idtac | Int.repr 0 => idtac | Int.repr 1 => idtac
  | Int.repr (Z.b2z true) => idtac | Int.repr (Z.b2z false) => idtac
  | Int.repr (Z.b2z (negb true)) => idtac | Int.repr (Z.b2z (negb false)) => idtac
  | (if true then ?y else ?z) => hrx5_b6_lit y; hrx5_b6_lit z
  | (if false then ?y else ?z) => hrx5_b6_lit y; hrx5_b6_lit z
  end.
Ltac hrx5_b6_kill :=
  match goal with
  | Hx: @eq int ?a ?b |- _ => hrx5_b6_lit a; hrx5_b6_lit b; vm_compute in Hx; discriminate Hx
  | Hx: @eq int ?a ?b -> False |- _ => hrx5_b6_lit a; hrx5_b6_lit b; exfalso; apply Hx; vm_compute; reflexivity
  | Hx: ~ @eq int ?a ?b |- _ => hrx5_b6_lit a; hrx5_b6_lit b; exfalso; apply Hx; vm_compute; reflexivity
  | Hx: typed_true _ ?v |- _ =>
      lazymatch v with context [Val.of_bool true] => idtac | context [Val.of_bool false] => idtac
      | Vtrue => idtac | Vfalse => idtac end;
      exfalso; revert Hx; vm_compute; intros Hx; discriminate Hx
  | Hx: typed_false _ ?v |- _ =>
      lazymatch v with context [Val.of_bool true] => idtac | context [Val.of_bool false] => idtac
      | Vtrue => idtac | Vfalse => idtac end;
      exfalso; revert Hx; vm_compute; intros Hx; discriminate Hx
  end.

(* a leaf of the path computation: case split on the verdict v (0..3) and ul *)
Ltac hrx5_b6_vleaf :=
  match goal with Hv: 0 <= fst ?vm <= 3 |- _ =>
    unfold rx_consumes, rx_needs_cookie, VALID_MAC_WITH_COOKIE, VALID_MAC_BUT_NO_COOKIE in *;
    destruct (Z.eqb_spec (fst vm) 3); destruct (Z.eqb_spec (fst vm) 1); try lia;
    repeat match goal with |- context [zeq ?a ?b] => destruct (zeq a b); try lia end
  end;
  repeat match goal with b : bool |- _ =>
    tryif (let x := eval unfold b in b in idtac) then fail else destruct b end;
  cbn [andb orb negb] in *; try hrx5_b6_kill; try reflexivity.

Section B6.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hrx5_B6_ok {Espec: OracleKind} gv L FR :
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_S5 x25519 aead_dec xaead_enc xaead_dec gv L FR) hrx5_B6
    (overridePost (hrx5_S6 x25519 aead_dec xaead_enc xaead_dec gv L FR) (hrx5_RB x25519 gv L FR)).
Proof.
  intros HH. forget (hrx5_RB x25519 gv L FR) as RB. destruct RB as [Rn Rb Rc Rr].
  unfold overridePost. cbv beta iota.
  unfold hrx5_S5, hrx5_Delta. simplify_func_tycontext. abbreviate_semax.
  Intros R sec birth S w NS. Intros PS T head nk KE st. Intros i kc lul q proto ip4.
  Intros ip6 port o dp img tg. Intros ai ar d.
  match goal with Hw: itable_wf T |- _ => rename Hw into Hhrx5_itwf end.
  unfold hrx5_B6.
  unfold hrx5_rest, hrx5_cglobs, hrx5_scr5, hrx5_ltemps, hrx5_lvars, hrx5_ptrs. cbn [app].
  forward. forward.
  set (msg := obj_bytes o) in *.
  assert (Hk: 0 <= obj_kind o <= 3) by (destruct o; simpl; lia).
  set (bk := andb (hrx5_fwd msg) (orb (obj_kind o =? 1) (obj_kind o =? 2))%Z).
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?S))) _ _ =>
    forward_if (PROPx P (LOCALx (temp HRM._t'108 (Val.of_bool bk) :: Q) (SEPx S))) end.
  { assert (Hf: hrx5_fwd msg = true).
    { destruct (hrx5_fwd msg); [reflexivity |]. contradiction. }
    forward_if.
    - forward. entailer!.
      unfold bk; rewrite Hf.
      try (apply (f_equal Int.unsigned) in H8; rewrite !Int.unsigned_repr in H8 by rep_lia).
      rewrite H8. reflexivity.
    - forward. forward. entailer!.
      unfold bk; rewrite Hf. assert (N1: obj_kind o <> 1) by (intro E; apply H8; rewrite E; reflexivity || exact E).
      rewrite (proj2 (Z.eqb_neq _ _) N1). simpl orb.
      destruct (Z.eq_dec (obj_kind o) 2) as [E|E]; [rewrite E; reflexivity |].
      rewrite (proj2 (Z.eqb_neq _ _) E). destruct (zeq (obj_kind o) 2); [contradiction | reflexivity]. }
  { forward. entailer!.
    unfold bk. destruct (hrx5_fwd msg); [vm_compute in H7; discriminate | reflexivity]. }
  set (DL := hrx5_DL x25519 R L sec birth) in *.
  set (W0 := hrx5_W0 DL T PS S w kc lul) in *.
  set (sk := hrx5_skb dp o proto ip4 ip6 port) in *.
  set (W1 := rx_model x25519 aead_dec xaead_enc xaead_dec W0 q (l_skb L) sk msg d) in *.
  set (pth := hrx5_path W0 q sk msg d).
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?S))) _ _ =>
    let Q1 := hrx5_b6_rm HRM._path Q in let Q2 := hrx5_b6_rm HM._m_lul Q1 in
    let Q3 := hrx5_b6_rm HM._secret_birth Q2 in let Q4 := hrx5_b6_rm HRM._rotated Q3 in
    let S1 := hrx5_b6_rep (l_secret L) (hbytes Tsh (cc_secret (d_cc (rw_D W1))) (l_secret L)) S in
    forward_if (PROPx (hrx5_b6_devok DL (rw_D W1) :: P) (LOCALx (temp HRM._path (Vint (Int.repr pth)) :: temp HM._m_lul (Vlong (rw_lul W1)) ::
      temp HM._secret_birth (Vlong (cc_birth (d_cc (rw_D W1)))) :: Q4) (SEPx S1))) end.
  { (* a forwarded initiation / response: the load, the macs, the path *)
    assert (Ebk: bk = true) by (destruct bk; [reflexivity | exfalso; revert H7; vm_compute; intros X; discriminate X]).
    unfold bk in Ebk. apply andb_prop in Ebk. destruct Ebk as [Hf Hk12].
    assert (Hk12': obj_kind o = 1 \/ obj_kind o = 2) by (apply orb_prop in Hk12; destruct Hk12 as [E|E]; lia).
    clear Hk12 H7.
    destruct (hrx5_b6_obj o H3 Hf) as (Hlen & Htw12 & _). pose proof (Htw12 Hk12') as Htw. clear Htw12.
    assert (Hnow: 0 <= Int64.unsigned (s_boot S) < 2 ^ 62) by (destruct H as (_ & _ & _ & X); exact X).
    destruct (hrx5_b6_hs x25519 aead_dec xaead_enc xaead_dec W0 q (l_skb L) sk msg d Hf Htw Hnow)
      as (El & ED & Erl & Ep).
    pose proof (hrx5_b6_log x25519 aead_dec xaead_enc xaead_dec W0 q (l_skb L) sk msg d Hf Htw Hnow
      (proj1 H6) (proj1 (proj2 H6))) as Hlog. cbv zeta in Hlog.
    change (rx_model x25519 aead_dec xaead_enc xaead_dec W0 q (l_skb L) sk msg d) with W1 in El, ED, Erl, Hlog.
    change (hrx5_path W0 q sk msg d) with pth in Ep, Hlog.
    change (rw_S W0) with S in *. change (rw_lul W0) with lul in *. change (rw_D W0) with DL in *.
    set (LM := load_model q lul (s_boot S)) in *.
    set (ul := fst LM) in *.
    set (CC := d_cc DL) in *.
    set (vm := validate_model CC sk msg ul (s_boot S) (s_rlallow S) (rd_r d)) in *.
    rewrite hrx5_b6_qlen. forward. forward.
    (* the load *)
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?S))) _ _ =>
      let Q1 := hrx5_b6_rm HRM._ul Q in let Q2 := hrx5_b6_rm HM._m_lul Q1 in
      forward_if (PROPx P (LOCALx (temp HRM._ul (Vint (Int.repr (Z.b2z ul))) :: temp HM._m_lul (Vlong (snd LM)) :: Q2)
        (SEPx S))) end.
    { pose proof (hrx5_b6_lt512 q H7) as Elt.
      forward. entailer!.
      unfold ul, LM, load_model. rewrite Elt. split; reflexivity. }
    { pose proof (hrx5_b6_lt512' q H7) as Elt.
      forward_if.
      - forward_call (lul, Int64.repr 1, s_boot S). forward.
        forward_if.
        + forward. entailer!.
          destruct (birthdate_expired lul (Int64.repr 1) (s_boot S)) eqn:Eex; [| vm_compute in H9; discriminate].
          unfold ul, LM, load_model. rewrite Elt, Eex, (Int64.eq_false lul Int64.zero H8). split; reflexivity.
        + forward. entailer!.
          destruct (birthdate_expired lul (Int64.repr 1) (s_boot S)) eqn:Eex; [vm_compute in H9; contradiction |].
          unfold ul, LM, load_model. rewrite Elt, Eex, (Int64.eq_false lul Int64.zero H8). split; reflexivity.
      - forward. entailer!.
        unfold ul, LM, load_model. rewrite Elt. split; reflexivity. }
    (* mac1 *)
    change (Zlength (obj_bytes o)) with (Zlength msg) in Hlen. set (n := Zlength msg) in *.
    assert (Hmk: Zlength (hrx5_mk1 x25519 R) = 32) by apply hrx5_b6_ckeys_len.
    unfold img_rep, wg_consts. Intros.
    assert_PROP (@field_compatible HCS (tarray tuchar n) [] img) as FCi by (unfold hbytes; entailer!).
    rewrite (hrx5_b6_split3 Ews msg img) by (auto; lia). fold n. Intros.
    set (P := sublist 0 (n - 32) msg). set (M1 := sublist (n - 32) (n - 16) msg).
    set (M2 := sublist (n - 16) n msg).
    assert (HP: Zlength P = n - 32) by (unfold P; rewrite Zlength_sublist; lia).
    assert (HM1: Zlength M1 = 16) by (unfold M1; rewrite Zlength_sublist; lia).
    assert (HM2: Zlength M2 = 16) by (unfold M2; rewrite Zlength_sublist; lia).
    rewrite <- (hrx5_b6_hin Tsh (hrx5_mk1 x25519 R) (l_mk1 L)) by lia.
    rewrite <- (hrx5_b6_hin Ews P img) by lia.
    forward_call (gv, Tsh, l_mac L, Tsh, l_mk1 L, hrx5_mk1 x25519 R, Ews, img, P).
    { entailer!. rewrite HP, Hmk. simpl. reflexivity. }
    rewrite (hrx5_b6_hin Tsh (hrx5_mk1 x25519 R) (l_mk1 L)) by lia.
    rewrite (hrx5_b6_hin Ews P img) by lia.
    assert (Pimg: isptr img) by (destruct FCi; auto).
    forward_call (Tsh, l_mac L, MAC (hrx5_mk1 x25519 R) P, Ews, offset_val (n - 32) img, M1).
    { entailer!. rewrite (hrx5_b6_offs img n 32), hrx5_b6_MAC_len by (auto; lia). reflexivity. }
    { rewrite hrx5_b6_MAC_len. rep_lia. }
    sep_apply (hrx5_b6_hout Tsh (MAC (hrx5_mk1 x25519 R) P) (l_mac L)). rewrite hrx5_b6_MAC_len.
    (* the verdict, the rotation *)
    set (CC1 := checker_rotate CC (s_boot S) (rd_r d)) in *.
    assert (Hvm: vm =
      if negb (bytes_eqb (MAC (hrx5_mk1 x25519 R) P) M1) then (INVALID_MAC, CC) else
      if negb ul then (VALID_MAC_BUT_NO_COOKIE, CC) else
      if negb (bytes_eqb (MAC (cookie_of (cc_secret CC1) sk) (sublist 0 (n - 16) msg)) M2)
      then (VALID_MAC_BUT_NO_COOKIE, CC1) else
      if negb (s_rlallow S) then (VALID_MAC_WITH_COOKIE_BUT_RATELIMITED, CC1) else (VALID_MAC_WITH_COOKIE, CC1))
      by reflexivity.
    assert (Hrot: validate_rotates CC msg ul (s_boot S) =
      andb (bytes_eqb (MAC (hrx5_mk1 x25519 R) P) M1) (andb ul (checker_rotates CC (s_boot S)))) by reflexivity.
    clearbody vm. clearbody ul.
    remember (bytes_eqb (MAC (hrx5_mk1 x25519 R) P) M1) as b1 eqn:Eb1.
    match goal with |- semax _ (PROPx ?Pp (LOCALx ?Qq (SEPx ?Ss))) _ _ =>
      let Q1 := hrx5_b6_rm HRM._rotated Qq in let Q2 := hrx5_b6_rm HM._secret_birth Q1 in
      let S1 := hrx5_b6_rep (l_secret L) (hbytes Tsh (cc_secret (snd vm)) (l_secret L)) Ss in
      forward_if (PROPx Pp (LOCALx (temp HRM._verdict (Vint (Int.repr (fst vm))) ::
        temp HRM._rotated (Vint (Int.repr (if validate_rotates CC msg ul (s_boot S) then 1 else 0))) ::
        temp HM._secret_birth (Vlong (cc_birth (snd vm))) :: Q2) (SEPx S1))) end.
    { (* mac1 invalid *)
      forward. entailer!.
      - destruct (bytes_eqb (MAC (hrx5_mk1 x25519 R) P) M1); [hrx5_b6_kill |].
        rewrite Hrot. cbn [negb fst snd andb]. split3; reflexivity.
      - destruct (bytes_eqb (MAC (hrx5_mk1 x25519 R) P) M1); [hrx5_b6_kill |].
        cbn [negb fst snd]. apply derives_refl. }
    { forward_if.
      - (* not under load *)
        forward. entailer!.
        + destruct (bytes_eqb (MAC (hrx5_mk1 x25519 R) P) M1); [| hrx5_b6_kill].
          destruct ul; [hrx5_b6_kill |].
          rewrite Hrot. cbn [negb fst snd andb]. split3; reflexivity.
        + destruct (bytes_eqb (MAC (hrx5_mk1 x25519 R) P) M1); [| hrx5_b6_kill].
          destruct ul; [hrx5_b6_kill |].
          cbn [negb fst snd]. apply derives_refl.
      - (* under load: the rotation, mac2, the rate limiter *)
        destruct b1; [| hrx5_b6_kill]. destruct ul; [| hrx5_b6_kill].
        assert (HCC1: d_cc (rw_D W1) = CC1).
        { rewrite ED, Hvm. cbn [negb]. destruct (bytes_eqb _ M2); destruct (s_rlallow S); reflexivity. }
        assert (Lsec: Zlength sec = 32) by (destruct H as (_ & X & _); exact X).
        assert (LCC1: Zlength (cc_secret CC1) = 32).
        { unfold CC1, checker_rotate. destruct (birthdate_expired _ _ _); [apply H6 | exact Lsec]. }
        forward_call (birth, Int64.repr 120, s_boot S).
        match goal with |- semax _ (PROPx ?Pp (LOCALx ?Qq (SEPx ?Ss))) _ _ =>
          let Q1 := hrx5_b6_rm HRM._rotated Qq in let Q2 := hrx5_b6_rm HM._secret_birth Q1 in
          let S1 := hrx5_b6_rep (l_secret L) (hbytes Tsh (cc_secret CC1) (l_secret L)) Ss in
          forward_if (PROPx Pp (LOCALx (
            temp HRM._rotated (Vint (Int.repr (if birthdate_expired birth (Int64.repr 120) (s_boot S) then 1 else 0))) ::
            temp HM._secret_birth (Vlong (cc_birth CC1)) :: Q2) (SEPx S1))) end.
        + destruct (birthdate_expired birth (Int64.repr 120) (s_boot S)) eqn:Eex; [| hrx5_b6_kill].
          forward. forward.
          sep_apply (hrx5_b6_rxw_sec W gv Tsh (l_wd L) head W1). rewrite HCC1.
          sep_apply (hrx5_b6_hout Tsh sec (l_secret L)). rewrite Lsec.
          forward_call (Tsh, l_secret L, Tsh, cc_addr (l_wd L), cc_secret CC1).
          { rewrite LCC1. entailer!. simpl. unfold cc_addr, OFS_DEV_CHECKER.
            rewrite offset_offset_val, Z.add_0_r. reflexivity. }
          { rewrite LCC1. cancel. }
          sep_apply (modus_ponens_wand (hbytes Tsh (cc_secret CC1) (cc_addr (l_wd L)))).
          entailer!. try unfold CC1. unfold checker_rotate. change (cc_birth CC) with birth. rewrite Eex. reflexivity.
        + destruct (birthdate_expired birth (Int64.repr 120) (s_boot S)) eqn:Eex; [hrx5_b6_kill |].
          forward. entailer!.
          * try unfold CC1. unfold checker_rotate. change (cc_birth CC) with birth. rewrite Eex. reflexivity.
          * try unfold CC1. unfold checker_rotate. change (cc_birth CC) with birth. rewrite Eex. apply derives_refl.
        + (* mac2 with the cookie of the (rotated) secret *)
          clearbody CC1. clear HCC1.
          (* m_cookie's spec reads the skb as skb_src_rep (data and len any; spec 1ca2d0e) *)
          rewrite (skb_src_rep_full Tsh (l_skb L) sk).
          forward_call (gv, Tsh, l_c L, Tsh, l_secret L, cc_secret CC1, Tsh, l_skb L, sk, sk_data sk, Vint (sk_len sk)).
          rewrite <- (skb_src_rep_full Tsh (l_skb L) sk).
          pose proof (hrx5_b6_join2 Ews msg img ltac:(lia) FCi) as J2.
          change (Zlength msg) with n in J2. fold P M1 in J2.
          sep_apply (derives_refl' _ _ J2).
          set (P16 := sublist 0 (n - 16) msg) in *.
          assert (HP16: Zlength P16 = n - 16) by (unfold P16; rewrite Zlength_sublist; lia).
          rewrite <- (hrx5_b6_hin Tsh (cookie_of (cc_secret CC1) sk) (l_c L)) by (rewrite hrx5_b6_cookie_len; lia).
          rewrite <- (hrx5_b6_hin Ews P16 img) by lia.
          forward_call (gv, Tsh, l_mac L, Tsh, l_c L, cookie_of (cc_secret CC1) sk, Ews, img, P16).
          { entailer!. rewrite hrx5_b6_cookie_len, HP16. reflexivity. }
          { rewrite hrx5_b6_cookie_len, HP16. rep_lia. }
          rewrite (hrx5_b6_hin Tsh (cookie_of (cc_secret CC1) sk) (l_c L)) by (rewrite hrx5_b6_cookie_len; lia).
          rewrite (hrx5_b6_hin Ews P16 img) by lia.
          forward_call (Tsh, l_mac L, MAC (cookie_of (cc_secret CC1) sk) P16, Ews, offset_val (n - 16) img, M2).
          { entailer!. rewrite (hrx5_b6_offs img n 16), hrx5_b6_MAC_len by (auto; lia). reflexivity. }
          { rewrite hrx5_b6_MAC_len. rep_lia. }
          sep_apply (derives_refl' _ _ (eq_sym J2)).
          sep_apply (hrx5_b6_hout Tsh (MAC (cookie_of (cc_secret CC1) sk) P16) (l_mac L)).
          sep_apply (hrx5_b6_hout Tsh (cookie_of (cc_secret CC1) sk) (l_c L)).
          rewrite hrx5_b6_MAC_len, hrx5_b6_cookie_len.
          forward_if.
          * forward. entailer!.
            -- destruct (bytes_eqb (MAC (cookie_of (cc_secret CC1) sk) P16) M2); [hrx5_b6_kill |].
               rewrite Hrot. cbn [negb fst snd andb]. split3; reflexivity.
            -- destruct (bytes_eqb (MAC (cookie_of (cc_secret CC1) sk) P16) M2); [hrx5_b6_kill |].
               cbn [negb fst snd]. apply derives_refl.
          * sep_apply (hrx5_b6_rxw_shim W gv Tsh (l_wd L) head W1). rewrite Erl. Intros.
            forward.
            { entailer!. destruct (s_rlallow S); simpl; auto. }
            sep_apply (modus_ponens_wand (hbytes Ews (s_log (rw_S W1)) (gv _wg_shim_random_log) *
              hbytes Ews (s_logprev (rw_S W1)) (gv _wg_shim_random_log_prev) *
              @data_at W Ews tbool (Val.of_bool (s_rlallow S)) (gv HM._wg_shim_ratelimit_allow))).
            forward_if.
            -- forward. entailer!.
               ++ destruct (bytes_eqb (MAC (cookie_of (cc_secret CC1) sk) P16) M2); [| hrx5_b6_kill].
                  destruct (s_rlallow S); [hrx5_b6_kill |].
                  rewrite Hrot. cbn [negb fst snd andb]. split3; reflexivity.
               ++ destruct (bytes_eqb (MAC (cookie_of (cc_secret CC1) sk) P16) M2); [| hrx5_b6_kill].
                  destruct (s_rlallow S); [hrx5_b6_kill |].
                  cbn [negb fst snd]. apply derives_refl.
            -- forward. entailer!.
               ++ destruct (bytes_eqb (MAC (cookie_of (cc_secret CC1) sk) P16) M2); [| hrx5_b6_kill].
                  destruct (s_rlallow S); [| hrx5_b6_kill].
                  rewrite Hrot. cbn [negb fst snd andb]. split3; reflexivity.
               ++ destruct (bytes_eqb (MAC (cookie_of (cc_secret CC1) sk) P16) M2); [| hrx5_b6_kill].
                  destruct (s_rlallow S); [| hrx5_b6_kill].
                  cbn [negb fst snd]. apply derives_refl. }
    (* the path *)
    assert (HJd: hrx5_b6_devok DL (rw_D W1)).
    { exists (snd vm). split; [exact ED |].
      assert (Lsec: Zlength sec = 32) by (destruct H as (_ & X & _); exact X).
      rewrite Hvm. repeat match goal with |- context [if ?b then _ else _] => destruct b end;
        cbn [snd]; try (split3; [reflexivity | reflexivity | split; [reflexivity | exact Lsec]]);
        unfold CC1, checker_rotate; destruct (birthdate_expired _ _ _);
        (split3; [reflexivity | reflexivity | split; [reflexivity | first [apply H6 | exact Lsec]]]). }
    assert (HRs: validate_rotates CC msg ul (s_boot S) = true -> cc_secret (snd vm) = rd_r d).
    { rewrite Hrot, Hvm. intros Hr. destruct b1; [| discriminate]. destruct ul; [| discriminate].
      cbn [andb] in Hr. cbn [negb].
      assert (E1: cc_secret CC1 = rd_r d).
      { unfold CC1, checker_rotate. unfold checker_rotates in Hr. rewrite Hr. reflexivity. }
      repeat match goal with |- context [if ?b then _ else _] => destruct b end; exact E1. }
    assert (Hv03: 0 <= fst vm <= 3).
    { rewrite Hvm. unfold INVALID_MAC, VALID_MAC_BUT_NO_COOKIE, VALID_MAC_WITH_COOKIE_BUT_RATELIMITED,
        VALID_MAC_WITH_COOKIE.
      repeat match goal with |- context [if ?b then _ else _] => destruct b end; cbn [fst]; lia. }
    clear Hvm.
    match goal with |- semax _ (PROPx ?Pp (LOCALx ?Qq (SEPx ?Ss))) _ _ =>
      forward_if (PROPx Pp (LOCALx (temp HRM._t'104 (Val.of_bool (andb ul (fst vm =? 3))) :: Qq) (SEPx Ss))) end.
    { forward. entailer!. cbn [andb].
      match goal with |- context [?x =? 3] => destruct (Z.eqb_spec x 3); destruct (zeq x 3); try lia; reflexivity end. }
    { forward. entailer!. }
    match goal with |- semax _ (PROPx ?Pp (LOCALx ?Qq (SEPx ?Ss))) _ _ =>
      forward_if (PROPx Pp (LOCALx (temp HRM._t'105 (Val.of_bool (rx_consumes ul (fst vm))) :: Qq) (SEPx Ss))) end.
    { forward. entailer!; hrx5_b6_vleaf. }
    { forward_if.
      - forward. forward. entailer!; hrx5_b6_vleaf.
      - forward. entailer!; hrx5_b6_vleaf. }
    match goal with |- semax _ (PROPx ?Pp (LOCALx ?Qq (SEPx ?Ss))) _ _ =>
      let Q1 := hrx5_b6_rm HRM._path Qq in
      forward_if (PROPx Pp (LOCALx (temp HRM._path (Vint (Int.repr pth)) :: Q1) (SEPx Ss))) end.
    { forward. entailer!; rewrite Ep; hrx5_b6_vleaf. }
    { match goal with |- semax _ (PROPx ?Pp (LOCALx ?Qq (SEPx ?Ss))) _ _ =>
        forward_if (PROPx Pp (LOCALx (temp HRM._t'103 (Val.of_bool (rx_needs_cookie ul (fst vm))) :: Qq)
          (SEPx Ss))) end.
      - forward. entailer!; hrx5_b6_vleaf.
      - forward. entailer!; hrx5_b6_vleaf.
      - forward_if.
        + forward. entailer!; rewrite Ep; hrx5_b6_vleaf.
        + forward. entailer!; rewrite Ep; hrx5_b6_vleaf. }
    (* the rotation's CHECK, then the join *)
    pose proof (hrx5_b6_split3 Ews msg img ltac:(lia) FCi) as J3.
    change (Zlength msg) with n in J3. fold P M1 M2 in J3.
    sep_apply (derives_refl' _ _ (eq_sym J3)). clear J3.
    rewrite <- hrx5_b6_qlen.
    forward_if.
    - destruct (validate_rotates CC msg ul (s_boot S)) eqn:Er; [| hrx5_b6_kill].
      pose proof (HRs eq_refl) as Esec. destruct (Hlog eq_refl) as [Hl2 Hln2]. clear HRs Hlog.
      rewrite Esec.
      sep_apply (hrx5_b6_rxw_shim W gv Tsh (l_wd L) head W1). Intros.
      assert (Lr: Zlength (rd_r d) = 32) by apply H6.
      destruct (Z.eq_dec pth 2) as [E2|E2].
      + rewrite (Hl2 E2).
        match goal with |- semax _ ?Pre _ _ => forward_loop Pre break: Pre end.
        * entailer!.
        * match goal with |- semax _ (PROPx ?Pp (LOCALx ?Qq (SEPx ?Ss))) _ _ =>
            forward_if (PROPx Pp (LOCALx (temp HRM._t'106 (gv HRM._wg_shim_random_log_prev) :: Qq) (SEPx Ss))) end.
          -- forward. entailer!.
          -- forward. entailer!.
          -- forward_call (Tsh, l_secret L, rd_r d, Ews, gv _wg_shim_random_log_prev, rd_r d).
             { entailer!. rewrite Lr. reflexivity. }
             assert (Hb: bytes_eqb (rd_r d) (rd_r d) = true)
               by (unfold bytes_eqb; destruct list_eq_dec; congruence).
             rewrite Hb.
             forward_if True; [discriminate | forward; entailer! |].
             forward. entailer!.
        * sep_apply (modus_ponens_wand (hbytes Ews (s_log (rw_S W1)) (gv _wg_shim_random_log) *
            hbytes Ews (rd_r d) (gv _wg_shim_random_log_prev) *
            @data_at W Ews tbool (Val.of_bool (s_rlallow (rw_S W1))) (gv HM._wg_shim_ratelimit_allow))).
          unfold img_rep, wg_consts. entailer!.
          all: first [ rewrite ED; reflexivity
                     | rewrite ED; cbn [d_cc dev_set_cc]; rewrite Esec; apply derives_refl ].
      + rewrite (Hln2 E2).
        match goal with |- semax _ ?Pre _ _ => forward_loop Pre break: Pre end.
        * entailer!.
        * match goal with |- semax _ (PROPx ?Pp (LOCALx ?Qq (SEPx ?Ss))) _ _ =>
            forward_if (PROPx Pp (LOCALx (temp HRM._t'106 (gv HRM._wg_shim_random_log) :: Qq) (SEPx Ss))) end.
          -- assert (Hp012: 0 <= pth <= 2)
               by (rewrite Ep; repeat match goal with |- context [if ?b then _ else _] => destruct b end; lia).
             match goal with Hx: Int.repr _ = Int.repr 2 |- _ =>
               apply repr_inj_signed in Hx; [contradiction | rep_lia | rep_lia] end.
          -- forward. entailer!.
          -- forward_call (Tsh, l_secret L, rd_r d, Ews, gv _wg_shim_random_log, rd_r d).
             { entailer!. rewrite Lr. reflexivity. }
             assert (Hb: bytes_eqb (rd_r d) (rd_r d) = true)
               by (unfold bytes_eqb; destruct list_eq_dec; congruence).
             rewrite Hb.
             forward_if True; [discriminate | forward; entailer! |].
             forward. entailer!.
        * sep_apply (modus_ponens_wand (hbytes Ews (rd_r d) (gv _wg_shim_random_log) *
            hbytes Ews (s_logprev (rw_S W1)) (gv _wg_shim_random_log_prev) *
            @data_at W Ews tbool (Val.of_bool (s_rlallow (rw_S W1))) (gv HM._wg_shim_ratelimit_allow))).
          unfold img_rep, wg_consts. entailer!.
          all: first [ rewrite ED; reflexivity
                     | rewrite ED; cbn [d_cc dev_set_cc]; rewrite Esec; apply derives_refl ].
    - forward. unfold img_rep, wg_consts. entailer!.
      all: first [ rewrite ED; reflexivity | rewrite ED; cbn [d_cc dev_set_cc]; apply derives_refl ]. }
  { forward_if.
    - assert (Hf: hrx5_fwd msg = true).
      { destruct (hrx5_fwd msg); [reflexivity |]. contradiction. }
      destruct (hrx5_b6_obj o H3 Hf) as (Hlen & _ & Htw).
      assert (Hk12: obj_kind o <> 1 /\ obj_kind o <> 2).
      { unfold bk in H7. rewrite Hf in H7. simpl in H7.
        destruct (obj_kind o =? 1) eqn:E1; [vm_compute in H7; discriminate |].
        destruct (obj_kind o =? 2) eqn:E2; [vm_compute in H7; discriminate |]. lia. }
      destruct (hrx5_b6_cookie x25519 aead_dec xaead_enc xaead_dec W0 q (l_skb L) sk msg d Hf
        (Htw (proj1 Hk12) (proj2 Hk12))) as (El & ED & Ep).
      change (rw_lul W1 = rw_lul W0) in El. change (rw_D W1 = rw_D W0) in ED.
      forward. entailer!.
      + split; [exists (d_cc DL); rewrite ED; repeat split; apply H |].
        unfold pth. rewrite El, ED, Ep. split3; reflexivity.
      + rewrite ED. apply derives_refl.
    - assert (Hf: hrx5_fwd msg = false).
      { destruct (hrx5_fwd msg); [vm_compute in H8; discriminate | reflexivity]. }
      destruct (hrx5_b6_nofwd x25519 aead_dec xaead_enc xaead_dec W0 q (l_skb L) sk msg d Hf) as (E1 & Ep).
      change (W1 = W0) in E1.
      forward. entailer!.
      + split; [exists (d_cc DL); rewrite E1; repeat split; apply H |].
        unfold pth. rewrite E1, Ep. split3; reflexivity.
      + rewrite E1. apply derives_refl. }
  (* the tail: ds's secret and secret_birthdate *)
  Intros. rename H7 into HDV.
  assert (Lsec: Zlength (cc_secret (d_cc (rw_D W1))) = 32).
  { destruct HDV as (CC & E & _ & _ & _ & L32). rewrite E. exact L32. }
  rewrite (hrx5_b6_ds_open Tsh DL head (l_ds L)).
  sep_apply (hrx5_b6_out_cs Tsh (bytes (cc_secret (d_cc DL))) (offset_val 73 (l_ds L))).
  forward_call (Tsh, offset_val 73 (l_ds L), Tsh, l_secret L, cc_secret (d_cc (rw_D W1))).
  { entailer!. rewrite Lsec. simpl. f_equal. }
  { rewrite Lsec. cancel. }
  forward.
  rewrite (hrx5_b6_in_cs Tsh _ _ Lsec).
  sep_apply (hrx5_b6_ds_close Tsh DL (rw_D W1) head (l_ds L) HDV).
  sep_apply (hrx5_b6_hout Tsh (cc_secret (d_cc (rw_D W1))) (l_secret L)). rewrite Lsec.
  unfold hrx5_S6.
  Exists R sec birth S w NS. Exists PS T head nk KE st. Exists i kc lul q proto ip4.
  Exists ip6 port o dp img tg. Exists ai ar d. cbv zeta. fold DL W0 sk W1.
  unfold hrx5_rest, hrx5_cglobs, hrx5_scr5, hrx5_lvars, hrx5_ptrs. cbn [app].
  entailer!.
  all: apply derives_refl.
Qed.

End B6.
