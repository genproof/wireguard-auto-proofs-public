(* law handshake_receive, phase B8 branch C: the entry hrx5_B8_Q (branch C) |-- EX M a P pt, QC0 (the pure analysis of the accepted cookie reply).
*)
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_ilem.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_C_defs.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* the pure analysis of branch C                                           *)
(* ---------------------------------------------------------------------- *)

Local Open Scope Z_scope.

Lemma hrx5_B8CP_le32 v : le32_val (le32 v) = v.
Proof.
  unfold le32_val, le32. cbn [map].
  assert (Z0: forall (x0 x1 x2 x3: byte), Znth 0 [x0; x1; x2; x3] = x0) by reflexivity.
  assert (Z1: forall (x0 x1 x2 x3: byte), Znth 1 [x0; x1; x2; x3] = x1) by reflexivity.
  assert (Z2: forall (x0 x1 x2 x3: byte), Znth 2 [x0; x1; x2; x3] = x2) by reflexivity.
  assert (Z3: forall (x0 x1 x2 x3: byte), Znth 3 [x0; x1; x2; x3] = x3) by reflexivity.
  rewrite Z0, Z1, Z2, Z3. clear Z0 Z1 Z2 Z3.
  pose proof (Int.unsigned_range v) as Hv. set (u := Int.unsigned v) in *.
  rewrite !Byte.unsigned_repr_eq. change Byte.modulus with 256.
  change (2 ^ (8 * 0)) with 1. change (2 ^ (8 * 1)) with 256. change (2 ^ (8 * 2)) with 65536.
  change (2 ^ (8 * 3)) with 16777216. change (2 ^ 8) with 256. change (2 ^ 16) with 65536.
  change (2 ^ 24) with 16777216. rewrite Z.div_1_r.
  rewrite <- (Int.repr_unsigned v). fold u. f_equal.
  change Int.modulus with 4294967296 in Hv.
  rewrite (Z.mod_small (u / 16777216) 256) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  assert (E1: u mod 256 + u / 256 mod 256 * 256 = u mod 65536).
  { pose proof (Z.mod_mul_r u 256 256 ltac:(lia) ltac:(lia)) as X. change (256 * 256) with 65536 in X. rewrite Z.quot_div_nonneg in X by lia.
    rewrite !Z.rem_mod_nonneg in X by (try apply Z.div_pos; lia). lia. }
  assert (E2: u mod 65536 + u / 65536 mod 256 * 65536 = u mod 16777216).
  { pose proof (Z.mod_mul_r u 65536 256 ltac:(lia) ltac:(lia)) as X. change (65536 * 256) with 16777216 in X. rewrite Z.quot_div_nonneg in X by lia.
    rewrite !Z.rem_mod_nonneg in X by (try apply Z.div_pos; lia). lia. }
  assert (E3: u mod 16777216 + u / 16777216 * 16777216 = u).
  { rewrite (Z.div_mod u 16777216) at 3 by lia. lia. }
  lia.
Qed.

Lemma hrx5_B8CP_len M : cm_ok M -> Zlength (cookie_msg_bytes M) = 64.
Proof.
  intros (H1 & H2). unfold cookie_msg_bytes, le32. autorewrite with sublist.
  rewrite H1, H2. reflexivity.
Qed.

Lemma hrx5_B8CP_cm_of M : cm_ok M -> cm_of (cookie_msg_bytes M) = M.
Proof.
  intros (H1 & H2). destruct M as [ty rcv non enc]; cbn [cm_nonce cm_enc] in *.
  unfold cm_of, cookie_msg_bytes; cbn [cm_type cm_receiver cm_nonce cm_enc].
  assert (L4: forall v, Zlength (le32 v) = 4) by reflexivity.
  pose proof (L4 ty) as Lty. pose proof (L4 rcv) as Lrc.
  f_equal.
  - rewrite sublist_app1 by (try rewrite L4; lia). rewrite sublist_same by (try rewrite L4; lia).
    apply hrx5_B8CP_le32.
  - rewrite sublist_app2 by (try rewrite L4; lia). rewrite L4. simpl Z.sub.
    rewrite sublist_app1 by (try rewrite L4; lia). rewrite sublist_same by (try rewrite L4; lia).
    apply hrx5_B8CP_le32.
  - list_solve.
  - list_solve.
Qed.

Lemma hrx5_B8CP_tw M : hrx5_tw (cookie_msg_bytes M) = cm_type M.
Proof.
  unfold hrx5_tw, cookie_msg_bytes. rewrite sublist_app1 by (cbn; list_solve).
  rewrite sublist_same by reflexivity. apply hrx5_B8CP_le32.
Qed.

Lemma hrx5_B8CP_fwd_type M : cm_ok M -> hrx5_fwd (cookie_msg_bytes M) = true -> cm_type M = Int.repr 3.
Proof.
  intros Hok. unfold hrx5_fwd. rewrite hrx5_B8CP_len, hrx5_B8CP_tw by exact Hok.
  cbn [Z.leb Z.eqb Pos.eqb Z.compare Pos.compare Pos.compare_cont andb orb].
  rewrite !andb_false_r, andb_true_r. cbn [orb].
  intros H. pose proof (Int.eq_spec (cm_type M) (Int.repr 3)) as E. rewrite H in E. exact E.
Qed.

Lemma hrx5_B8CP_path_fwd W q s msg d : hrx5_path W q s msg d = 1 -> hrx5_fwd msg = true.
Proof. unfold hrx5_path. destruct (hrx5_fwd msg); [auto | discriminate]. Qed.

Lemma hrx5_B8CP_sfind_in {A} (l: list (val * share * A)) a sh v : sfind l a = Some (sh, v) -> In (a, sh, v) l.
Proof.
  induction l as [| [[x shx] vx] l IH]; cbn; [discriminate |]. intros H.
  destruct (EqDec_val x a) as [E | E]; [inversion H; subst; left; reflexivity | right; exact (IH H)].
Qed.

Section Model.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hrx5_B8CP_tgt T PS M a P pt :
  hrx5ck_tgt xaead_dec T PS M = Some (a, P, pt) ->
  (exists sh, sfind PS a = Some (sh, P)) /\ (exists k n ad, xaead_dec k n ad (cm_enc M) = Some pt).
Proof.
  unfold hrx5ck_tgt. destruct (t_find_index T (t_L T) (cm_receiver M)) as [[a0 E]|]; [| discriminate].
  destruct (Int.eq _ Int.zero); [discriminate |].
  destruct (sfind PS (e_peer E)) as [[sh P0]|] eqn:Hf; [| discriminate].
  destruct (ck_sent (p_cookie P0)); [| discriminate].
  destruct (xaead_dec _ _ _ _) as [pt0|] eqn:Hd; [| discriminate].
  intros H; inversion H; subst. split; [exists sh; exact Hf | eauto].
Qed.

Lemma hrx5_B8CP_model D T PS S w kc lul q sp s M d a P pt :
  cm_ok M -> hrx5_fwd (cookie_msg_bytes M) = true -> hrx5ck_tgt xaead_dec T PS M = Some (a, P, pt) ->
  rx_model x25519 aead_dec xaead_enc xaead_dec (hrx5_W0 D T PS S w kc lul) q sp s (cookie_msg_bytes M) d =
  mkRW D T (supd PS a (hrx5ck_new P pt (s_boot S))) [] S w kc lul rx0.
Proof.
  intros Hok Hfwd Ht.
  unfold rx_model. rewrite Hfwd. unfold rx_packet.
  rewrite hrx5_B8CP_tw, (hrx5_B8CP_fwd_type M Hok Hfwd), Int.eq_true.
  cbn [rw_D rw_S rw_lul rw_T rw_PS rw_KS rw_w rw_kc rw_rx hrx5_W0].
  rewrite hrx5_B8CP_cm_of by exact Hok.
  unfold mcons_res. rewrite hrx5ck_agree, Ht. reflexivity.
Qed.

(* branch C's case analysis of the harness's model block *)
Lemma hrx5_B8CP_case R NS PS T o now tg ai ar :
  hrx5_acc_ok x25519 aead_dec xaead_dec R NS PS T o now tg ai ar -> obj_kind o = 3 -> tg <> nullval ->
  hrx5_fwd (obj_bytes o) = true ->
  exists M a P pt, o = OCookie M /\ ai = 0 /\ ar = 0 /\ tg = hrx5_nfind NS a /\
    hrx5ck_tgt xaead_dec T PS M = Some (a, P, pt).
Proof.
  intros Hacc Hk Htg Hf. destruct o as [b|M|M|M]; cbn [obj_kind] in Hk; try discriminate.
  unfold hrx5_acc_ok in Hacc. rewrite Hf in Hacc. destruct Hacc as (Hai & Har & Htg').
  destruct (hrx5ck_tgt _ _ _ _) as [[[a P] pt]|] eqn:Ht.
  - exists M, a, P, pt. auto.
  - contradiction.
Qed.

End Model.

Local Open Scope logic.

Lemma hrx5_B8C_entry_ok : hrx5_B8C_entry_stmt.
Proof.
  intros x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul
    q proto ip4 ip6 port o dp img tg ai ar d HY (Hpath & Hk & Htg).
  unfold hrx5_B8_path in Hpath.
  pose proof (hrx5_B8CP_path_fwd _ _ _ _ _ Hpath) as Hfwd.
  unfold hrx5_B8_Q.
  match goal with |- ENTAIL _, ?P |-- _ => let P' := eval cbv zeta in P in change P with P' end.
  rewrite Hpath.
  Intros.
  match goal with H: hrx5_acc_ok _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    destruct (hrx5_B8CP_case x25519 aead_dec xaead_dec _ _ _ _ _ _ _ _ _ H Hk Htg Hfwd)
      as (M & a & P & pt & -> & -> & -> & -> & Ht) end.
  cbn [obj_bytes obj_ok obj_rep hrx5_ptrs obj_kind] in *.
  rewrite (hrx5_B8CP_model x25519 aead_dec xaead_enc xaead_dec _ T PS S w kc lul q _ _ M d a P pt)
    by assumption.
  cbn [rw_D rw_T rw_PS rw_KS rw_S rw_w rw_kc rw_lul rw_rx].
  unfold hrx5_scr5, hrx5_ci_rep, hrx5_st_rep, hrx5_pt_rep. cbv beta iota. cbn [obj_bytes].
  rewrite Hfwd, Ht.
  destruct (hrx5_B8CP_tgt xaead_dec T PS M a P pt Ht) as [[sh Hsf] (k & n & ad & Hd)].
  assert (Hlpt: Zlength pt = 16).
  { destruct HY as (_ & _ & HXA). apply (xaead_dec_length _ _ HXA) in Hd.
    match goal with H: cm_ok M |- _ => destruct H as [_ Le] end. rewrite Le in Hd. lia. }
  assert (Hsh: sh = Ews).
  { match goal with H: hrx5_inv _ _ _ _ _ _ _ _ _ |- _ => destruct H as (HF & _) end.
    rewrite Forall_forall in HF. specialize (HF _ (hrx5_B8CP_sfind_in _ _ _ _ Hsf)).
    destruct HF as (Hs & _). exact Hs. }
  subst sh.
  Exists M a P pt.
  unfold hrx5_B8C_QC0, hrx5_B8C_props, hrx5_B8C_temps, hrx5_B8C_sep, hrx5_B8C_world, hrx5_B8C_scr, rxw_rep.
  cbn [app keypairs_rep iter_sepcon rw_D rw_T rw_PS rw_KS rw_S rw_w rw_kc rw_lul rw_rx].
  change (d_itab (hrx5_DL x25519 R L sec birth)) with (l_itd L).
  change (d_ptab (hrx5_DL x25519 R L sec birth)) with (l_ptd L).
  rewrite sepcon_emp. repeat flatten_sepcon_in_SEP.
  unfold hrx5_lvars, hrx5_rest, hrx5_cglobs, hrx5_ptrs. cbn [app].
  entailer!.
Qed.
