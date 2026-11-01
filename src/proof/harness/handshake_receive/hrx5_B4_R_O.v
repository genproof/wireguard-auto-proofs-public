(* law handshake_receive, B4 segment R, part O: statement 25 for OResp M from the core (hrx5_B4_R_core_stmt): hrx5_B4_Q -> hrx5_S4.
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
#[local] Existing Instance W_handshake_receive.
#[local] Existing Instance W_handshake_receive.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_R_pure.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_R_sep.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_R_defs.
Local Open Scope logic.

Ltac hrx5_B4_R_O_ent :=
  cbv beta iota delta [loop1_ret_assert overridePost hrx5_R frame_ret_assert function_body_ret_assert
                       RA_break RA_normal]; entailer!.
Ltac hrx5_B4_R_O_absurd :=
  exfalso; first
  [ discriminate
  | match goal with H: ?x <> ?x |- _ => exact (H eq_refl) end
  | match goal with H: Int.repr 0 <> Int.zero |- _ => exact (H eq_refl) end
  | match goal with H: Int.one = Int.zero |- _ => exact (Int.one_not_zero H) end
  | match goal with H: Int.zero = Int.one |- _ => exact (Int.one_not_zero (eq_sym H)) end ].

Lemma hrx5_B4_R_O_st x25519 aead_dec R T PS M st : hrx5_fwd (resp_bytes M) = true ->
  hrx5_st_rep x25519 aead_dec R T PS (OResp M) st = hrx5_B4_R_strep x25519 aead_dec (hrx5_ID x25519 R) T PS M st.
Proof. intros Hf. unfold hrx5_st_rep, hrx5_B4_R_strep. cbn [obj_bytes]. rewrite Hf. reflexivity. Qed.

Lemma hrx5_B4_R_O_acc x25519 aead_dec xaead_dec R NS PS T M now tg ar : hrx5_fwd (resp_bytes M) = true ->
  hrx5_B4_R_acc x25519 aead_dec (hrx5_ID x25519 R) T PS M NS tg ar ->
  hrx5_acc_ok x25519 aead_dec xaead_dec R NS PS T (OResp M) now tg 0 ar.
Proof. intros Hf Ha. unfold hrx5_acc_ok, hrx5_B4_R_acc in *. cbn [obj_bytes]. rewrite Hf. auto. Qed.

(* the frame of the response branch: every SEP item of hrx5_B4_Q the branch does not read *)
Definition hrx5_B4_R_O_FXl x25519 gv L FR R sec birth S w PS T head KE kc lul q proto ip4 ip6 port M dp img
  : list mpred :=
  [device_rep Tsh (l_wd L) (hrx5_DL x25519 R L sec birth); ptable Tsh (l_ptd L) head; peers_rep PS;
   @data_at HCS Tsh t_mident (mident_val (hrx5_IK x25519 R)) (l_ik L);
   hbytes Tsh (rr_rawd R) (l_rawd L); hbytes Tsh (rr_rawk R) (l_rawk L);
   hbytes Tsh (hrx5_mk1 x25519 R) (l_mk1 L); hbytes Tsh (hrx5_ssk x25519 R) (l_ssk L);
   kents_rep W (hrx5_khead (map (kent_snapped T) KE)) (map (kent_snapped T) KE);
   mem_mgr gv; shim_state4 gv S w; noise_globals gv kc; hrx5_consts gv; FR;
   lul_rep gv lul; @data_at_ HRX Ews t_rxlog (gv HM._wg_shim_rx); qlen_rep gv q;
   skb_rep Tsh (l_skb L) (hrx5_skb dp (OResp M) proto ip4 ip6 port);
   @malloc_token W Ews t_resp dp; img_rep img (resp_bytes M);
   hout Tsh 32 (l_pub L); @data_at_ CKS Tsh t_devsnap (l_ds L); @data_at_ CKS Tsh t_shimsnap (l_ss L);
   @data_at_ CKS Tsh t_skbsnap (l_sks L); @data_at_ HCS Tsh t_mcinit (l_ci L);
   hout Tsh 32 (l_secret L); hout Tsh 16 (l_c L); hout Tsh 16 (l_mac L); hout Tsh 16 (l_pt L);
   @data_at_ Noise.CS Tsh t_init (l_t L); @data_at_ Noise.CS Tsh t_resp (l_t1 L); hout Tsh 16 (l_ck L);
   hout Tsh 32 (l_sst L)].

Lemma hrx5_B4_R_O_ok : hrx5_B4_R_O_stmt.
Proof.
  unfold hrx5_B4_R_O_stmt.
  intros Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q
    proto ip4 ip6 port M dp img HH Hcore.
  rewrite hrx5_B4_R_M_eq, hrx5_B4_R_else_eq.
  unfold hrx5_B4_Q, hrx5_Delta, hrx5_RB, hrx5_B4_R_c97, hrx5_B4_R_e97, hrx5_B4_R_c94, hrx5_B4_R_e94, hrx5_B4_R_CK,
    hrx5_ltemps, hrx5_ptrs, hrx5_lvars.
  cbn [app obj_bytes obj_kind obj_ok]. simplify_func_tycontext. abbreviate_semax.
  Intros.
  unfold hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr; cbn [app].
  destruct (hrx5_fwd (resp_bytes M)) eqn:Hfw.
  all: forward_if (temp HM._t'95 (Vint Int.zero)); [ forward; hrx5_B4_R_O_ent | forward; hrx5_B4_R_O_ent | ].
  all: forward_if (temp HM._t'96 (Vint Int.zero)); [ hrx5_B4_R_O_absurd | forward; hrx5_B4_R_O_ent | ].
  all: forward_if (temp HM._t'97 (Vint Int.zero)); [ hrx5_B4_R_O_absurd | forward; hrx5_B4_R_O_ent | ].
  all: forward_if; [ hrx5_B4_R_O_absurd | ].
  2: { (* not fwd: nothing *)
    forward_if (temp HM._t'93 (Vint Int.zero)); [ hrx5_B4_R_O_absurd | forward; hrx5_B4_R_O_ent | ].
    forward_if (temp HM._t'94 (Vint Int.zero)); [ hrx5_B4_R_O_absurd | forward; hrx5_B4_R_O_ent | ].
    forward_if; [ hrx5_B4_R_O_absurd | ].
    forward_if (temp HM._t'92 (Vint Int.zero)); [ hrx5_B4_R_O_absurd | forward; hrx5_B4_R_O_ent | ].
    forward_if; [ hrx5_B4_R_O_absurd | ].
    forward.
    match goal with |- _ |-- RA_normal ?X => change (RA_normal X) with (hrx5_S4 x25519 aead_dec xaead_dec gv L FR) end.
    unfold hrx5_S4.
    Exists R sec birth S w NS PS T.
    Exists head nk KE st i kc lul q.
    Exists proto ip4 ip6 port (OResp M) dp img nullval.
    Exists 0 0.
    unfold hrx5_scr4, hrx5_ci_rep, hrx5_st_rep, hrx5_pt_rep, hrx5_ltemps, hrx5_ptrs, hrx5_lvars, hrx5_wcore, hrx5_rest,
      hrx5_globs.
    cbn [app obj_bytes obj_kind].
    assert (Hacc: hrx5_acc_ok x25519 aead_dec xaead_dec R NS PS T (OResp M) (s_boot S) nullval 0 0).
    { unfold hrx5_acc_ok. cbn [obj_bytes]. rewrite Hfw. auto. }
    rewrite Hfw. entailer!. }
  forward_if (temp HM._t'93 (Vint Int.one)); [ forward; hrx5_B4_R_O_ent | hrx5_B4_R_O_absurd | ].
  destruct (mi_ok (hrx5_ID x25519 R)) eqn:Hok.
  2: { (* no identity: nothing *)
    forward_if (temp HM._t'94 (Vint Int.zero));
      [ rewrite (hrx5_B4_R_mident_cs Tsh (hrx5_ID x25519 R)); forward; forward; rewrite <- hrx5_B4_R_mident_cs;
        rewrite Hok; hrx5_B4_R_O_ent | hrx5_B4_R_O_absurd | ].
    forward_if; [ hrx5_B4_R_O_absurd | ].
    forward_if (temp HM._t'92 (Vint Int.zero)); [ forward; hrx5_B4_R_O_ent | hrx5_B4_R_O_absurd | ].
    forward_if; [ hrx5_B4_R_O_absurd | ].
    forward.
    match goal with |- _ |-- RA_normal ?X => change (RA_normal X) with (hrx5_S4 x25519 aead_dec xaead_dec gv L FR) end.
    unfold hrx5_S4.
    Exists R sec birth S w NS PS T.
    Exists head nk KE st i kc lul q.
    Exists proto ip4 ip6 port (OResp M) dp img nullval.
    Exists 0 0.
    unfold hrx5_scr4, hrx5_ci_rep, hrx5_st_rep, hrx5_pt_rep, hrx5_ltemps, hrx5_ptrs, hrx5_lvars, hrx5_wcore, hrx5_rest,
      hrx5_globs.
    cbn [app obj_bytes obj_kind].
    assert (Htg: hrx5cr_tgt x25519 aead_dec (hrx5_ID x25519 R) T PS M = None).
    { unfold hrx5cr_tgt. rewrite Hok. reflexivity. }
    assert (Hacc: hrx5_acc_ok x25519 aead_dec xaead_dec R NS PS T (OResp M) (s_boot S) nullval 0 0).
    { unfold hrx5_acc_ok. cbn [obj_bytes]. rewrite Hfw, Htg. auto. }
    rewrite Hfw, Htg. entailer!. }
  forward_if (temp HM._t'94 (Vint Int.one));
    [ rewrite (hrx5_B4_R_mident_cs Tsh (hrx5_ID x25519 R)); forward; forward; rewrite <- hrx5_B4_R_mident_cs;
      rewrite Hok; hrx5_B4_R_O_ent | hrx5_B4_R_O_absurd | ].
  forward_if; [ | hrx5_B4_R_O_absurd ].
  (* the facts of the core *)
  destruct hrx5_B4_R_sep_ok as (_ & _ & _ & Sptrs & _ & _ & _ & _ & Sfc).
  destruct hrx5_B4_R_pure_ok as (_ & _ & _ & _ & _ & Psnap & _).
  pose proof H0 as (Hpok & _ & HndP & _ & Hhp & _ & Hpool).
  destruct (Psnap T NS PS Hhp) as (_ & _ & Hhead).
  assert (HlIA: Zlength (mi_priv (hrx5_ID x25519 R)) = 32).
  { unfold hrx5_ID, mident_of. cbn [mi_priv]. apply hrx5_B4_R_clamp_len. destruct H as ((? & _) & _). assumption. }
  assert (HhsP: Forall (fun x => match x with (_, _, P) => hs_ok (p_hs P) end) PS).
  { rewrite Forall_forall in Hpok |- *. intros [[a sh] P] Hin. destruct (Hpok _ Hin) as (_ & _ & _ & Hok' & _). exact Hok'. }
  assert_PROP (itable_wf T) as Hwf. { unfold itable. entailer!. }
  assert_PROP (Forall isptr (saddrs (t_D T))) as Hptr.
  { unfold itable. Intros. sep_apply (hrx5_B4_R_ptrs (t_L T) (t_D T)). entailer!. }
  assert_PROP (Forall (fun x => @field_compatible W t_peer [] (peer_addr4 x)) PS) as Hfc0.
  { sep_apply (Sfc PS). entailer!. }
  assert_PROP (Forall isptr (map hn_addr (hnodes_snapped4 T NS PS))) as HptrN.
  { sep_apply (Sptrs (hrx5_head (hnodes_snapped4 T NS PS)) (hnodes_snapped4 T NS PS)). entailer!. }
  pose proof (Hcore Espec x25519 aead_dec xaead_enc xaead_dec gv L nk KE st i S lul dp img (Zlength (resp_bytes M))
    (if 4 <=? Zlength (resp_bytes M) then hrx5_tw (resp_bytes M) else Int.zero)
    (hrx5_ID x25519 R) (map ke_addr KE) NS PS T M
    (fold_right_sepcon (hrx5_B4_R_O_FXl x25519 gv L FR R sec birth S w PS T head KE kc lul q proto ip4 ip6 port M dp img))
    (hrx5_RB x25519 gv L FR) Hok HlIA Hwf Hptr Hpool Hhp HndP HhsP Hfc0 HptrN) as HC.
  unfold hrx5_RB in HC.
  eapply semax_pre; [ | eapply hrx5_B4_R_post; [ | exact HC ] ].
  - unfold hrx5_B4_R_A0, hrx5_B4_R_R, hrx5_B4_R_Q, hrx5_ltemps, hrx5_lvars. rewrite hrx5_B4_R_sepx.
    unfold hrx5_B4_R_O_FXl. cbn [app]. rewrite Hhead. unfold obj_rep. entailer!.
  - unfold hrx5_B4_R_OUT. Intros tg ar.
    unfold hrx5_S4.
    Exists R sec birth S w NS PS T.
    Exists head nk KE st i kc lul q.
    Exists proto ip4 ip6 port (OResp M) dp img tg.
    Exists 0 ar.
    unfold hrx5_B4_R_R, hrx5_B4_R_Q, hrx5_scr4, hrx5_ci_rep, hrx5_pt_rep, hrx5_ltemps, hrx5_ptrs, hrx5_lvars, hrx5_wcore,
      hrx5_rest, hrx5_globs.
    cbn [app obj_bytes obj_kind]. rewrite hrx5_B4_R_O_st by exact Hfw. rewrite hrx5_B4_R_sepx.
    unfold hrx5_B4_R_O_FXl. cbn [app]. rewrite Hhead, Hfw.
    assert (Hacc: hrx5_acc_ok x25519 aead_dec xaead_dec R NS PS T (OResp M) (s_boot S) tg 0 ar)
      by (apply hrx5_B4_R_O_acc; assumption).
    unfold obj_rep. entailer!.
Qed.
