(* law handshake_receive: B8 branch R segment D, part CHK of the node
   loop: CHECK(hs_same_but_next(&nd->snap, &nd->p->handshake) && nd->p->refcount.refcount == nd->refs &&
   pr_same(&nd->rest, nd->p)) at a node k <> j: the state does not change.  States: hrx5_B8_R_D_defs.v.
   Port of handshake_clear's
   hcl5_p7_chk. *)
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_D_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_D_chk_lem.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_D_chk_body.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

Section Seg.
Context {Espec: OracleKind}.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Variables (gv: globals) (L: hrx5_loc) (R: hrx5_run) (NS: list hnode4) (PS: list (val * share * peer))
  (KE: list kent4) (T: tstate) (head nk: val) (j: Z) (a tg: val) (Pf: peer) (Tf: tstate) (D: device) (FRM: mpred).
Variables (vh vs vallok vsess vnk vkes vsteps vi vnow vlul vbuf vmi vmr vmc vimg vlen vkind vai var vhead0
           vpath: val).

Lemma hrx5_B8RD_chk_ok (Rp: ret_assert) (k: Z) (nx q: val) (Q: peer) :
  hrx5_B8RD_hyp x25519 L R NS PS KE T head nk j a tg Tf ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec)
    (hrx5_B8RD_Q0 gv L NS PS T j a tg Pf Tf D FRM vh vs vallok vsess vnk vkes vsteps vi vnow vlul vbuf vmi vmr vmc
       vimg vlen vkind vai var vhead0 vpath k nx q Q)
    hrx5_B8RD_chk
    (overridePost (hrx5_B8RD_Q0 gv L NS PS T j a tg Pf Tf D FRM vh vs vallok vsess vnk vkes vsteps vi vnow vlul vbuf
       vmi vmr vmc vimg vlen vkind vai var vhead0 vpath k nx q Q) Rp).
Proof.
  intros HH. destruct HH as (Hinv & Hj & Hhj & Htg & Hndn & HTf).
  unfold hrx5_B8RD_Q0 at 1. unfold hrx5_B8RD_Q at 1. cbn [app].
  Intros.
  pose proof Hinv as Hinv0. destruct Hinv as (Hpok & Hwf & Hndp & Hch & Hnp & Hnk & Hpool).
  match goal with H: Znth k PS = (q, Ews, Q) |- _ => rename H into EK end.
  match goal with H: k <> j |- _ => rename H into Hkj end.
  match goal with H: 0 <= k < Zlength NS |- _ => rename H into Hk end.
  pose proof (hrx5_B8RDc_len_peers _ _ Hnp) as HL.
  assert (Hpq: hrx5_pok x25519 R L (q, Ews, Q)) by (rewrite <- EK; apply Forall_Znth; first [exact Hpok | lia]).
  destruct Hpq as (_ & Hdev & Hsid & _ & _ & _ & _ & _ & Hcur & Hprev & Hnext).
  pose proof (Znth_In k PS ltac:(lia)) as HinQ. rewrite EK in HinQ.
  assert (Ha: a = peer_addr4 (Znth j PS)) by (rewrite <- Hhj; apply hrx5_B8RDc_hn_p; auto).
  set (C := upd_Znth j PS (a, Ews, Pf)).
  set (others := sublist 0 k C ++ sublist (k + 1) (Zlength C) C).
  assert (Hpkn: p_pknext Q = nullval \/ In (p_pknext Q) (map peer_addr4 others)).
  { subst others C. rewrite hrx5_B8RDc_others_addrs by (auto; lia).
    exact (hrx5_B8RDc_pknext head PS k q Ews Q Hch ltac:(lia) EK). }
  assert (Hoth: Forall (fun y => match y with (_, sh, _) => sh = Ews end) others).
  { subst others C. apply hrx5_B8RDc_others_sh; [lia|].
    eapply Forall_impl; [|exact Hpok]. intros [[b sh] Q'] Hq. exact (proj1 Hq). }
  assert (EC: Znth k C = (q, Ews, Q)) by (subst C; rewrite hrx5_B8RDc_upd_nth by lia; exact EK).
  assert (HLC: Zlength C = Zlength PS) by (subst C; apply hrx5_B8RDc_upd_len; lia).
  unfold hrx5_B8RD_fix. cbn [app].
  assert_PROP (NoDup (saddrs (t_D Tf))) as Hndf.
  { unfold itable. Intros. match goal with Hw: itable_wf _ |- _ => destruct Hw as (_ & _ & Hw0 & _) end.
    apply prop_right. exact Hw0. }
  assert (Hnd: NoDup (saddrs (t_D T))) by (rewrite <- (hrx5_B8RDc_tD T Tf (hs_addr a) HTf); exact Hndf).
  destruct (hrx5_B8RDc_pool_hs _ _ _ q Ews Q Hpool Hnd HinQ) as (HinT & HepT).
  assert (Hin: In (hs_addr q) (saddrs (t_D Tf))) by (rewrite (hrx5_B8RDc_tD T Tf (hs_addr a) HTf); exact HinT).
  assert (Hepf: e_peer (t_entry_d Tf (hs_addr q)) = q) by (rewrite (hrx5_B8RDc_entry_d T Tf (hs_addr a)) by exact HTf; exact HepT).
  assert (Hne: hs_addr q <> hs_addr a).
  { rewrite Ha. replace q with (peer_addr4 (Znth k PS)) by (rewrite EK; reflexivity).
    apply (hrx5_B8RDc_ne _ PS T j k Hpool Hnd); lia. }
  pose proof (hrx5_B8RDc_snapf T Tf (hs_addr a) q Q HTf Hne) as Hsnap.
  rewrite (hrx5_B8RDc_peers_at k C) by lia. fold others. rewrite EC. cbn [peer_item_rep].
  set (FRM' := (@data_at W_handshake_receive Tsh (tptr t_hnode4) (hrx5_head (hnodes_snapped4 T NS PS)) (l_peers L) *
               FRM *
               hrx5_B8RD_seg (hrx5_head (hnodes_snapped4 T NS PS)) (hn_addr (Znth k NS))
                 (firstn (Z.to_nat k) (hnodes_snapped4 T NS PS)) *
               @malloc_token W_handshake_receive Ews t_hnode4 (hn_addr (Znth k NS)) *
               @malloc_token W_handshake_receive Ews t_peer q *
               hnodes_rep4 W_handshake_receive nx (skipn (Z.to_nat (k + 1)) (hnodes_snapped4 T NS PS)))%logic).
  apply semax_pre with (P' := hrx5_B8RDc_S gv L tg vh vs vallok vsess vnk vkes vsteps vi vnow vlul vbuf vmi vmr vmc
     vimg vlen vkind vai var vhead0 vpath (hn_addr (Znth k NS)) (hrx5_B8RD_nhk PS T a k) q Q T Tf nx D others FRM').
  { unfold hrx5_B8RDc_S, FRM'. go_lowerx.
    apply andp_right; [apply prop_right; repeat (split; [assumption|]); auto |]. cancel. }
  eapply semax_post; [| | | | apply (hrx5_B8RDc_body x25519 aead_dec xaead_enc xaead_dec gv L tg vh vs vallok vsess
     vnk vkes vsteps vi vnow vlul vbuf vmi vmr vmc vimg vlen vkind vai var vhead0 vpath (hn_addr (Znth k NS))
     (hrx5_B8RD_nhk PS T a k) q Q T Tf nx D others FRM' Rp); auto].
  2-4: unfold overridePost; destruct Rp as [Rn Rb Rc Rr]; simpl; try intros; apply andp_left2, derives_refl.
  unfold overridePost; destruct Rp as [Rn Rb Rc Rr]; simpl RA_normal.
  unfold hrx5_B8RDc_S, hrx5_B8RD_Q0, hrx5_B8RD_Q, hrx5_B8RD_fix, FRM'. cbn [app].
  change (peers_rep (upd_Znth j PS (a, Ews, Pf))) with (peers_rep C).
  rewrite (hrx5_B8RDc_peers_at k C) by lia. fold others. rewrite EC. cbn [peer_item_rep].
  go_lowerx.
  apply andp_right; [apply prop_right; repeat (split; [first [assumption | lia]|]); auto |].
  apply andp_right; [apply prop_right; repeat (split; [assumption|]); auto |]. cancel.
Qed.

End Seg.
