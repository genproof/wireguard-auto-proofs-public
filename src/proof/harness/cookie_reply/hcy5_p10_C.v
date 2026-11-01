(* law cookie_reply, phase P10, segment C:
   statement 59..61: kents_snap(kes); dev_take(&da, &wa); head0 = ita.head.
*)
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
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_cut.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_spec.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_defs.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p10_defs.
Require WgNoise.harness.x_cookie_reply.code.

#[local] Existing Instance W_cookie_reply.
Local Open Scope Z_scope.

#[local] Instance hcy5_p10_c_cceN : change_composite_env Noise.CS W_cookie_reply.
Proof. make_cs_preserve Noise.CS W_cookie_reply. Defined.
#[local] Instance hcy5_p10_c_cceK : change_composite_env CKS W_cookie_reply.
Proof. make_cs_preserve CKS W_cookie_reply. Defined.

Lemma hcy5_p10_c_devsnap_ sh p : @data_at_ W_cookie_reply sh t_devsnap p = @data_at_ CKS sh t_devsnap p.
Proof. symmetry. exact (f_equal (fun f => f p) (@data_at__change_composite CKS W_cookie_reply _ sh t_devsnap eq_refl)). Qed.

Lemma hcy5_p10_c_ptrs PS : peers_rep PS |-- !! Forall (fun x => isptr (peer_addr4 x)) PS.
Proof.
  induction PS as [| [[a sh] P] PS IH]; unfold peers_rep in *; simpl.
  - entailer!.
  - sep_apply IH. unfold peer_item_rep at 1, peer_rep. entailer!.
    constructor; [cbn; destruct H0; assumption | assumption].
Qed.

Lemma hcy5_p10_c_kptrs l KE : kents_rep W l KE |-- !! Forall (fun e => isptr (ke_addr e)) KE.
Proof.
  revert l; induction KE as [| e KE IH]; intros l; cbn [kents_rep].
  - entailer!.
  - Intros nx. sep_apply (IH nx). unfold kent_cell. entailer!.
    constructor; [| assumption].
    match goal with X: field_compatible t_kent [] (ke_addr e) |- _ => destruct X; assumption end.
Qed.

Lemma hcy5_p10_c_itab_W sh (v: val) p :
  @data_at Noise.CS sh t_itab v p = @data_at W_cookie_reply sh t_itab v p.
Proof.
  rewrite (@data_at_change_composite Noise.CS W_cookie_reply _ sh t_itab v v (JMeq_refl v));
    [reflexivity | prove_cs_preserve_type].
Qed.

Lemma hcy5_p10_c_itable_open sht tab T :
  itable sht tab T = (!! itable_wf T &&
    (@data_at W_cookie_reply sht t_itab (hd nullval (t_L T)) tab *
     iter_sepcon (pool_item_rep (t_L T)) (t_D T)))%logic.
Proof. unfold itable. rewrite hcy5_p10_c_itab_W. reflexivity. Qed.

Lemma hcy5_p10_c_itable_fold sht tab T : itable_wf T ->
  (@data_at W_cookie_reply sht t_itab (hd nullval (t_L T)) tab *
   iter_sepcon (pool_item_rep (t_L T)) (t_D T) |-- itable sht tab T)%logic.
Proof. intros HT. rewrite hcy5_p10_c_itable_open. entailer!. Qed.

Lemma hcy5_p10_c_pa PS x : Forall (fun x => isptr (peer_addr4 x)) PS -> In x (map peer_addr4 PS) -> isptr x.
Proof.
  intros Hp Hx. apply in_map_iff in Hx. destruct Hx as (y & <- & Hy). rewrite Forall_forall in Hp. exact (Hp _ Hy).
Qed.

(* every entry of the pool has a peer that is a pointer *)
Lemma hcy5_p10_c_pool_peer PS KE T a sh E :
  hcy5_T_ok PS KE T -> Forall (fun x => isptr (peer_addr4 x)) PS -> In (a, sh, E) (t_D T) -> isptr (e_peer E).
Proof.
  intros ((own & ix & HD & Hown) & _) Hptr Hin. rewrite HD in Hin. apply in_app_or in Hin.
  destruct Hin as [Hin | Hin]; apply in_map_iff in Hin; destruct Hin as (k & Hk & Hk').
  - unfold hcy5_kentry in Hk. inversion Hk; subst. cbn.
    rewrite Forall_forall in Hown. apply (hcy5_p10_c_pa PS); [exact Hptr | exact (Hown _ Hk')].
  - unfold hcy5_hent in Hk. inversion Hk; subst. cbn. apply (hcy5_p10_c_pa PS); assumption.
Qed.

Lemma hcy5_p10_c_ksnap_pre PS KE T :
  hcy5_T_ok PS KE T -> Forall (fun x => isptr (peer_addr4 x)) PS ->
  Forall (fun e => In (ke_addr e) (saddrs (t_D T)) /\ e_peer (t_entry_d T (ke_addr e)) <> Vundef) KE.
Proof.
  intros HT Hptr. pose proof HT as ((own & ix & HD & Hown) & _). rewrite Forall_forall. intros e He.
  assert (Hin: In (ke_addr e) (saddrs (t_D T))).
  { rewrite HD. apply (prot_rep3_saddrs_in _ _ Ews (mkEntry (own (ke_addr e)) IDX_KEYPAIR (ix (ke_addr e)))).
    apply in_or_app. left. apply (in_map (hcy5_kentry own ix)), in_map, He. }
  split; [exact Hin|].
  destruct (prot_rep3_sfind_in (t_D T) (ke_addr e) Hin) as (sh & E & HE).
  unfold t_entry_d, t_entry. rewrite HE. apply prot_rep3_sfind_In in HE.
  pose proof (hcy5_p10_c_pool_peer PS KE T _ _ _ HT Hptr HE) as Hp.
  destruct (e_peer E); try contradiction; discriminate.
Qed.

Lemma hcy5_p10_c_hd_pn PS KE T : itable_wf T -> hcy5_T_ok PS KE T ->
  Forall (fun x => isptr (peer_addr4 x)) PS -> Forall (fun e => isptr (ke_addr e)) KE ->
  is_pointer_or_null (hd nullval (t_L T)).
Proof.
  intros (_ & Hinc & _) ((own & ix & HD & _) & _) Hp Hk. destruct (t_L T) as [| v l] eqn:E; cbn; [reflexivity|].
  assert (Hv: In v (saddrs (t_D T))) by (apply Hinc; left; reflexivity).
  rewrite HD in Hv. unfold hcy5_pool, saddrs in Hv. rewrite map_app, !map_map in Hv.
  apply in_app_or in Hv. rewrite Forall_forall in Hk. destruct Hv as [Hv | Hv].
  - apply in_map_iff in Hv. destruct Hv as (e & <- & He). specialize (Hk _ He). cbn.
    destruct (ke_addr e); try contradiction; exact I.
  - apply in_map_iff in Hv. destruct Hv as (a & <- & Ha). cbn.
    rewrite Forall_forall in Hp. pose proof (Hp _ Ha) as Ha'. unfold hcy5_hent, hs_addr.
    destruct (peer_addr4 a); try contradiction; exact I.
Qed.

Lemma hcy5_p10_c_phead PS : Forall (fun x => isptr (peer_addr4 x)) PS -> hcy5_phead PS <> Vundef.
Proof.
  destruct PS as [| [[a sh] P] PS]; cbn; intros Hp; [discriminate|].
  inversion Hp; subst. cbn in *. destruct a; try contradiction; discriminate.
Qed.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hcy5_p10_C_ok {Espec: OracleKind} gv L FR :
  hcy5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hcy5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hcy5_p10_TB x25519 xaead_enc gv L FR) hcy5_p10_sC
    (overridePost (hcy5_p10_TC x25519 xaead_enc gv L FR) (hcy5_R gv)).
Proof.
  intros HH. unfold hcy5_p10_TB, hcy5_Delta, hcy5_R, hcy5_p10_sC. simplify_func_tycontext. abbreviate_semax.
  Intros R S m c rp Q nonce rr CK CM NS PS.
  Intros T np CL KE CM' honest.
  unfold hcy5_aside, hcy5_snaps0, hcy5_lvars, hcy5_globs, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB; cbn [app].
  assert_PROP (Forall (fun x => isptr (peer_addr4 x)) PS) as Hptr by (sep_apply (hcy5_p10_c_ptrs PS); entailer!).
  assert_PROP (Forall (fun e => isptr (ke_addr e)) KE) as Hkp by (sep_apply (hcy5_p10_c_kptrs (hcy5_khead KE) KE); entailer!).
  assert_PROP (isptr (l_wa L) /\ isptr (l_pta L) /\ isptr (l_ita L)) as Hlv by entailer!.
  destruct Hlv as (Hwa & Hpt & Hit).
  forward_call (hcy5_khead KE, KE, Tsh, l_ita L, T).
  { apply (hcy5_p10_c_ksnap_pre PS KE T); assumption. }
  rewrite hcy5_p10_c_devsnap_.
  change (ptable Tsh (l_pta L) (hcy5_phead PS)) with (ptable Tsh (d_ptab (hcy5_DA x25519 R L)) (hcy5_phead PS)).
  forward_call (Tsh, l_da L, Tsh, l_wa L, hcy5_DA x25519 R L, Tsh, hcy5_phead PS).
  { pose proof (hcy5_p10_c_phead PS Hptr).
    unfold hcy5_DA, setup_dev; cbn.
    repeat constructor; try discriminate; auto; intro X; rewrite X in *; contradiction. }
  rewrite hcy5_p10_c_itable_open. Intros.
  match goal with X: hcy5_T_ok PS KE T |- _ => pose proof (hcy5_p10_c_hd_pn PS KE T ltac:(assumption) X Hptr Hkp) as Hhd end.
  forward.
  sep_apply (hcy5_p10_c_itable_fold Tsh (l_ita L) T ltac:(assumption)).
  unfold hcy5_p10_TC. Exists R S m c rp Q nonce rr CK CM NS PS.
  Exists T np CL KE CM' honest.
  unfold hcy5_aside, hcy5_lvars, hcy5_globs, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB; cbn [app].
  change (d_ptab (hcy5_DA x25519 R L)) with (l_pta L).
  entailer!.
Qed.

End Seg.
