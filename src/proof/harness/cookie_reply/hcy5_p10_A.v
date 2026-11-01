(* law cookie_reply, phase P10, segment A:
   statement 57: hnodes_snap(peers).
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

(* the pool's entries: their peers are peers of PS *)
Lemma hcy5_p10_a_pool_peer PS KE T a sh E :
  hcy5_T_ok PS KE T -> In (a, sh, E) (t_D T) -> In (e_peer E) (map peer_addr4 PS).
Proof.
  intros ((own & ix & HD & Hown) & _) Hin. rewrite HD in Hin. unfold hcy5_pool in Hin.
  apply in_app_or in Hin. destruct Hin as [Hin | Hin]; apply in_map_iff in Hin; destruct Hin as (x & Hx & Hin).
  - unfold hcy5_kentry in Hx. inv Hx. cbn [e_peer]. rewrite Forall_forall in Hown. apply Hown. exact Hin.
  - unfold hcy5_hent in Hx. inv Hx. cbn [e_peer]. exact Hin.
Qed.

(* every peer's handshake entry is in the pool *)
Lemma hcy5_p10_a_pool_hs PS KE T a :
  hcy5_T_ok PS KE T -> In a (map peer_addr4 PS) -> In (hs_addr a) (saddrs (t_D T)).
Proof.
  intros ((own & ix & HD & _) & _) Hin. rewrite HD. unfold hcy5_pool, saddrs.
  rewrite map_app. apply in_or_app. right. rewrite map_map. apply in_map_iff. exists a. split; auto.
Qed.

Lemma hcy5_p10_a_sfind_in (D: list (val * share * entry)) a :
  In a (saddrs D) -> exists sh E, sfind D a = Some (sh, E) /\ In (a, sh, E) D.
Proof.
  intros Hin. destruct (prot_rep3_sfind_in D a Hin) as (sh & E & HE).
  exists sh, E. split; [exact HE | exact (prot_rep3_sfind_In _ _ _ _ HE)].
Qed.

(* an address of the pool: its entry's peer is a peer of PS *)
Lemma hcy5_p10_a_entry_peer PS KE T a :
  hcy5_T_ok PS KE T -> In a (saddrs (t_D T)) -> In (e_peer (t_entry_d T a)) (map peer_addr4 PS).
Proof.
  intros HT Hin. destruct (hcy5_p10_a_sfind_in (t_D T) a Hin) as (sh & E & H1 & H2).
  unfold t_entry_d, t_entry. rewrite H1. eapply hcy5_p10_a_pool_peer; eauto.
Qed.

Lemma hcy5_p10_a_peers_ptr PS : peers_rep PS |-- !! Forall (fun x => isptr (peer_addr4 x)) PS.
Proof.
  unfold peers_rep. induction PS as [| [[a sh] P] PS IH]; simpl.
  - entailer!.
  - sep_apply IH. unfold peer_rep. entailer!. constructor; auto. destruct H0 as [Hp _]. exact Hp.
Qed.

Lemma hcy5_p10_a_kents_ptr l KE : kents_rep W_cookie_reply l KE |-- !! Forall isptr (map ke_addr KE).
Proof.
  revert l. induction KE as [| e KE IH]; intros l; simpl.
  - entailer!.
  - Intros nx. sep_apply (IH nx). unfold kent_cell. entailer!. constructor; auto.
    destruct H1 as [Hp _]. exact Hp.
Qed.

Lemma hcy5_p10_a_pn l NS : hnodes_rep4 W_cookie_reply l NS |-- !! is_pointer_or_null l.
Proof.
  destruct NS as [| N NS]; simpl.
  - Intros. subst. entailer!.
  - Intros nx. subst. entailer!. destruct H0 as [Hp _]. destruct (hn_addr N); simpl in *; try contradiction; auto.
Qed.

Lemma hcy5_p10_a_head T NS PS : length NS = length PS -> hcy5_head (hnodes_snapped4 T NS PS) = hcy5_head NS.
Proof.
  intros Hl. destruct NS as [| N NS]; [reflexivity |]. destruct PS as [| [[p sh] P] PS]; [discriminate |].
  reflexivity.
Qed.

(* the pubkey_next fields along the chain are peers or NULL *)
Lemma hcy5_p10_a_pknext h PS :
  pk_chain h PS -> Forall (fun x => isptr (peer_addr4 x)) PS ->
  Forall (fun x => match x with (_, _, P) => p_pknext P <> Vundef end) PS.
Proof.
  revert h. induction PS as [| [[a sh] P] PS IH]; intros h Hc Hp; constructor.
  - destruct Hc as [_ Hc]. inv Hp. destruct PS as [| [[b sh'] P'] PS'].
    + cbn in Hc. rewrite Hc. discriminate.
    + destruct Hc as [-> _]. inv H2. cbn in H1. destruct b; try contradiction. discriminate.
  - destruct Hc as [_ Hc]. inv Hp. eapply IH; eauto.
Qed.

(* the precondition of hnodes_snap on the peers *)
Lemma hcy5_p10_a_pre L KE NS PS T :
  hcy5_lists_ok L (map ke_addr KE) NS PS -> hcy5_T_ok PS KE T -> isptr (l_wa L) ->
  Forall (fun x => isptr (peer_addr4 x)) PS -> Forall isptr (map ke_addr KE) ->
  Forall (fun x => match x with (p, _, P) =>
            In (hs_addr p) (saddrs (t_D T)) /\ e_peer (t_entry_d T (hs_addr p)) <> Vundef /\
            hs_sid (p_hs P) <> Vundef /\
            Forall (fun v => v <> Vundef) [p_device P; p_cur P; p_prev P; p_next P; p_pknext P] end) PS.
Proof.
  intros (Hpok & Hnp & _ & _ & Hpk) HT Hwa Hpp Hkp.
  pose proof (hcy5_p10_a_pknext _ _ Hpk Hpp) as Hpkn.
  apply Forall_forall. intros [[a sh] P] Hin.
  assert (Ha: In a (map peer_addr4 PS)) by (apply in_map_iff; exists (a, sh, P); auto).
  pose proof (hcy5_p10_a_pool_hs PS KE T a HT Ha) as Hs.
  rewrite Forall_forall in Hpok, Hpkn. specialize (Hpok _ Hin). specialize (Hpkn _ Hin). cbn in Hpkn.
  destruct Hpok as (_ & Hdev & Hsid & _ & _ & Hsl).
  assert (Hnu: forall v, v = nullval \/ In v (map ke_addr KE) -> v <> Vundef).
  { intros v [-> | Hv]; [discriminate |]. rewrite Forall_forall in Hkp. specialize (Hkp _ Hv).
    destruct v; try contradiction. discriminate. }
  inv Hsl. inv H2. inv H4.
  split; [exact Hs |]. split.
  { pose proof (hcy5_p10_a_entry_peer PS KE T _ HT Hs) as Hin'. apply in_map_iff in Hin'.
    destruct Hin' as (y & Hy & Hiny). rewrite Forall_forall in Hpp. specialize (Hpp y Hiny). rewrite Hy in Hpp.
    destruct (e_peer _); try contradiction. discriminate. }
  split.
  { rewrite Hsid. unfold id_addr. destruct (l_wa L); try contradiction. discriminate. }
  repeat constructor; auto.
  rewrite Hdev. destruct (l_wa L); try contradiction. discriminate.
Qed.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hcy5_p10_A_ok {Espec: OracleKind} gv L FR :
  hcy5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hcy5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hcy5_S9 x25519 xaead_enc gv L FR) hcy5_p10_sA
    (overridePost (hcy5_p10_TA x25519 xaead_enc gv L FR) (hcy5_R gv)).
Proof.
  intros HH. unfold hcy5_S9, hcy5_Delta, hcy5_R, hcy5_p10_sA. simplify_func_tycontext. abbreviate_semax.
  Intros R S m c rp Q nonce rr CK CM.
  Intros NS PS T np CL KE CM' honest.
  unfold hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_snaps0, hcy5_globs, hcy5_lvars; cbn [app].
  assert_PROP (is_pointer_or_null (hcy5_head NS)) as Hpn.
  { sep_apply (hcy5_p10_a_pn (hcy5_head NS) NS). entailer!. }
  assert_PROP (Forall (fun x => isptr (peer_addr4 x)) PS) as Hpp.
  { sep_apply (hcy5_p10_a_peers_ptr PS). entailer!. }
  assert_PROP (Forall isptr (map ke_addr KE)) as Hkp.
  { sep_apply (hcy5_p10_a_kents_ptr (hcy5_khead KE) KE). entailer!. }
  assert_PROP (isptr (l_wa L)) as Hwa.
  { unfold device_rep. entailer!. }
  forward.
  pose proof H0 as Hlists. destruct Hlists as (Hpok & Hnp & Hnd1 & Hnd2 & Hpk).
  forward_call (hcy5_head NS, NS, PS, Tsh, l_ita L, T).
  { split.
    - unfold peers_wf. eapply Forall_impl; [| exact Hpok]. intros [[a sh] P] Hp. destruct Hp as (-> & _). auto.
    - apply (hcy5_p10_a_pre L KE NS); auto. }
  unfold hcy5_p10_TA. Exists R S m c rp Q nonce rr CK CM. Exists NS PS T np CL KE CM' honest.
  unfold hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_snaps0, hcy5_globs, hcy5_lvars; cbn [app].
  rewrite hcy5_p10_a_head
    by (pose proof (f_equal (@length _) Hnp) as Hl; rewrite !length_map in Hl; exact Hl).
  entailer!.
Qed.

End Seg.
