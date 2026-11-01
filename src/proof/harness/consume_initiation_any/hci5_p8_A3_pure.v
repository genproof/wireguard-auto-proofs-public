(* law consume_initiation_any, phase P8, segment A3: the pure facts of the acceptance branch
   (from hci5_p8_QA1's PROPs; port of v1's hci3_p8_A3_pure.v).  The accepted peer at a (state P before the call)
   is in PS with share Ews (PS = PS1 ++ (a, Ews, P) :: PS2); its node in the snapshotted node list holds the
   handshake snapshot hs_snap_cur T a P (its entry and links from the table T: ANY), the reference count p_refs P
   and the rest prsnap_val P; the handshake's entry is in T's pool with peer a; the lengths of t, ck2, h2; the
   pointers pr_same compares are valid (device, slots, pubkey_next); pr_eqb P (hci5_p8_put ..) = true. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.blake2s.model.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_model.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_defs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p8_defs.

Local Open Scope Z_scope.

Lemma hci5_p8_A3_len_blake2s key m : Zlength (blake2s key 32 m) = 32.
Proof.
  unfold blake2s, b2s_digest_stream, b2s_out.
  rewrite Zlength_map, Zlength_correct, upto_length. reflexivity.
Qed.

Lemma hci5_p8_A3_len_hmac k d : Zlength (hmac k d) = 32.
Proof. unfold hmac, HASH. apply hci5_p8_A3_len_blake2s. Qed.

Lemma hci5_p8_A3_len2 aead_enc aead_dec SS CK H ENCT t ck h : aead_props aead_enc aead_dec ->
  Zlength ENCT = 28 -> m_consume_init2_model aead_dec SS CK H ENCT = Some (t, ck, h) ->
  Zlength t = 12 /\ Zlength ck = 32 /\ Zlength h = 32.
Proof.
  intros HA HL H0.
  unfold m_consume_init2_model, consume_init_stage2 in H0.
  destruct (negb _); [discriminate |].
  destruct (aead_dec _ _ _ _) eqn:E; inv H0.
  apply (aead_dec_length _ _ HA) in E. cbn [im_enct] in E.
  unfold kdf1, mix_hash, HASH. rewrite hci5_p8_A3_len_hmac, hci5_p8_A3_len_blake2s. lia.
Qed.

Lemma hci5_p8_A3_find_in : forall PS s a P, pk_find PS s = Some (a, P) -> exists sh, In (a, sh, P) PS.
Proof.
  induction PS as [|[[x sh] Q] PS IH]; simpl; intros s a P H; [discriminate|].
  destruct (bytes_eqb (hs_rstatic (p_hs Q)) s).
  - inv H. eauto.
  - destruct (IH _ _ _ H) as [sh' Hin]. eauto.
Qed.

Lemma hci5_p8_A3_nodup PS KE T : itable_wf T -> hci5_T_ok PS KE T -> NoDup (map peer_addr4 PS).
Proof.
  intros (_ & _ & H & _) (Hs & _). rewrite Hs in H.
  apply NoDup_app_remove_l in H.
  apply (NoDup_map_inv hs_addr). rewrite map_map. exact H.
Qed.

Lemma hci5_p8_A3_sfind : forall PS a sh P, NoDup (map peer_addr4 PS) -> In (a, sh, P) PS ->
  sfind PS a = Some (sh, P).
Proof.
  induction PS as [|[[x sh0] w] PS IH]; simpl; intros a sh P Hnd Hin; [contradiction|].
  inv Hnd. destruct Hin as [Heq | Hin].
  - inv Heq. rewrite if_true by auto. reflexivity.
  - rewrite if_false; [eauto|]. intros ->. apply H1.
    change a with (peer_addr4 (a, sh, P)). apply in_map; auto.
Qed.

Lemma hci5_p8_A3_split T : forall PS NS a sh P,
  map hn_p NS = map peer_addr4 PS -> NoDup (map peer_addr4 PS) -> In (a, sh, P) PS ->
  exists NS1 N NS2, hnodes_snapped4 T NS PS = NS1 ++ hn_snapshot4 T N (a, sh, P) :: NS2 /\
    hci5_nfind NS a = hn_addr N /\ hn_p N = a.
Proof.
  induction PS as [|[[x sh0] Q] PS IH]; intros NS a sh P Hmap Hnd Hin; [contradiction|].
  destruct NS as [|N0 NS]; [discriminate|]. simpl in Hmap. injection Hmap as Hx Hmap. subst x.
  simpl in Hnd. apply NoDup_cons_iff in Hnd. destruct Hnd as [H1 H2].
  change (hnodes_snapped4 T (N0 :: NS) ((hn_p N0, sh0, Q) :: PS)) with
    (hn_snapshot4 T N0 (hn_p N0, sh0, Q) :: hnodes_snapped4 T NS PS).
  destruct Hin as [Heq | Hin].
  - inv Heq. exists [], N0, (hnodes_snapped4 T NS PS).
    simpl. rewrite if_true by auto. auto.
  - destruct (IH NS a sh P Hmap H2 Hin) as (NS1 & N & NS2 & E & Ha & Hp).
    exists (hn_snapshot4 T N0 (hn_p N0, sh0, Q) :: NS1), N, NS2.
    split; [rewrite E; reflexivity|]. split; [| auto].
    simpl. rewrite if_false; auto. intros Hx. rewrite Hx in H1. apply H1.
    change a with (peer_addr4 (a, sh, P)). apply in_map; auto.
Qed.

Lemma hci5_p8_A3_supd_addrs (PS: list (val * share * peer)) a v :
  map peer_addr4 (supd PS a v) = map peer_addr4 PS.
Proof.
  induction PS as [|[[x sh] w] PS IH]; [reflexivity |]. simpl.
  destruct (EqDec_val x a); simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma hci5_p8_A3_supd_shares (PS: list (val * share * peer)) a v :
  Forall (fun x => match x with (_, sh, _) => sh = Ews end) PS ->
  Forall (fun x => match x with (_, sh, _) => sh = Ews end) (supd PS a v).
Proof.
  induction PS as [|[[x sh] w] PS IH]; intros H; [constructor |]. inv H. simpl.
  destruct (EqDec_val x a); constructor; auto.
Qed.

Lemma hci5_p8_A3_snapped_p T : forall NS PS, map hn_p NS = map peer_addr4 PS ->
  map hn_p (hnodes_snapped4 T NS PS) = map hn_p NS.
Proof.
  induction NS as [|N NS IH]; intros [|[[p sh] P] PS] H; simpl in H; try discriminate; auto.
  injection H as H1 H2.
  change (hnodes_snapped4 T (N :: NS) ((p, sh, P) :: PS)) with
    (hn_snapshot4 T N (p, sh, P) :: hnodes_snapped4 T NS PS).
  simpl. rewrite IH by auto. reflexivity.
Qed.

Lemma hci5_p8_A3_kents_addr T KE : map ke_addr (map (kent_snapped T) KE) = map ke_addr KE.
Proof. rewrite map_map. apply map_ext. intros e. reflexivity. Qed.

(* the list without the peer at a *)
Lemma hci5_p8_A3_in_app : forall PS (a: val) (sh: share) (P: peer), In (a, sh, P) PS ->
  exists PS1 PS2, PS = PS1 ++ (a, sh, P) :: PS2.
Proof.
  induction PS as [|x PS IH]; intros a sh P Hin; [contradiction|].
  destruct Hin as [<- | Hin]; [exists [], PS; reflexivity|].
  destruct (IH a sh P Hin) as (PS1 & PS2 & E). exists (x :: PS1), PS2. rewrite E. reflexivity.
Qed.

Lemma hci5_p8_A3_sdel : forall PS1 PS2 (a: val) (sh: share) (P: peer),
  NoDup (map peer_addr4 (PS1 ++ (a, sh, P) :: PS2)) -> sdel (PS1 ++ (a, sh, P) :: PS2) a = PS1 ++ PS2.
Proof.
  induction PS1 as [|[[x sh0] w] PS1 IH]; intros PS2 a sh P Hnd; simpl.
  - rewrite if_true by auto. reflexivity.
  - simpl in Hnd. apply NoDup_cons_iff in Hnd. destruct Hnd as [H1 H2].
    rewrite if_false; [rewrite IH by exact H2; reflexivity|].
    intros ->. apply H1. rewrite map_app. apply in_app_iff. right. left. reflexivity.
Qed.

(* the pubkey_next of the peer at a: NULL or another peer's address *)
Lemma hci5_p8_A3_chain : forall PS1 head PS2 (a: val) (sh: share) (P: peer),
  pk_chain head (PS1 ++ (a, sh, P) :: PS2) ->
  p_pknext P = nullval \/ In (p_pknext P) (map peer_addr4 (PS1 ++ PS2)).
Proof.
  induction PS1 as [|[[x sh0] w] PS1 IH]; intros head PS2 a sh P Hc; simpl in Hc.
  - destruct Hc as [_ Hc]. destruct PS2 as [|[[y sh1] Q] PS2]; simpl in Hc; [left; exact Hc|].
    right. destruct Hc as [-> _]. left. reflexivity.
  - destruct Hc as [_ Hc]. destruct (IH _ _ _ _ _ Hc) as [E | E]; [left; exact E|].
    right. right. exact E.
Qed.

(* the accepted peer after the call: its rest is P's *)
Lemma hci5_p8_A3_veqb_refl v : veqb v v = true.
Proof. unfold veqb. rewrite if_true by auto. reflexivity. Qed.

Lemma hci5_p8_A3_bytes_eqb_refl b : bytes_eqb b b = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec _ b b); [reflexivity | congruence]. Qed.

Lemma hci5_p8_A3_pr_eqb P M now t ck2 h2 : pr_eqb P (hci5_p8_put P M now t ck2 h2) = true.
Proof.
  unfold pr_eqb, pr_eqb_nc, cookie_eqb, hci5_p8_put, hci5_new, p_set_hs, p_set_refs.
  destruct P; cbn - [veqb bytes_eqb Int64.eq].
  rewrite !hci5_p8_A3_veqb_refl, !hci5_p8_A3_bytes_eqb_refl, !Int64.eq_true, !eqb_reflx. reflexivity.
Qed.

Section Facts.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).

(* everything the CHECKs of A3 need about the accepted peer, its node, its entry and the model's values *)
Lemma hci5_p8_A3_facts R L NS PS KE T head na M now a P t ck2 h2 :
  aead_props aead_enc aead_dec ->
  hci5_inv x25519 R L NS PS KE T head na -> itable_wf T -> im_ok M ->
  hci5_tgt x25519 aead_dec (hci5_IB x25519 R) PS M now = Some (a, P, t, ck2, h2) ->
  exists NS1 N NS2 PS1 PS2,
    hnodes_snapped4 T NS PS = NS1 ++ N :: NS2 /\
    hn_addr N = hci5_nfind NS a /\ hn_p N = a /\
    hn_snap N = hsnap_val (hs_snap_cur T a P) /\ hn_refs N = Vint (p_refs P) /\ hn_rest N = prsnap_val P /\
    PS = PS1 ++ (a, Ews, P) :: PS2 /\ sdel PS a = PS1 ++ PS2 /\
    sfind PS a = Some (Ews, P) /\ In (a, Ews, P) PS /\
    hci5_pok x25519 R L (a, Ews, P) /\
    In (hs_addr a) (saddrs (t_D T)) /\ e_peer (t_entry_d T (hs_addr a)) = a /\
    (p_pknext P = nullval \/ In (p_pknext P) (map peer_addr4 (PS1 ++ PS2))) /\
    Forall (fun k => k = nullval \/ In k (map ke_addr KE)) [p_cur P; p_prev P; p_next P] /\
    Zlength t = 12 /\ Zlength ck2 = 32 /\ Zlength h2 = 32.
Proof.
  intros HA Hl Hwf HM Ht.
  unfold hci5_tgt in Ht.
  destruct (mi_ok (hci5_IB x25519 R)); [|discriminate].
  destruct (m_consume_init1_model x25519 aead_dec _ _ _) as [[[[s k] ck1] h1]|]; [|discriminate].
  destruct (pk_find PS s) as [[a0 P0]|] eqn:Hf; [|discriminate].
  destruct (m_consume_init2_model aead_dec _ ck1 h1 (im_enct M)) as [[[t0 ck0] h0]|] eqn:H2; [|discriminate].
  destruct (_ && _)%bool; [|discriminate]. inv Ht.
  destruct (hci5_p8_A3_len2 aead_enc aead_dec _ _ _ _ _ _ _ HA (proj1 (proj2 (proj2 HM))) H2) as (Lt & Lck & Lh).
  destruct (hci5_p8_A3_find_in _ _ _ _ Hf) as [sh Hin].
  destruct Hl as (Hpok & _ & Hch & Hnp & _ & HT & Hslots).
  pose proof (proj1 (Forall_forall _ _) Hpok _ Hin) as Hok.
  assert (Hsh: sh = Ews) by (destruct Hok; auto). subst sh.
  pose proof (hci5_p8_A3_nodup PS KE T Hwf HT) as Hnd.
  destruct (hci5_p8_A3_split T PS NS a Ews P Hnp Hnd Hin) as (NS1 & N & NS2 & E & Hfind & Hp).
  destruct (hci5_p8_A3_in_app PS a Ews P Hin) as (PS1 & PS2 & EPS).
  exists NS1, (hn_snapshot4 T N (a, Ews, P)), NS2, PS1, PS2.
  split; [exact E|]. cbn [hn_snapshot4 hn_addr hn_p hn_snap hn_refs hn_rest].
  split; [auto|]. split; [auto|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact EPS|].
  split; [rewrite EPS; apply hci5_p8_A3_sdel; rewrite <- EPS; exact Hnd|].
  split; [apply hci5_p8_A3_sfind; auto|]. split; [exact Hin|]. split; [exact Hok|].
  destruct HT as (Hs & _ & He & _).
  split; [rewrite Hs; apply in_app_iff; right;
          apply (in_map (fun x => hs_addr (peer_addr4 x)) PS (a, Ews, P)), Hin|].
  split; [exact (proj1 (Forall_forall _ _) He _ Hin)|].
  split; [rewrite EPS in Hch; exact (hci5_p8_A3_chain _ _ _ _ _ _ Hch)|].
  split; [exact (proj1 (Forall_forall _ _) Hslots _ Hin)|].
  auto.
Qed.

End Facts.
