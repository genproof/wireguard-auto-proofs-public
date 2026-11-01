(* law handshake_receive: phase B8, branch R: the
   pure statement hrx5_B8R_I_stmt. *)
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
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* lengths of the model's hashes                                           *)
(* ---------------------------------------------------------------------- *)

Lemma hrx5_B8RI_hash_len m : Zlength (HASH m) = 32.
Proof. unfold HASH, model.blake2s, model.b2s_digest_stream, model.b2s_out. rewrite Zlength_map. reflexivity. Qed.
Lemma hrx5_B8RI_kdf1_len a b : Zlength (kdf1 a b) = 32.
Proof. unfold kdf1, hmac. cbv zeta. apply hrx5_B8RI_hash_len. Qed.
Lemma hrx5_B8RI_mix_hash_len a b : Zlength (mix_hash a b) = 32.
Proof. unfold mix_hash. apply hrx5_B8RI_hash_len. Qed.

Lemma hrx5_B8RI_cr_len x25519 aead_dec ck0 h0 eph spriv psk e encn ck h :
  m_consume_response_model x25519 aead_dec ck0 h0 eph spriv psk e encn = Some (ck, h) ->
  Zlength ck = 32 /\ Zlength h = 32.
Proof.
  unfold m_consume_response_model, consume_resp_crypto. cbv zeta.
  destruct (negb _); [discriminate|]. destruct (negb _); [discriminate|].
  destruct (aead_dec _ _ _ _); [|discriminate]. intros H; inv H.
  split; [apply hrx5_B8RI_kdf1_len | apply hrx5_B8RI_mix_hash_len].
Qed.

Lemma hrx5_B8RI_sfind_in (l: list (val * share * peer)) a sh v :
  sfind l a = Some (sh, v) -> In (a, sh, v) l.
Proof.
  induction l as [|[[x shx] y] l IH]; simpl; intros H; [discriminate|].
  destruct (EqDec_val x a) as [->|Hne]; [inv H; left; reflexivity | right; auto].
Qed.

Lemma hrx5_B8RI_tgt x25519 aead_dec IA T PS M a P ck h :
  hrx5cr_tgt x25519 aead_dec IA T PS M = Some (a, P, ck, h) ->
  (exists sh, sfind PS a = Some (sh, P)) /\ Zlength ck = 32 /\ Zlength h = 32.
Proof.
  unfold hrx5cr_tgt. destruct (mi_ok IA); [|discriminate].
  destruct (t_find_index _ _ _) as [[x E]|]; [|discriminate].
  destruct (Int.eq (e_type E) IDX_HANDSHAKE); [|discriminate].
  destruct (sfind PS (e_peer E)) as [[sh P0]|] eqn:Hf; [|discriminate].
  destruct (Int.eq _ _); [|discriminate].
  destruct (m_consume_response_model _ _ _ _ _ _ _ _ _) as [[ck0 h0]|] eqn:Hm; [|discriminate].
  intros H; inv H. split; [eauto|]. eapply hrx5_B8RI_cr_len; exact Hm.
Qed.

(* ---------------------------------------------------------------------- *)
(* the boot clock is kept by begin_session                                 *)
(* ---------------------------------------------------------------------- *)

Lemma hrx5_B8RI_put_boot k u W : s_boot (kw_S (kp_put k u W)) = s_boot (kw_S W).
Proof.
  unfold kp_put. destruct (eq_dec k nullval); [reflexivity|].
  destruct (afind _ _); [|reflexivity]. destruct (Int.eq _ _); reflexivity.
Qed.

Lemma hrx5_B8RI_add_boot P new init W : s_boot (kw_S (snd (add_new_keypair_model P new init W))) = s_boot (kw_S W).
Proof.
  unfold add_new_keypair_model. destruct init; [destruct (negb _)|]; cbn [snd]; rewrite !hrx5_B8RI_put_boot; reflexivity.
Qed.

Lemma hrx5_B8RI_bs_boot P hs k kc W :
  s_boot (kw_S (snd (fst (begin_session_model P hs k kc W)))) = s_boot (kw_S W).
Proof.
  unfold begin_session_model. destruct (negb _); [reflexivity|].
  destruct (eq_dec k nullval); [reflexivity|]. cbv zeta.
  destruct (p_dead P); [reflexivity|].
  match goal with |- context [add_new_keypair_model ?a ?b ?c ?d] =>
    pose proof (hrx5_B8RI_add_boot a b c d) as HA; destruct (add_new_keypair_model a b c d) as [P2 W2] end.
  destruct (t_replace _ _ _). cbn [snd fst kw_S] in *. rewrite HA. reflexivity.
Qed.

Lemma hrx5_B8RI_resp_D W D1 S1 lul a P1 k sp len : rw_D (rx_resp_accepted W D1 S1 lul a P1 k sp len) = D1.
Proof. reflexivity. Qed.

Lemma hrx5_B8RI_resp_boot W D1 S1 lul a P1 k sp len :
  s_boot (rw_S (rx_resp_accepted W D1 S1 lul a P1 k sp len)) = s_boot S1.
Proof.
  unfold rx_resp_accepted. cbv zeta. cbn [rw_S].
  pose proof (hrx5_B8RI_bs_boot P1 (hs_addr a) k (rw_kc W) (mkKW (rw_KS W) (rw_T W) S1)) as HB.
  unfold bs_res. destruct (Int.eq _ _); [unfold shim_release; cbn [s_boot]|]; exact HB.
Qed.

(* ---------------------------------------------------------------------- *)
(* the invariant                                                           *)
(* ---------------------------------------------------------------------- *)

Lemma hrx5_B8RI_inv_T x25519 R L NS PS KE T T' head nk :
  t_D T' = t_D T -> hrx5_inv x25519 R L NS PS KE T head nk -> hrx5_inv x25519 R L NS PS KE T' head nk.
Proof.
  intros HD (H1 & H2 & H3 & H4 & H5 & H6 & H7). repeat (split; [assumption|]).
  unfold hrx5cr_pool in *. rewrite HD. exact H7.
Qed.

Lemma hrx5_B8RI_pok x25519 R L a P M ck h d :
  hrx5_pok x25519 R L (a, Ews, P) -> rm_ok M -> Zlength ck = 32 -> Zlength h = 32 ->
  hrx5_pok x25519 R L (a, Ews, hrx5_B8R_Pf d P M ck h).
Proof.
  intros (Hsh & Hdev & Hsid & Hhs & Hss & Hrefs & Hlic & Hpk & Hc & Hp & Hn) (Heph & _) Hck Hh.
  destruct Hhs as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  unfold hrx5_B8R_Pf, hrx5cr_new. destruct (hrx5_B8R_alloc d);
    cbn [hrx5_pok p_set_refs p_set_hs p_device p_hs p_refs p_pknext p_cur p_prev p_next hs_zero
         hs_sid hs_ss hs_rstatic hs_lic hs_ok hs_eph hs_reph hs_psk hs_hash hs_ck hs_ts];
    repeat split; auto; try (rewrite Zlength_zeros || unfold zeros; reflexivity); lia.
Qed.

Lemma hrx5_B8RI_snapped_p T NS PS :
  length NS = length PS -> map hn_p (hnodes_snapped4 T NS PS) = map hn_p NS.
Proof.
  unfold hnodes_snapped4. revert PS. induction NS as [|N NS IH]; intros [|x PS] H; simpl in *; try discriminate;
    [reflexivity|].
  destruct x as [[p sh] P]. simpl. f_equal. apply IH. lia.
Qed.

Lemma hrx5_B8RI_snapped_a T NS PS :
  length NS = length PS -> map hn_addr (hnodes_snapped4 T NS PS) = map hn_addr NS.
Proof.
  unfold hnodes_snapped4. revert PS. induction NS as [|N NS IH]; intros [|x PS] H; simpl in *; try discriminate;
    [reflexivity|].
  destruct x as [[p sh] P]. simpl. f_equal. apply IH. lia.
Qed.

Lemma hrx5_B8RI_kaddr T KE : map ke_addr (map (kent_snapped T) KE) = map ke_addr KE.
Proof. rewrite map_map. apply map_ext. intros e. reflexivity. Qed.

Lemma hrx5_B8RI_inv_nodes x25519 R L NS PS KE T head nk NS' KE' :
  hrx5_inv x25519 R L NS PS KE T head nk ->
  map hn_p NS' = map hn_p NS -> map hn_addr NS' = map hn_addr NS -> map ke_addr KE' = map ke_addr KE ->
  hrx5_inv x25519 R L NS' PS KE' T head nk.
Proof.
  intros (HF & Hwf & HND & Hch & Hnp & Hnk & Hpool) Hp Ha Hk.
  unfold hrx5_inv. split; [exact HF|]. split; [exact Hwf|]. split; [exact HND|]. split; [exact Hch|].
  split; [unfold hnodes_peers4 in *; rewrite Hp; exact Hnp|].
  split; [rewrite Ha; exact Hnk|]. rewrite Hk. exact Hpool.
Qed.

Lemma hrx5_B8RI_vm_cc CC s msg cc now rl r :
  snd (validate_model CC s msg cc now rl r) = CC \/
  snd (validate_model CC s msg cc now rl r) = checker_rotate CC now r.
Proof.
  unfold validate_model.
  destruct (negb (bytes_eqb _ _)); [left; reflexivity |].
  destruct (negb cc); [left; reflexivity |].
  destruct (negb (bytes_eqb _ _)); [right; reflexivity |].
  destruct (negb rl); right; reflexivity.
Qed.

Lemma hrx5_B8RI_rot CC now r :
  checker_rotate CC now r = CC \/
  checker_rotate CC now r = mkChk r (cc_ekey CC) (cc_mkey CC) now (cc_dev CC).
Proof. unfold checker_rotate. destruct (birthdate_expired _ _ _); auto. Qed.

Lemma hrx5_B8R_I_ok : hrx5_B8R_I_stmt.
Proof.
  unfold hrx5_B8R_I_stmt.
  intros x25519 aead_enc aead_dec xaead_enc xaead_dec L R sec birth S w NS PS T head nk KE st i kc lul q proto
    ip4 ip6 port o dp tg ai ar d a P M ck h j HY Hb Hinv Hst Hi Hok Hmc Hacc Hd HF.
  cbv zeta.
  cbn [fold_right] in HF.
  destruct HF as (Ho & Hfwd & Hai & Har & Ht & Hj & HZ & Hnp & Htg & HW1 & _).
  rewrite HW1. clear HW1. subst o.
  rewrite hrx5_B8RI_resp_D.
  assert (HSb: s_boot (hrx5_B8R_Sf d P (rx_resp_accepted
      (hrx5_W0 (hrx5_DL x25519 R L sec birth) T PS S w kc lul)
      (hrx5_B8R_D1 (hrx5_DL x25519 R L sec birth) S q lul (hrx5_skb dp (OResp M) proto ip4 ip6 port)
         (obj_bytes (OResp M)) d)
      (hrx5_B8R_S1 (hrx5_DL x25519 R L sec birth) S q lul (obj_bytes (OResp M)) d)
      (hrx5_B8R_lul1 S q lul) a (hrx5cr_new P M ck h) (rd_k d) (l_skb L)
      (sk_len (hrx5_skb dp (OResp M) proto ip4 ip6 port)))) = s_boot S).
  { unfold hrx5_B8R_Sf.
    destruct (hrx5_B8R_sess d P); [unfold shim_free; cbn [s_boot]|]; rewrite hrx5_B8RI_resp_boot;
      unfold hrx5_B8R_S1; destruct (validate_rotates _ _ _ _); reflexivity. }
  unfold hrx5_base_ok. rewrite HSb. clear HSb.
  (* the peer *)
  destruct (hrx5_B8RI_tgt _ _ _ _ _ _ _ _ _ _ Ht) as ([sh Hf] & Hck & Hh).
  assert (HI: hrx5_inv x25519 R L (hnodes_snapped4 T NS PS) (supd PS a (hrx5_B8R_Pf d P M ck h))
                (map (kent_snapped T) KE) (hrx5_B8R_Tf d P T a) head nk).
  { assert (Hlen: length NS = length PS).
    { destruct Hinv as (_ & _ & _ & _ & Hnp' & _). unfold hnodes_peers4 in Hnp'.
      rewrite <- (map_length hn_p NS), Hnp', map_length. reflexivity. }
    pose proof (proj1 Hinv) as HFa.
    rewrite Forall_forall in HFa. pose proof (HFa _ (hrx5_B8RI_sfind_in _ _ _ _ Hf)) as Hpok.
    assert (sh = Ews) by (destruct Hpok as [? _]; auto). subst sh.
    assert (HI2: hrx5_inv x25519 R L NS (supd PS a (hrx5_B8R_Pf d P M ck h)) KE T head nk).
    { eapply (proj1 (hrx5_B8i_lem x25519)); [exact Hinv | exact Hf | |].
      - apply hrx5_B8RI_pok; auto.
      - unfold hrx5_B8R_Pf, hrx5cr_new. destruct (hrx5_B8R_alloc d); reflexivity. }
    eapply hrx5_B8RI_inv_T; [| eapply hrx5_B8RI_inv_nodes; [exact HI2 | | | apply hrx5_B8RI_kaddr]].
    - unfold hrx5_B8R_Tf. destruct (hrx5_B8R_sess d P); reflexivity.
    - apply hrx5_B8RI_snapped_p; exact Hlen.
    - apply hrx5_B8RI_snapped_a; exact Hlen. }
  (* the device *)
  unfold hrx5_B8R_D1, hrx5_B8R_vm.
  set (vm := validate_model _ _ _ _ _ _ _).
  assert (Hv: snd vm = d_cc (hrx5_DL x25519 R L sec birth) \/
              snd vm = checker_rotate (d_cc (hrx5_DL x25519 R L sec birth)) (s_boot S) (rd_r d))
    by apply hrx5_B8RI_vm_cc.
  clearbody vm.
  assert (HD: forall sec1 birth1, dev_set_cc (hrx5_DL x25519 R L sec birth)
     (mkChk sec1 (cc_ekey (d_cc (hrx5_DL x25519 R L sec birth))) (cc_mkey (d_cc (hrx5_DL x25519 R L sec birth))) birth1
        (cc_dev (d_cc (hrx5_DL x25519 R L sec birth)))) = hrx5_DL x25519 R L sec1 birth1).
  { intros. unfold hrx5_DL, hrx5_D, setup_dev, dev_set_cc. cbn [d_cc cc_ekey cc_mkey cc_dev]. reflexivity. }
  assert (HD0: dev_set_cc (hrx5_DL x25519 R L sec birth) (d_cc (hrx5_DL x25519 R L sec birth)) =
               hrx5_DL x25519 R L sec birth).
  { unfold hrx5_DL, hrx5_D, setup_dev, dev_set_cc. cbn [d_cc]. reflexivity. }
  destruct Hb as (Hrun & Hsec & Hbirth & Hnow).
  destruct Hd as (Hr & _).
  destruct Hv as [Hv | Hv]; rewrite Hv;
    [| destruct (hrx5_B8RI_rot (d_cc (hrx5_DL x25519 R L sec birth)) (s_boot S) (rd_r d)) as [Hq | Hq];
       rewrite Hq].
  - exists sec, birth. rewrite HD0. auto 10.
  - exists sec, birth. rewrite HD0. auto 10.
  - exists (rd_r d), (s_boot S). rewrite HD. auto 10.
Qed.
