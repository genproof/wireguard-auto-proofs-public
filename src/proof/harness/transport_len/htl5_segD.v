
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require WgNoise.units.DataHeader.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_dec3.
Require Import WgNoise.proof.harness.common4t.ht4_worlds.
Require Import WgNoise.proof.harness.common4t.ht4c_spec.
Require Import WgNoise.proof.harness.common4t.ht4r_spec.
Require Import WgNoise.proof.harness.common4t.ht4a_aead.
Require Import WgNoise.proof.data_header.dh4_spec.
Require Import WgNoise.proof.harness.transport_len.htl5_defs.
Require WgNoise.harness.x_transport_len.code.
Require Import WgNoise.proof.aead.aead_models_props3.

#[local] Existing Instance W_transport_len.
Local Open Scope Z_scope.

Lemma htl5_segD_and1 b : 0 <= b <= Byte.max_unsigned ->
  Int.and (Int.repr b) (Int.repr 1) = Int.repr (Z.land b 1).
Proof. intros Hb. unfold Int.and. rewrite !Int.unsigned_repr by rep_lia. reflexivity. Qed.

Lemma htl5_segD_land1 b : 0 <= Z.land b 1 <= 1.
Proof.
  change (Z.land b 1) with (Z.land b (Z.ones 1)). rewrite Z.land_ones by lia.
  pose proof (Z.mod_pos_bound b (2 ^ 1) ltac:(lia)). lia.
Qed.

Lemma htl5_segD_bytes (bs: list Z) :
  Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  map (fun b => Vint (Int.repr b)) bs = map Vubyte (map Byte.repr bs).
Proof.
  induction 1; simpl; [reflexivity |]. f_equal; auto.
  unfold Vubyte. rewrite Byte.unsigned_repr by rep_lia. reflexivity.
Qed.

(* a byte buffer as the AEAD input (prim_bytes: emp when empty) and the 0-length rest kept in the frame *)
Lemma htl5_segD_pb (sh: share) (n: Z) (m: list byte) (p: val) :
  Zlength m = n ->
  data_at sh (tarray tuchar n) (map Vubyte m) p =
  (prim_bytes sh m p * (if Z.eq_dec n 0 then data_at sh (tarray tuchar n) (map Vubyte m) p else emp))%logic.
Proof.
  intros L. unfold prim_bytes. rewrite L. destruct (Z.eq_dec n 0).
  - rewrite emp_sepcon; auto.
  - rewrite sepcon_emp; auto.
Qed.

Lemma htl5_segD_pb_back (sh: share) (n: Z) (m: list byte) (p: val) :
  Zlength m = n ->
  (prim_bytes sh m p * (if Z.eq_dec n 0 then data_at sh (tarray tuchar n) (map Vubyte m) p else emp))%logic
  |-- data_at sh (tarray tuchar n) (map Vubyte m) p.
Proof. intros L. rewrite <- (htl5_segD_pb sh n m p L). apply derives_refl. Qed.

(* the packet split at the encrypted_data region [16, tot) *)
Lemma htl5_segD_split (pk: list byte) (tot: Z) (p: val) :
  Zlength pk = tot -> 16 <= tot -> field_compatible (tarray tuchar tot) [] p ->
  data_at Ews (tarray tuchar tot) (map Vubyte pk) p =
  (data_at Ews (tarray tuchar 16) (map Vubyte (sublist 0 16 pk)) p *
   data_at Ews (tarray tuchar (tot - 16)) (map Vubyte (sublist 16 tot pk)) (offset_val 16 p))%logic.
Proof.
  intros L H F.
  rewrite (split2_data_at_Tarray_tuchar Ews tot 16) by (try rewrite Zlength_map; lia).
  rewrite !sublist_map. f_equal. f_equal.
  unfold field_address0; rewrite if_true; [reflexivity|]. auto with field_compatible.
Qed.

(* the packet with its encrypted_data region replaced *)
Lemma htl5_segD_join (pk c: list byte) (tot: Z) (p: val) :
  Zlength pk = tot -> Zlength c = tot - 16 -> 16 <= tot -> field_compatible (tarray tuchar tot) [] p ->
  (data_at Ews (tarray tuchar 16) (map Vubyte (sublist 0 16 pk)) p *
   data_at Ews (tarray tuchar (tot - 16)) (map Vubyte c) (offset_val 16 p))%logic
  |-- data_at Ews (tarray tuchar tot) (map Vubyte (sublist 0 16 pk ++ c)) p.
Proof.
  intros L Lc H F.
  assert (L': Zlength (sublist 0 16 pk ++ c) = tot) by (rewrite Zlength_app, Zlength_sublist; lia).
  rewrite (htl5_segD_split (sublist 0 16 pk ++ c) tot p L' H F).
  rewrite sublist_app1 by (rewrite ?Zlength_sublist; lia).
  rewrite sublist_app2 by (rewrite Zlength_sublist; lia).
  rewrite sublist_sublist00 by lia.
  rewrite Zlength_sublist by lia.
  replace (16 - (16 - 0)) with 0 by lia. replace (tot - (16 - 0)) with (Zlength c) by lia.
  rewrite (sublist_same 0 (Zlength c) c) by lia. apply derives_refl.
Qed.

Lemma htl5_segD_ok {Espec: OracleKind} gv vk FR :
  semax htl5_Delta (htl5_PC gv vk FR) htl5_segD (overridePost (htl5_PD gv vk FR) (htl5_R gv)).
Proof.
  unfold htl5_PC. Intros key nonce tot pkt pk.
  unfold htl5_Delta, htl5_segD, htl5_R. apply htl5_post_canon.
  simplify_func_tycontext. abbreviate_semax.
  unfold htl5_lv, htl5_buf, htl5_ranges in *. simpl app.
  destruct H as (Hk & Hn & Ht).
  Intros. forward.
  assert (E1: Int64.sub (Int64.repr tot) (Int64.repr (Int.signed (Int.repr 16))) = Int64.repr (tot - 16))
    by (unfold Int64.sub; rewrite !Int64.unsigned_repr by rep_lia; reflexivity).
  rewrite E1; clear E1.
  match goal with |- semax _ ?P _ _ => forward_loop P break: P end.
  * apply ENTAIL_refl.
  * match goal with |- semax _ ?P _ _ => forward_if P end.
    -- exfalso. unfold Int64.ltu in H. rewrite !Int64.unsigned_repr in H by rep_lia.
       rewrite zlt_false in H by lia. exact (Int.one_not_zero H).
    -- forward. entailer!.
    -- forward. entailer!.
  * forward.
    assert (E2: Int64.sub (Int64.repr (tot - 16)) (Int64.repr (Int.signed (Int.repr 16))) = Int64.repr (tot - 32))
      by (change (Int.signed (Int.repr 16)) with 16; unfold Int64.sub; rewrite !Int64.unsigned_repr by rep_lia; f_equal; lia).
    rewrite E2; clear E2.
    forward_call tt.
    Intros b.
    forward.
    rewrite htl5_segD_and1 by auto.
    pose proof (htl5_segD_land1 b) as Hau.
    set (au := Z.land b 1) in *. clearbody au.
    assert_PROP (field_compatible (tarray tuchar tot) [] pkt) as Fp by entailer!.
    forward_if (PROP () LOCAL (temp TLC._pt_len (Vlong (Int64.repr (tot - 32)));
       temp TLC._enc_len (Vlong (Int64.repr (tot - 16))); temp TLC._pkt pkt;
       temp TLC._nonce (Vlong (Int64.repr nonce)); temp TLC._authentic (Vint (Int.repr au));
       lvar TLC._key (tarray tuchar 32) vk; gvars gv)
      SEP (EX pk': list byte, !! (Zlength pk' = tot /\ htl5_auth au key nonce tot pk') &&
             data_at Ews (tarray tuchar tot) (map Vubyte pk') pkt;
           data_at Tsh (tarray tuchar 32) (map Vubyte key) vk; malloc_token Ews (tarray tuchar tot) pkt;
           mem_mgr gv; zero_page gv; htl5_minusp gv; FR)).
    -- forward_call (tarray tuchar (tot - 32), gv).
       { simpl sizeof. rewrite Z.max_r by lia. rep_lia. }
       Intros pt.
       destruct (eq_dec pt nullval) as [Hnull | Hnn].
       { subst pt. forward_if (PROP (False) LOCAL () SEP ()).
         - assert_PROP (isptr pkt) as Pp by entailer!.
           sep_apply (data_at_data_at_ Ews (tarray tuchar tot) (map Vubyte pk) pkt).
           forward_call (tarray tuchar tot, pkt, gv).
           { rewrite if_false by (destruct pkt; try contradiction; discriminate). cancel. }
           forward. sep_apply (data_at_data_at_ Tsh (tarray tuchar 32) (map Vubyte key) vk). cancel.
         - contradiction H3. reflexivity. }
       match goal with |- semax _ ?P _ _ => forward_if P end.
       { contradiction. }
       { forward. entailer!. }
       Intros.
       forward_call (pt, tot - 32, Ews).
       Intros bs. rewrite (htl5_segD_bytes bs) by auto.
       set (m := map Byte.repr bs).
       assert (Hm: Zlength m = tot - 32) by (subst m; rewrite Zlength_map; auto).
       clearbody m. clear dependent bs.
       rewrite (htl5_segD_pb Ews (tot - 32) m pt Hm).
       rewrite (htl5_segD_split pk tot pkt) by (auto; lia).
       sep_apply (data_at_data_at_ Ews (tarray tuchar (tot - 16)) (map Vubyte (sublist 16 tot pk)) (offset_val 16 pkt)).
       replace (tot - 16) with (Zlength m + 16) by lia.
       assert (P0: prim_bytes Ews [] nullval = emp) by reflexivity.
       Intros.
       forward_call (Ews, offset_val 16 pkt, Ews, pt, m, Ews, nullval, @nil byte, nonce, Tsh, vk, key, gv).
       { entailer!. simpl. rewrite Hm. reflexivity. }
       { rewrite P0. cancel. }
       { rewrite Zlength_nil. rep_lia. }
       rewrite P0.
       sep_apply (htl5_segD_pb_back Ews (tot - 32) m pt Hm).
       assert_PROP (isptr pt) as Ppt by entailer!.
       sep_apply (data_at_data_at_ Ews (tarray tuchar (tot - 32)) (map Vubyte m) pt).
       forward_call (tarray tuchar (tot - 32), pt, gv).
       { rewrite if_false by (destruct pt; try contradiction; discriminate). cancel. }
       destruct aead_models_ok3 as [HA _].
       pose proof (aead_enc_length _ _ HA key nonce [] m) as Le.
       remember (aead_enc key nonce [] m) as c eqn:Ec.
       replace (Zlength m + 16) with (tot - 16) by lia.
       sep_apply (htl5_segD_join pk c tot pkt H1 ltac:(lia) ltac:(lia) Fp).
       Exists (sublist 0 16 pk ++ c).
       entailer!.
       split.
       ++ rewrite Zlength_app, Zlength_sublist by lia. lia.
       ++ intros _. exists m. split; auto.
          rewrite sublist_app2 by (rewrite Zlength_sublist by lia; lia).
          rewrite Zlength_sublist by lia. rewrite sublist_same by lia. reflexivity.
    -- forward. Exists pk. entailer!. intros E. exfalso. assert (au = 1) by lia. subst au. discriminate H2.
    -- Intros pk'. unfold htl5_PD, htl5_lv, htl5_buf, htl5_ranges. simpl app.
       Exists key nonce tot pkt pk' au. entailer!.
Qed.
