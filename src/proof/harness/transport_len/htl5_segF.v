
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

(* a byte buffer of n bytes as the AEAD output (prim_out: emp when empty) and the 0-length rest kept in the frame *)
Lemma htl5_segF_po (sh: share) (n: Z) (v: list val) (p: val) :
  Zlength v = n ->
  data_at sh (tarray tuchar n) v p =
  (prim_out sh v p * (if Z.eq_dec n 0 then data_at sh (tarray tuchar n) v p else emp))%logic.
Proof.
  intros L. unfold prim_out. rewrite L. destruct (Z.eq_dec n 0).
  - rewrite emp_sepcon; auto.
  - rewrite sepcon_emp; auto.
Qed.

Lemma htl5_segF_po_back (sh: share) (n: Z) (v v': list val) (p: val) :
  Zlength v = n -> Zlength v' = n ->
  (prim_out sh v' p * (if Z.eq_dec n 0 then data_at sh (tarray tuchar n) v p else emp))%logic
  |-- data_at sh (tarray tuchar n) v' p.
Proof.
  intros L L'. unfold prim_out. rewrite L'. destruct (Z.eq_dec n 0) as [E|E].
  - rewrite emp_sepcon. rewrite E in L, L'. apply Zlength_nil_inv in L. apply Zlength_nil_inv in L'. subst. apply derives_refl.
  - rewrite sepcon_emp. apply derives_refl.
Qed.

(* the packet split at the encrypted_data region [16, tot) *)
Lemma htl5_segF_split (pk: list byte) (tot: Z) (p: val) :
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

Lemma htl5_segF_merge (pk: list byte) (tot: Z) (p: val) :
  Zlength pk = tot -> 16 <= tot -> field_compatible (tarray tuchar tot) [] p ->
  (data_at Ews (tarray tuchar 16) (map Vubyte (sublist 0 16 pk)) p *
   data_at Ews (tarray tuchar (tot - 16)) (map Vubyte (sublist 16 tot pk)) (offset_val 16 p))%logic
  |-- data_at_ Ews (tarray tuchar tot) p.
Proof. intros L H F. rewrite <- htl5_segF_split by auto. apply data_at_data_at_. Qed.

(* minusp as ref_aead_decrypt_spec_n W_transport_len states it (u32 arrays are cs-independent) *)
Lemma htl5_segF_minusp gv : htl5_minusp gv = @ht4_minusp W_transport_len htl5_mp gv.
Proof. unfold htl5_minusp, ht4_minusp. apply htl5_data_at_tuint_cs. Qed.

(* VST's after_forward_call simplifies remove_localdef_temp with `simpl rlt_ident_eq`, exponential in the common
   bits of two identifiers (TLC._ref_ok vs TLC._ref_pt); this removes it by Pos.eqb computation instead *)
Lemma htl5_segF_rlt (i: ident) (L: list localdef) :
  forallb (fun d => match d with temp j _ => negb (Pos.eqb i j) | _ => true end) L = true ->
  remove_localdef_temp i L = L.
Proof.
  induction L as [|d L IH]; intros H; [reflexivity |].
  simpl in H. apply andb_prop in H as [H1 H2].
  change (remove_localdef_temp i (d :: L)) with
    (match d with temp j _ => if rlt_ident_eq i j then remove_localdef_temp i L else d :: remove_localdef_temp i L
     | _ => d :: remove_localdef_temp i L end).
  rewrite IH by auto.
  destruct d; auto.
  destruct (rlt_ident_eq i i0); auto. subst. rewrite Pos.eqb_refl in H1. discriminate.
Qed.

Lemma htl5_segF_ok {Espec: OracleKind} gv vk FR :
  semax htl5_Delta (htl5_PE gv vk FR) htl5_segF (overridePost FF (htl5_R gv)).
Proof.
unfold htl5_PE. Intros key nonce tot pkt pk au pto rpt.
unfold htl5_Delta, htl5_segF, htl5_R. apply htl5_post_canon. simplify_func_tycontext. abbreviate_semax.
unfold htl5_lv, htl5_buf, htl5_ranges in *. simpl app.
destruct H as (Hk & Hn & Ht).
destruct aead_models_ok3 as [HA _].
assert_PROP (field_compatible (tarray tuchar tot) [] pkt) as Fp by entailer!.
rewrite (htl5_segF_split pk tot pkt) by (auto; lia).
assert (Lc: Zlength (sublist 16 tot pk) = tot - 16) by (rewrite Zlength_sublist; lia).
assert (Hl: forall pt, aead_dec key nonce [] (sublist 16 tot pk) = Some pt -> Zlength pt = tot - 32)
  by (intros pt E; apply (aead_dec_length _ _ HA) in E; lia).
assert (Hau: au <> 0 -> exists pt, aead_dec key nonce [] (sublist 16 tot pk) = Some pt).
{ intros E. destruct (H3 E) as (m & _ & Em). rewrite Em. exists m. apply (aead_dec_enc _ _ HA). }
clear H3.
remember (sublist 16 tot pk) as c eqn:Ec.
rewrite (htl5_segF_po Ews (tot - 32) (Zrepeat Vundef (tot - 32)) pto) by (rewrite Zlength_Zrepeat; lia).
rewrite (htl5_segF_po Ews (tot - 32) (Zrepeat Vundef (tot - 32)) rpt) by (rewrite Zlength_Zrepeat; lia).
assert (Pc: data_at Ews (tarray tuchar (tot - 16)) (map Vubyte c) (offset_val 16 pkt) = prim_bytes Ews c (offset_val 16 pkt))
  by (unfold prim_bytes; rewrite if_false, Lc by lia; reflexivity).
rewrite Pc. Intros.
assert (P0: prim_bytes Ews [] nullval = emp) by reflexivity.
forward_call (Ews, pto, Zrepeat Vundef (tot - 32), Ews, offset_val 16 pkt, c, Ews, nullval, @nil byte, nonce, Tsh, vk, key, gv).
{ entailer!. simpl. rewrite Lc. reflexivity. }
{ rewrite P0. cancel. }
{ rewrite Zlength_nil, Zlength_Zrepeat by lia. rep_lia. }
rewrite htl5_segF_minusp.
(* forward_call by hand: after_forward_call only once remove_localdef_temp is gone (htl5_segF_rlt) *)
eapply semax_seq'.
- prove_call_setup (@nil Type) funspec_sub_refl
    (Ews, rpt, Zrepeat Vundef (tot - 32), Ews, offset_val 16 pkt, c, Ews, nullval, @nil byte, nonce, Tsh, vk, key, gv);
    clear_Delta_specs; clear_MORE_POST; [ .. | forward_call_id1_y_wow ].
  + entailer!. simpl. rewrite Lc. reflexivity.
  + rewrite Zlength_nil, Zlength_Zrepeat by lia. rep_lia.
- match goal with |- context [remove_localdef_temp ?i ?L] => rewrite (htl5_segF_rlt i L) by reflexivity end.
  after_forward_call.
  rewrite P0.
  destruct (aead_dec key nonce [] c) as [pt|] eqn:Hd.
  + assert (Hpt: Zlength pt = tot - 32) by (apply Hl; auto).
    cbv [Val.of_bool].
    match goal with |- semax _ ?P _ _ => forward_loop P break: P end.
    * apply ENTAIL_refl.
    * match goal with |- semax _ ?P _ _ => forward_if P end.
      -- match goal with Hc: Int.repr (Z.b2z (Int.eq _ _)) = Int.zero |- _ =>
           rewrite Int.eq_true in Hc; discriminate Hc end.
      -- forward. entailer!.
      -- forward. entailer!.
    * sep_apply (htl5_segF_po_back Ews (tot - 32) (Zrepeat Vundef (tot - 32)) (map Vubyte pt) pto
        ltac:(rewrite Zlength_Zrepeat; lia) ltac:(rewrite Zlength_map; lia)).
      sep_apply (htl5_segF_po_back Ews (tot - 32) (Zrepeat Vundef (tot - 32)) (map Vubyte pt) rpt
        ltac:(rewrite Zlength_Zrepeat; lia) ltac:(rewrite Zlength_map; lia)).
      match goal with |- semax _ ?P _ _ => forward_if P end.
      -- match goal with |- semax _ ?P _ _ => forward_loop P break: P end.
         ++ apply ENTAIL_refl.
         ++ forward_call (Ews, pto, pt, Ews, rpt, pt).
            { entailer!. simpl. rewrite Hpt. reflexivity. }
            { rewrite Hpt. cancel. }
            rewrite if_true by auto.
            match goal with |- semax _ ?P _ _ => forward_if P end.
            { match goal with Hc: _ |- _ => discriminate Hc end. }
            { forward. entailer!. }
            forward. rewrite Hpt. entailer!.
      -- match goal with Hc: Int.one = Int.zero |- _ => contradiction (Int.one_not_zero Hc) end.
      -- match goal with |- semax _ ?P _ _ => forward_if P end.
         ++ match goal with |- semax _ ?P _ _ => forward_loop P break: P end.
            ** apply ENTAIL_refl.
            ** match goal with |- semax _ ?P _ _ => forward_if P end.
               { match goal with Hc: _ |- _ => discriminate Hc end. }
               forward. entailer!.
               forward. entailer!.
         ++ forward. entailer!.
         ++
            rewrite <- Pc, Ec.
            sep_apply (htl5_segF_merge pk tot pkt H1 ltac:(lia) Fp).
            assert_PROP (isptr pkt /\ isptr pto /\ isptr rpt) as Pptrs by entailer!. destruct Pptrs as (Pp & Ppo & Prp).
            forward_call (tarray tuchar tot, pkt, gv).
            { rewrite if_false by (destruct pkt; try contradiction; discriminate). cancel. }
            forward_call (tarray tuchar (tot - 32), pto, gv).
            { rewrite if_false by (destruct pto; try contradiction; discriminate).
              sep_apply (data_at_data_at_ Ews (tarray tuchar (tot - 32)) (map Vubyte pt) pto). cancel. }
            forward_call (tarray tuchar (tot - 32), rpt, gv).
            { rewrite if_false by (destruct rpt; try contradiction; discriminate).
              sep_apply (data_at_data_at_ Ews (tarray tuchar (tot - 32)) (map Vubyte pt) rpt). cancel. }
            forward.
            sep_apply (data_at_data_at_ Tsh (tarray tuchar 32) (map Vubyte key) vk).
            cancel.
  + assert (Ha0: au = 0) by (destruct (Z.eq_dec au 0) as [E|E]; auto; destruct (Hau E) as [? E']; discriminate E').
    subst au. cbv [Val.of_bool].
    match goal with |- semax _ ?P _ _ => forward_loop P break: P end.
    * apply ENTAIL_refl.
    * match goal with |- semax _ ?P _ _ => forward_if P end.
      -- match goal with Hc: Int.repr (Z.b2z (Int.eq _ _)) = Int.zero |- _ =>
           rewrite Int.eq_true in Hc; discriminate Hc end.
      -- forward. entailer!.
      -- forward. entailer!.
    * sep_apply (htl5_segF_po_back Ews (tot - 32) (Zrepeat Vundef (tot - 32)) (Zrepeat Vundef (tot - 32)) pto
        ltac:(rewrite Zlength_Zrepeat; lia) ltac:(rewrite Zlength_Zrepeat; lia)).
      sep_apply (htl5_segF_po_back Ews (tot - 32) (Zrepeat Vundef (tot - 32)) (Zrepeat Vundef (tot - 32)) rpt
        ltac:(rewrite Zlength_Zrepeat; lia) ltac:(rewrite Zlength_Zrepeat; lia)).
      match goal with |- semax _ ?P _ _ => forward_if P end.
      -- match goal with Hc: Int.zero <> Int.zero |- _ => contradiction end.
      -- forward. entailer!.
      -- match goal with |- semax _ ?P _ _ => forward_if P end.
         ++ match goal with Hc: Int.repr 0 <> Int.zero |- _ => contradiction end.
         ++ forward. entailer!.
         ++
            rewrite <- Pc, Ec.
            sep_apply (htl5_segF_merge pk tot pkt H1 ltac:(lia) Fp).
            assert_PROP (isptr pkt /\ isptr pto /\ isptr rpt) as Pptrs by entailer!. destruct Pptrs as (Pp & Ppo & Prp).
            forward_call (tarray tuchar tot, pkt, gv).
            { rewrite if_false by (destruct pkt; try contradiction; discriminate). cancel. }
            forward_call (tarray tuchar (tot - 32), pto, gv).
            { rewrite if_false by (destruct pto; try contradiction; discriminate).
              sep_apply (data_at_data_at_ Ews (tarray tuchar (tot - 32)) (Zrepeat Vundef (tot - 32)) pto). cancel. }
            forward_call (tarray tuchar (tot - 32), rpt, gv).
            { rewrite if_false by (destruct rpt; try contradiction; discriminate).
              sep_apply (data_at_data_at_ Ews (tarray tuchar (tot - 32)) (Zrepeat Vundef (tot - 32)) rpt). cancel. }
            forward.
            sep_apply (data_at_data_at_ Tsh (tarray tuchar 32) (map Vubyte key) vk).
            cancel.
Qed.
