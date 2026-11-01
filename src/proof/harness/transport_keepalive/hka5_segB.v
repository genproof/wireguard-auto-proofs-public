(* segment B of main's loop body (statements 8..12: nonce, the header stores, encrypted_data: the AEAD of the empty plaintext, one byte corrupted for kind 1, or random bytes for kind 3).
   States and segments: hka5_defs.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_dec3.
Require Import WgNoise.proof.counter.counter_spec.
Require Import WgNoise.proof.harness.transport_keepalive.hka5_defs.
Require Import WgNoise.proof.harness.transport_keepalive.hka5e_lemmas.
Require WgNoise.proof.aead.aead_models_props3.

#[local] Existing Instance W_transport_keepalive.
Local Open Scope Z_scope.

Ltac hka5b_post := unfold hka5_LR, hka5_R;
  cbn [RA_break RA_normal loop1_ret_assert overridePost frame_ret_assert function_body_ret_assert].

Lemma hka5b_enc_range k e : hka5_kind_ok k e -> 0 <= e <= 16.
Proof. unfold hka5_kind_ok. intros (Hk & H3 & Hn3). destruct (Z.eq_dec k 3); [specialize (H3 e0) | specialize (Hn3 n)]; lia. Qed.

Lemma hka5b_resize sh n (C: list val) p : Zlength C = n ->
  data_at sh (tarray tuchar n) C p = data_at sh (tarray tuchar (Zlength C)) C p.
Proof. intros; subst; reflexivity. Qed.

Lemma hka5b_le64_len z : Zlength (le64_bytes z) = 8.
Proof. reflexivity. Qed.

Lemma hka5b_le32_len w : Zlength (le32_bytes w) = 4.
Proof. reflexivity. Qed.

Lemma hka5b_splice_len i l c : 0 <= i -> i + Zlength l <= Zlength c ->
  Zlength (haead_splice i l c) = Zlength c.
Proof. intros. unfold haead_splice. list_solve. Qed.

(* the header written by the three stores, and the untouched encrypted_data *)
Lemma hka5b_hdr (a b: int) (n enc: Z) : 0 <= enc ->
  haead_splice 8 (le64_bytes n) (haead_splice 4 (le32_bytes b) (haead_splice 0 (le32_bytes a) (Zrepeat Vundef (16 + enc)))) =
  sublist 0 16 (haead_splice 8 (le64_bytes n) (haead_splice 4 (le32_bytes b) (haead_splice 0 (le32_bytes a) (Zrepeat Vundef (16 + enc))))) ++
  Zrepeat Vundef enc.
Proof.
  intros He. unfold haead_splice.
  pose proof (hka5b_le64_len n). pose proof (hka5b_le32_len a). pose proof (hka5b_le32_len b).
  list_solve.
Qed.

Lemma hka5b_hdr_len (a b: int) (n enc: Z) : 0 <= enc ->
  Zlength (sublist 0 16 (haead_splice 8 (le64_bytes n) (haead_splice 4 (le32_bytes b)
    (haead_splice 0 (le32_bytes a) (Zrepeat Vundef (16 + enc)))))) = 16.
Proof.
  intros He. unfold haead_splice.
  pose proof (hka5b_le64_len n). pose proof (hka5b_le32_len a). pose proof (hka5b_le32_len b).
  list_solve.
Qed.

Lemma hka5b_pb_nil sh p : @prim_bytes W_transport_keepalive sh [] p = emp.
Proof. reflexivity. Qed.

Lemma hka5b_enc_len key n : Zlength (aead_enc key n [] []) = 16.
Proof.
  destruct WgNoise.proof.aead.aead_models_props3.aead_models_ok3 as [HP _].
  rewrite (aead_enc_length _ _ HP). reflexivity.
Qed.

Lemma hka5b_bytes (kb: list Z) : Forall (fun b => 0 <= b <= Byte.max_unsigned) kb ->
  map (fun b => Vint (Int.repr b)) kb = map Vubyte (map Byte.repr kb).
Proof.
  intros H. induction H as [|b kb Hb H IH]; [reflexivity |]. simpl. rewrite IH. f_equal.
  unfold Vubyte. rewrite Byte.unsigned_repr by (unfold Byte.max_unsigned in Hb; simpl in Hb; rep_lia). reflexivity.
Qed.

(* VST's after_forward_call simplifies remove_localdef_temp with `simpl rlt_ident_eq`; this removes it by Pos.eqb computation instead *)
Lemma hka5b_rlt (i: ident) (L: list localdef) :
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

(* a call `x = f(...)` by hand (forward_call hangs in after_forward_call, see hka5b_rlt) *)
Ltac hka5b_call w :=
  eapply semax_seq';
  [ prove_call_setup (@nil Type) funspec_sub_refl w; clear_Delta_specs; clear_MORE_POST;
    [ .. | forward_call_id1_wow ]
  | match goal with |- context [remove_localdef_temp ?i ?L] => rewrite (hka5b_rlt i L) by reflexivity end;
    after_forward_call ].

(* kind 1: the 32-byte packet as one array around the flip of encrypted_data[j] *)
Lemma hka5b_join sh (hdr X: list val) p : Zlength hdr = 16 -> Zlength X = 16 ->
  field_compatible (tarray tuchar 32) [] p ->
  (data_at sh (tarray tuchar 16) hdr p * data_at sh (tarray tuchar 16) X (offset_val 16 p))%logic
  |-- data_at sh (tarray tuchar 32) (hdr ++ X) p.
Proof. intros. rewrite (hka5e_split sh 32 16 16 hdr X p) by auto. apply derives_refl. Qed.

Lemma hka5b_unjoin sh (hdr X: list val) p : Zlength hdr = 16 -> Zlength X = 16 ->
  field_compatible (tarray tuchar 32) [] p ->
  data_at sh (tarray tuchar 32) (hdr ++ X) p
  |-- (data_at sh (tarray tuchar 16) hdr p * data_at sh (tarray tuchar 16) X (offset_val 16 p))%logic.
Proof. intros. rewrite (hka5e_split sh 32 16 16 hdr X p) by auto. apply derives_refl. Qed.

Lemma hka5b_ze8 (w: int) : Vint (Int.zero_ext 8 w) = Vubyte (Byte.repr (Int.unsigned w)).
Proof.
  unfold Vubyte. f_equal. rewrite <- (Int.repr_unsigned (Int.zero_ext 8 w)).
  rewrite Int.zero_ext_mod by (change Int.zwordsize with 32; lia). rewrite Byte.unsigned_repr_eq. reflexivity.
Qed.

Lemma hka5b_znth {d: Inhabitant val} (hdr: list val) (T: list byte) j : Zlength hdr = 16 -> 0 <= j < Zlength T ->
  @Znth val d (16 + j) (hdr ++ map Vubyte T) = Vubyte (Znth j T).
Proof.
  intros Hh Hj. rewrite app_Znth2 by lia. rewrite Hh. replace (16 + j - 16) with j by lia.
  rewrite Znth_map by lia. reflexivity.
Qed.

Lemma hka5b_upd (hdr: list val) (T: list byte) j b : Zlength hdr = 16 -> 0 <= j < Zlength T ->
  upd_Znth (16 + j) (hdr ++ map Vubyte T) (Vubyte b) = hdr ++ map Vubyte (upd_Znth j T b).
Proof.
  intros Hh Hj. rewrite upd_Znth_app2 by (rewrite Zlength_map; lia). rewrite Hh.
  replace (16 + j - 16) with j by lia. rewrite upd_Znth_map. reflexivity.
Qed.

Ltac hka5b_contra := exfalso; first [ solve [apply Int.one_not_zero; assumption] | solve [auto] | solve [lia] | discriminate
  | match goal with Hx: Int.repr ?a = Int.repr ?b |- _ =>
      apply (f_equal Int.unsigned) in Hx; rewrite !Int.unsigned_repr in Hx by rep_lia; lia end ].

Lemma hka5_segB_ok {Espec: OracleKind} gv vrc vwm vsnap vkey key steps FR i top S bm ha ln kind enc pkt po rp :
  semax hka5_Delta (hka5_PB gv vrc vwm vsnap vkey key steps FR i top S bm ha ln kind enc pkt po rp) hka5_segB
    (overridePost (hka5_QB gv vrc vwm vsnap vkey key steps FR i top S bm ha ln pkt po rp)
                  (hka5_LR gv vrc vwm vsnap vkey key steps FR)).
Proof.
  unfold hka5_Delta, hka5_PB, hka5_QB, hka5_PC, hka5_segB, hka5_tA, hka5_tB, hka5_tl, hka5_lv, hka5_cw, hka5_fr,
    hka5_pkt.
  simpl app. abbreviate_semax. Intros.
  assert (Hf := H). destruct Hf as (Hi & Hs & Hk & Hc & Hha & Hln).
  forward_if (EX b9: int,
    PROP ()
    LOCAL (temp KA._t'9 (Vint b9); temp KA._kind (Vint (Int.repr kind)); temp KA._enc_len (Vlong (Int64.repr enc));
      temp KA._tot (Vlong (Int64.repr (16 + enc))); temp KA._pt_len (Vlong (Int64.repr 0));
      temp KA._pkt pkt; temp KA._pt_out po; temp KA._ref_pt rp;
      temp KA._i (Vlong (Int64.repr i)); temp KA._steps (Vlong (Int64.repr steps));
      temp KA._have_auth (Vint (Int.repr ha)); temp KA._last_nonce (Vlong (Int64.repr ln));
      lvar KA._rc ht4k_trc vrc; lvar KA._wm ht4k_twm vwm; lvar KA._snap ht4k_tsnap vsnap;
      lvar KA._key (tarray tuchar 32) vkey; gvars gv)
    SEP (malloc_token Ews (tarray tuchar (16 + enc)) pkt; data_at_ Ews (tarray tuchar (16 + enc)) pkt;
      hka5_mb po; hka5_mb rp; data_at Tsh ht4k_trc (ht4k_rc top bm) vrc; ht4k_wm Tsh top S vwm;
      data_at_ Tsh ht4k_tsnap vsnap; data_at Tsh (tarray tuchar 32) (map Vubyte key) vkey;
      mem_mgr gv; zero_page gv; ht4_minusp hka5_mp gv; FR)).
  - forward. Exists (if Int.eq (Int.repr ha) Int.zero then Int.zero else Int.one). entailer!.
  - forward. Exists Int.zero. entailer!.
  - Intros b9.
    forward_if (EX n: Z,
      PROP (0 <= n <= Int64.max_unsigned)
      LOCAL (temp KA._t'10 (Vlong (Int64.repr n)); temp KA._kind (Vint (Int.repr kind));
        temp KA._enc_len (Vlong (Int64.repr enc));
        temp KA._tot (Vlong (Int64.repr (16 + enc))); temp KA._pt_len (Vlong (Int64.repr 0));
        temp KA._pkt pkt; temp KA._pt_out po; temp KA._ref_pt rp;
        temp KA._i (Vlong (Int64.repr i)); temp KA._steps (Vlong (Int64.repr steps));
        temp KA._have_auth (Vint (Int.repr ha)); temp KA._last_nonce (Vlong (Int64.repr ln));
        lvar KA._rc ht4k_trc vrc; lvar KA._wm ht4k_twm vwm; lvar KA._snap ht4k_tsnap vsnap;
        lvar KA._key (tarray tuchar 32) vkey; gvars gv)
      SEP (malloc_token Ews (tarray tuchar (16 + enc)) pkt; data_at_ Ews (tarray tuchar (16 + enc)) pkt;
        hka5_mb po; hka5_mb rp; data_at Tsh ht4k_trc (ht4k_rc top bm) vrc; ht4k_wm Tsh top S vwm;
        data_at_ Tsh ht4k_tsnap vsnap; data_at Tsh (tarray tuchar 32) (map Vubyte key) vkey;
        mem_mgr gv; zero_page gv; ht4_minusp hka5_mp gv; FR)).
    + forward. Exists ln. entailer!.
    + forward_call tt. Intros x.
      unfold ht4k_wm. Intros wp.
      forward. forward.
      Exists (Int64.unsigned (Int64.sub (Int64.add (Int64.repr top)
        (Int64.repr (Int.unsigned (Int.modu (Int.repr x) (Int.repr 64))))) (Int64.repr (Int.signed (Int.repr 16))))).
      rewrite Int64.repr_unsigned. unfold ht4k_wm. Exists wp. entailer!.

    + Intros n.
      forward.
      pose proof (hka5b_enc_range _ _ H1) as He.
      assert_PROP (field_compatible (tarray tuchar (16 + enc)) [] pkt) as Hfc by entailer!.
      unfold data_at_ at 1, field_at_.
      change (default_val (nested_field_type (tarray tuchar (16 + enc)) [])) with (Zrepeat Vundef (16 + enc)).
      fold (data_at Ews (tarray tuchar (16 + enc)) (Zrepeat Vundef (16 + enc)) pkt).
      rewrite (hka5b_resize Ews (16 + enc) (Zrepeat Vundef (16 + enc))) by (rewrite Zlength_Zrepeat; lia).
      forward_call (Ews, pkt, 0, Zrepeat Vundef (16 + enc), Int.repr 4).
      { rewrite Zlength_Zrepeat by lia. lia. }
      rewrite Zlength_Zrepeat by lia.
      set (C1 := haead_splice 0 (le32_bytes (Int.repr 4)) (Zrepeat Vundef (16 + enc))).
      assert (L1: Zlength C1 = 16 + enc)
        by (unfold C1; rewrite hka5b_splice_len; rewrite ?hka5b_le32_len, ?Zlength_Zrepeat; lia).
      rewrite (hka5b_resize Ews (16 + enc) C1 pkt L1).
      forward_call tt. Intros x12.
      forward_call (Ews, pkt, 4, C1, Int.repr x12).
      rewrite L1.
      set (C2 := haead_splice 4 (le32_bytes (Int.repr x12)) C1).
      assert (L2: Zlength C2 = 16 + enc)
        by (unfold C2; rewrite hka5b_splice_len; rewrite ?hka5b_le32_len, ?L1; lia).
      rewrite (hka5b_resize Ews (16 + enc) C2 pkt L2).
      forward_call (Ews, pkt, 8, C2, n).
      rewrite L2.
      unfold C2, C1.
      rewrite (hka5b_hdr (Int.repr 4) (Int.repr x12) n enc) by lia.
      set (hdr := sublist 0 16 _).
      assert (Lh: Zlength hdr = 16) by (apply hka5b_hdr_len; lia).
      rewrite (hka5e_split Ews (16 + enc) 16 enc hdr (Zrepeat Vundef enc) pkt Lh)
        by (try rewrite Zlength_Zrepeat; auto; lia).
      clearbody hdr. clear L2 C2 L1 C1.
      Intros.
      assert (Hkind: kind = 0 \/ kind = 1 \/ kind = 2 \/ kind = 3) by (destruct H1; lia).
      destruct H1 as (Hkr & Hk3 & Hkn3).
      destruct Hkind as [-> | [-> | [-> | ->]]].
      * (* kind 0 *)
        assert (enc = 16) by (apply Hkn3; lia). subst enc.
        forward_if (temp KA._t'15 (Vint Int.one)).
        { forward. entailer!. }
        { hka5b_contra; lia. }
        forward_if (temp KA._t'16 (Vint Int.one)).
        { forward. entailer!. }
        { hka5b_contra; lia. }
        forward_if; [| hka5b_contra].
        sep_apply (data_at_data_at_ Ews (tarray tuchar 16) (Zrepeat Vundef 16) (offset_val 16 pkt)).
        forward_call (Ews, offset_val 16 pkt, Ews, nullval, @nil byte, Ews, nullval, @nil byte, n, Tsh, vkey, key, gv).
        { rewrite !hka5b_pb_nil. change (Zlength (@nil byte) + 16) with 16. cancel. }
        { rewrite Zlength_nil. split; rep_lia. }
        forward_if; [hka5b_contra |].
        forward.
        hka5b_post. Exists n hdr (aead_enc key n [] []).
        rewrite hka5b_enc_len, !hka5b_pb_nil. change (Zlength (@nil byte) + 16) with 16.
        entailer!.
      * (* kind 1: the authentic tag with one byte flipped *)
        assert (enc = 16) by (apply Hkn3; lia). subst enc.
        forward_if (temp KA._t'15 (Vint Int.one)).
        { exfalso. lia. }
        { forward. entailer!. }
        forward_if (temp KA._t'16 (Vint Int.one)).
        { forward. entailer!. }
        { hka5b_contra; lia. }
        forward_if; [| hka5b_contra].
        sep_apply (data_at_data_at_ Ews (tarray tuchar 16) (Zrepeat Vundef 16) (offset_val 16 pkt)).
        forward_call (Ews, offset_val 16 pkt, Ews, nullval, @nil byte, Ews, nullval, @nil byte, n, Tsh, vkey, key, gv).
        { rewrite !hka5b_pb_nil. change (Zlength (@nil byte) + 16) with 16. cancel. }
        rewrite !hka5b_pb_nil. change (Zlength (@nil byte) + 16) with 16.
        pose proof (hka5b_enc_len key n) as LT. revert LT.
        generalize (aead_enc key n [] []) as T. intros T LT.
        forward_if; [| hka5b_contra].
        apply -> seq_assoc. hka5b_call tt. Intros j0.
        forward; [entailer!; match goal with Hx: _ /\ _ = Int.mone |- _ => destruct Hx as [_ Hx]; discriminate Hx end |].
        hka5b_call tt. Intros v.
        assert (Ej: Int.signed (Int.mods (Int.repr j0) (Int.repr 16)) = j0 mod 16).
        { unfold Int.mods. rewrite (Int.signed_repr j0) by rep_lia. rewrite (Int.signed_repr 16) by rep_lia.
          rewrite Z.rem_mod_nonneg by lia. pose proof (Z.mod_pos_bound j0 16 ltac:(lia)).
          rewrite Int.signed_repr by rep_lia. reflexivity. }
        rewrite Ej. clear Ej.
        pose proof (Z.mod_pos_bound j0 16 ltac:(lia)) as Hj.
        set (j := j0 mod 16) in *. clearbody j.
        sep_apply (hka5b_join Ews hdr (map Vubyte T) pkt Lh ltac:(rewrite Zlength_map; auto) Hfc).
        forward.
        { entailer!. erewrite hka5b_znth by lia. unfold Vubyte. simpl.
          pose proof (Byte.unsigned_range_2 (Znth j T)). rewrite Int.unsigned_repr; rep_lia. }
        erewrite hka5b_znth by lia.
        forward.
        { entailer!. unfold Int.mods. rewrite (Int.signed_repr v) by rep_lia.
          rewrite (Int.signed_repr 255) by rep_lia. rewrite Z.rem_mod_nonneg by lia.
          pose proof (Z.mod_pos_bound v 255 ltac:(lia)). rewrite Int.signed_repr by rep_lia.
          split; [rep_lia |]. intros [_ E]. discriminate E. }
        match goal with |- context [Vint (Int.zero_ext 8 ?w)] =>
          rewrite (hka5b_ze8 w); set (b := Byte.repr (Int.unsigned w)) end.
        clearbody b.
        rewrite (hka5b_upd hdr T j b Lh) by lia.
        sep_apply (hka5b_unjoin Ews hdr (map Vubyte (upd_Znth j T b)) pkt Lh
          ltac:(rewrite Zlength_map, upd_Znth_Zlength; lia) Hfc).
        hka5b_post. Exists n hdr (upd_Znth j T b).
        rewrite upd_Znth_Zlength by lia. rewrite LT.
        entailer!.
      * (* kind 2 *)
        assert (enc = 16) by (apply Hkn3; lia). subst enc.
        forward_if (temp KA._t'15 (Vint Int.zero)).
        { hka5b_contra; lia. }
        { forward. entailer!. }
        forward_if (temp KA._t'16 (Vint Int.one)).
        { hka5b_contra; lia. }
        { forward. entailer!. }
        forward_if; [| hka5b_contra].
        sep_apply (data_at_data_at_ Ews (tarray tuchar 16) (Zrepeat Vundef 16) (offset_val 16 pkt)).
        forward_call (Ews, offset_val 16 pkt, Ews, nullval, @nil byte, Ews, nullval, @nil byte, n, Tsh, vkey, key, gv).
        { rewrite !hka5b_pb_nil. change (Zlength (@nil byte) + 16) with 16. cancel. }
        all: try (rewrite Zlength_nil; split; rep_lia).
        forward_if; [hka5b_contra |].
        forward.
        hka5b_post. Exists n hdr (aead_enc key n [] []).
        rewrite hka5b_enc_len, !hka5b_pb_nil. change (Zlength (@nil byte) + 16) with 16.
        entailer!.
      * (* kind 3: enc_len < 16 random bytes *)
        assert (Henc: 0 <= enc < 16) by (apply Hk3; reflexivity).
        forward_if (temp KA._t'15 (Vint Int.zero)).
        { hka5b_contra; lia. }
        { forward. entailer!. }
        forward_if (temp KA._t'16 (Vint Int.zero)).
        { hka5b_contra; lia. }
        { forward. entailer!. }
        forward_if; [hka5b_contra |].
        sep_apply (data_at_data_at_ Ews (tarray tuchar enc) (Zrepeat Vundef enc) (offset_val 16 pkt)).
        forward_call (offset_val 16 pkt, enc, Ews).
        Intros bs.
        hka5b_post. Exists n hdr (map Byte.repr bs).
        rewrite <- (hka5b_bytes bs) by assumption. rewrite Zlength_map. 
        match goal with Hl: Zlength bs = enc |- _ => rewrite Hl end.
        entailer!.
Qed.
