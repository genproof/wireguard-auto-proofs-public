(*
   - the sk_buff: skb_rep (Cookie.CS) = the protocol field at the world HRX * the address / port
     arrays as hbytes (HCS) * the rest;
   - the local buffer u8 buf[18] holding a prefix A: pieces for bytes_copy / m_mac. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_spec.
Require WgNoise.proof.libc.libc_bytes.
Local Open Scope logic.

#[local] Instance hrx5_help_cce_C : change_composite_env Cookie.CS HRX.
Proof. make_cs_preserve Cookie.CS HRX. Defined.

Definition hrx5_help_fa4 (p: val) : val :=
  @field_address HRX t_skb (DOT HRC._ip4 DOT HRC._saddr DOT HRC._s_addr) p.
Definition hrx5_help_fa16 (p: val) : val :=
  @field_address HRX t_skb (DOT HRC._ip6 DOT HRC._saddr DOT HRC._s6_addr) p.
Definition hrx5_help_fa2 (p: val) : val :=
  @field_address HRX t_skb (DOT HRC._udp DOT HRC._source) p.

Section W.
#[local] Existing Instance HRX.

Definition hrx5_help_skb_rest (sh: share) (p: val) (s: skb) : mpred :=
  field_at sh t_skb (DOT HRC._data) (sk_data s) p * field_at sh t_skb (DOT HRC._len) (Vint (sk_len s)) p *
  spacer sh 36 40 p.

Lemma hrx5_help_skb_open sh p s :
  skb_ok s ->
  skb_rep sh p s =
  field_at sh t_skb (DOT HRC._protocol) (Vint (Int.repr (sk_proto s))) p *
  hbytes sh (sk_ip4 s) (hrx5_help_fa4 p) * hbytes sh (sk_ip6 s) (hrx5_help_fa16 p) *
  hbytes sh (sk_port s) (hrx5_help_fa2 p) * hrx5_help_skb_rest sh p s.
Proof.
  intros OK. pose proof OK as (Hpr & H4 & H6 & H2).
  unfold skb_rep. rewrite prop_true_andp by auto.
  destruct s as [d l pr a4 a6 a2]; simpl in *.
  pose (v := (d, (Vint l, (Vint (Int.repr pr), (bytes a4, (bytes a6, bytes a2))))) : @reptype HRX t_skb).
  rewrite (@data_at_change_composite Cookie.CS HRX _ sh t_skb _ v); [| apply JMeq_refl | prove_cs_preserve_type].
  unfold hrx5_help_fa4, hrx5_help_fa16, hrx5_help_fa2, hrx5_help_skb_rest, v, hbytes.
  rewrite H4, H6, H2.
  rewrite <- !(@WgNoise.proof.libc.libc_bytes.data_at_tarray_tuchar_cs HRX HCS).
  unfold_data_at (data_at sh t_skb _ p).
  unfold_field_at 4%nat. unfold_field_at 4%nat. unfold_field_at 5%nat. unfold_field_at 5%nat.
  unfold_field_at 6%nat.
  rewrite (field_at_data_at sh t_skb [StructField HRC._s_addr; StructField HRC._saddr; StructField HRC._ip4]).
  rewrite (field_at_data_at sh t_skb [StructField HRC._s6_addr; StructField HRC._saddr; StructField HRC._ip6]).
  rewrite (field_at_data_at sh t_skb [StructField HRC._source; StructField HRC._udp]).
  apply pred_ext; cancel.
Qed.

(* the same for skb_src_rep *)
Definition hrx5_help_skb_rest2 (sh: share) (p dv lv: val) : mpred :=
  field_at sh t_skb (DOT HRC._data) dv p * field_at sh t_skb (DOT HRC._len) lv p * spacer sh 36 40 p.

Lemma hrx5_help_skb_open2 sh p dv lv s :
  skb_ok s ->
  skb_src_rep sh p dv lv s =
  field_at sh t_skb (DOT HRC._protocol) (Vint (Int.repr (sk_proto s))) p *
  hbytes sh (sk_ip4 s) (hrx5_help_fa4 p) * hbytes sh (sk_ip6 s) (hrx5_help_fa16 p) *
  hbytes sh (sk_port s) (hrx5_help_fa2 p) * hrx5_help_skb_rest2 sh p dv lv.
Proof.
  intros OK. pose proof OK as (Hpr & H4 & H6 & H2).
  unfold skb_src_rep. rewrite prop_true_andp by auto.
  destruct s as [d l pr a4 a6 a2]; simpl in *.
  pose (v := (dv, (lv, (Vint (Int.repr pr), (bytes a4, (bytes a6, bytes a2))))) : @reptype HRX t_skb).
  rewrite (@data_at_change_composite Cookie.CS HRX _ sh t_skb _ v); [| apply JMeq_refl | prove_cs_preserve_type].
  unfold hrx5_help_fa4, hrx5_help_fa16, hrx5_help_fa2, hrx5_help_skb_rest2, v, hbytes.
  rewrite H4, H6, H2.
  rewrite <- !(@WgNoise.proof.libc.libc_bytes.data_at_tarray_tuchar_cs HRX HCS).
  unfold_data_at (data_at sh t_skb _ p).
  unfold_field_at 4%nat. unfold_field_at 4%nat. unfold_field_at 5%nat. unfold_field_at 5%nat.
  unfold_field_at 6%nat.
  rewrite (field_at_data_at sh t_skb [StructField HRC._s_addr; StructField HRC._saddr; StructField HRC._ip4]).
  rewrite (field_at_data_at sh t_skb [StructField HRC._s6_addr; StructField HRC._saddr; StructField HRC._ip6]).
  rewrite (field_at_data_at sh t_skb [StructField HRC._source; StructField HRC._udp]).
  apply pred_ext; cancel.
Qed.

(* the buffer holding the prefix A *)
Definition hrx5_help_bufv (A: list byte) : list val := bytes A ++ Zrepeat Vundef (18 - Zlength A).

Definition hrx5_help_tail (m: Z) (buf: val) : mpred :=
  data_at_ Tsh (tarray tuchar (18 - m)) (offset_val m buf).

Lemma hrx5_help_buf0 buf : data_at_ Tsh (tarray tuchar 18) buf = data_at Tsh (tarray tuchar 18) (hrx5_help_bufv []) buf.
Proof. reflexivity. Qed.

Lemma hrx5_help_nfo i : nested_field_offset (Tarray tuchar 18 noattr) (SUB i) = i.
Proof. unfold nested_field_offset; simpl. lia. Qed.

Lemma hrx5_help_buf_open A k buf :
  0 <= k -> Zlength A + k <= 18 -> field_compatible (tarray tuchar 18) [] buf ->
  data_at Tsh (tarray tuchar 18) (hrx5_help_bufv A) buf |--
  hbytes Tsh A buf * hout Tsh k (offset_val (Zlength A) buf) * hrx5_help_tail (Zlength A + k) buf.
Proof.
  intros Hk HA FC.
  assert (0 <= Zlength A) by apply Zlength_nonneg.
  unfold hrx5_help_bufv, hrx5_help_tail, hbytes, hout.
  rewrite (split3_data_at_Tarray_tuchar Tsh 18 (Zlength A) (Zlength A + k)) by
    (try lia; autorewrite with sublist; unfold bytes; rewrite Zlength_map; lia).
  rewrite !field_address0_offset by auto with field_compatible.
  rewrite !hrx5_help_nfo.
  unfold bytes.
  rewrite sublist_app1 by (rewrite ?Zlength_map; lia).
  rewrite sublist_same by (rewrite ?Zlength_map; lia).
  rewrite sublist_app2 by (rewrite ?Zlength_map; lia).
  rewrite sublist_app2 by (rewrite ?Zlength_map; lia).
  rewrite Zlength_map.
  rewrite !sublist_Zrepeat by lia.
  replace (Zlength A + k - Zlength A - (Zlength A - Zlength A)) with k by lia.
  replace (Zlength A + k - Zlength A) with k by lia.
  replace (18 - Zlength A - k) with (18 - (Zlength A + k)) by lia.
  rewrite <- (@WgNoise.proof.libc.libc_bytes.data_at_tarray_tuchar_cs HRX HCS Tsh (Zlength A)).
  rewrite <- !(@WgNoise.proof.libc.libc_bytes.data_at__tarray_tuchar_cs HRX HCS).
  rewrite !data_at__eq. apply derives_refl.
Qed.

Lemma hrx5_help_buf_close A X buf :
  Zlength A + Zlength X <= 18 -> field_compatible (tarray tuchar 18) [] buf ->
  hbytes Tsh A buf * hbytes Tsh X (offset_val (Zlength A) buf) * hrx5_help_tail (Zlength A + Zlength X) buf |--
  data_at Tsh (tarray tuchar 18) (hrx5_help_bufv (A ++ X)) buf.
Proof.
  intros HA FC.
  assert (0 <= Zlength A) by apply Zlength_nonneg.
  assert (0 <= Zlength X) by apply Zlength_nonneg.
  unfold hrx5_help_bufv, hrx5_help_tail, hbytes.
  rewrite (split3_data_at_Tarray_tuchar Tsh 18 (Zlength A) (Zlength A + Zlength X)) by
    (try lia; autorewrite with sublist; unfold bytes; rewrite ?map_app, ?Zlength_app, ?Zlength_map; lia).
  rewrite !field_address0_offset by auto with field_compatible.
  rewrite !hrx5_help_nfo.
  unfold bytes. rewrite map_app, <- app_assoc.
  assert (E1: sublist 0 (Zlength A) (map Vubyte A ++ map Vubyte X ++ Zrepeat Vundef (18 - Zlength (A ++ X))) = map Vubyte A) by list_solve.
  assert (E2: sublist (Zlength A) (Zlength A + Zlength X) (map Vubyte A ++ map Vubyte X ++ Zrepeat Vundef (18 - Zlength (A ++ X))) = map Vubyte X) by list_solve.
  assert (E3: sublist (Zlength A + Zlength X) 18 (map Vubyte A ++ map Vubyte X ++ Zrepeat Vundef (18 - Zlength (A ++ X))) = Zrepeat Vundef (18 - (Zlength A + Zlength X))) by list_solve.
  rewrite E1, E2, E3.
  replace (Zlength A + Zlength X - Zlength A) with (Zlength X) by lia.
  rewrite <- (@WgNoise.proof.libc.libc_bytes.data_at_tarray_tuchar_cs HRX HCS Tsh (Zlength A)).
  rewrite <- (@WgNoise.proof.libc.libc_bytes.data_at_tarray_tuchar_cs HRX HCS Tsh (Zlength X)).
  rewrite !data_at__eq. apply derives_refl.
Qed.

Lemma hrx5_help_buf_open0 k buf :
  0 <= k <= 18 -> field_compatible (tarray tuchar 18) [] buf ->
  data_at Tsh (tarray tuchar 18) (hrx5_help_bufv []) buf |-- hout Tsh k buf * hrx5_help_tail k buf.
Proof.
  intros Hk FC.
  eapply derives_trans; [apply (hrx5_help_buf_open [] k buf); auto; try rewrite Zlength_nil; lia |].
  rewrite Zlength_nil, Z.add_0_l, isptr_offset_val_zero by auto with field_compatible.
  unfold hbytes. rewrite Zlength_nil.
  sep_apply (data_at_zero_array_inv (cs:=HCS) Tsh tuchar (bytes []) buf); auto. cancel.
Qed.

Lemma hrx5_help_buf_close0 X buf :
  Zlength X <= 18 -> field_compatible (tarray tuchar 18) [] buf ->
  hbytes Tsh X buf * hrx5_help_tail (Zlength X) buf |-- data_at Tsh (tarray tuchar 18) (hrx5_help_bufv X) buf.
Proof.
  intros HX FC.
  eapply derives_trans; [| apply (hrx5_help_buf_close [] X buf); auto; try rewrite Zlength_nil; lia].
  rewrite Zlength_nil, Z.add_0_l, isptr_offset_val_zero by auto with field_compatible.
  unfold hbytes at 2. rewrite Zlength_nil.
  sep_apply (data_at_zero_array (cs:=HCS) Tsh tuchar (bytes []) buf); auto with field_compatible. cancel.
Qed.

Lemma hrx5_help_hin sh bs p : Zlength bs <> 0 -> hin sh bs p = hbytes sh bs p.
Proof. intros. unfold hin. rewrite if_false; auto. Qed.

Lemma hrx5_help_hout0 sh p : hout sh 0 p = hbytes sh [] p.
Proof. unfold hout, hbytes. rewrite data_at__eq. reflexivity. Qed.

End W.

(* draw_macs: the image split at len - 32 / len - 16; the local arrays at HRX as hout / hbytes *)
Section H.
#[local] Existing Instance HCS.

Lemma hrx5_help_split2 sh P X p :
  field_compatible (tarray tuchar (Zlength P + Zlength X)) [] p ->
  hbytes sh (P ++ X) p = hbytes sh P p * hbytes sh X (offset_val (Zlength P) p).
Proof.
  intros FC.
  assert (0 <= Zlength P) by apply Zlength_nonneg.
  assert (0 <= Zlength X) by apply Zlength_nonneg.
  unfold hbytes. rewrite Zlength_app.
  rewrite (@split2_data_at_Tarray_tuchar HCS sh (Zlength P + Zlength X) (Zlength P)) by
    (try lia; unfold bytes; rewrite Zlength_map, Zlength_app; lia).
  rewrite field_address0_offset by auto with field_compatible.
  replace (nested_field_offset _ _) with (Zlength P) by (unfold nested_field_offset; simpl; lia).
  replace (Zlength P + Zlength X - Zlength P) with (Zlength X) by lia.
  unfold bytes. rewrite map_app.
  rewrite sublist_app1 by (rewrite ?Zlength_map; lia).
  rewrite sublist_same by (rewrite ?Zlength_map; lia).
  rewrite sublist_app2 by (rewrite ?Zlength_map; lia).
  rewrite Zlength_map, Z.sub_diag.
  replace (Zlength P + Zlength X - Zlength P) with (Zlength (map Vubyte X)) by (rewrite Zlength_map; lia).
  rewrite sublist_same by lia. reflexivity.
Qed.

Lemma hrx5_help_hin_split sh A p :
  hbytes sh A p = hin sh A p * (if Z.eq_dec (Zlength A) 0 then hbytes sh A p else emp).
Proof. unfold hin. destruct (Z.eq_dec (Zlength A) 0); rewrite ?emp_sepcon, ?sepcon_emp; reflexivity. Qed.

Lemma hrx5_help_lout sh n p : @data_at_ HRX sh (tarray tuchar n) p = hout sh n p.
Proof. unfold hout. apply (@WgNoise.proof.libc.libc_bytes.data_at__tarray_tuchar_cs HRX HCS). Qed.

Lemma hrx5_help_hbytes_out sh A p : hbytes sh A p |-- hout sh (Zlength A) p.
Proof. unfold hbytes, hout. apply data_at_data_at_. Qed.

End H.
