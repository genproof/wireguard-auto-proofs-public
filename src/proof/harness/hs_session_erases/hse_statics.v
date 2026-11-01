(* The law hs_session_erases: the harness's own static functions zero and erased (harness/hs_session_erases.c).

   zero(bytes, n) returns 1 exactly when bytes[0..n-1] are all zero; erased(h) returns 1 exactly when the
   handshake at h is in state HANDSHAKE_ZEROED with its ephemeral private key, remote ephemeral and chaining key
   all zero (hse_erasedb), else 0.  Their bodies are proved in the compspecs of the harness (HCS), with only
   their callees in the context, and lifted into the law's unit with the rest of its piece. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require WgNoise.contracts.hs_session_erases.
Require WgNoise.harness.hs_session_erases.code.
Local Open Scope logic.

Module C := WgNoise.harness.hs_session_erases.code.

(* the compspecs of the harness hs_session_erases *)
Definition HCS : compspecs := WgNoise.contracts.hs_session_erases.Harness.CS.

(* the bytes are all zero *)
Definition hse_zerob (l: list byte) : bool := forallb (fun c => Byte.eq c Byte.zero) l.

(* the handshake is erased in the sense of the law *)
Definition hse_erasedb (H: handshake) : bool :=
  Int.eq (hs_state H) HS_ZEROED && hse_zerob (hs_eph H) && hse_zerob (hs_reph H) && hse_zerob (hs_ck H).

Section Specs.
#[local] Existing Instance HCS.

Definition zero_spec :=
  DECLARE C._zero
  WITH sh: share, b: val, l: list byte
  PRE [ tptr tuchar, tulong ]
    PROP (readable_share sh; Zlength l <= Int64.max_unsigned)
    PARAMS (b; Vlong (Int64.repr (Zlength l)))
    SEP (bytes_at sh l b)
  POST [ tint ]
    PROP () RETURN (Vint (if hse_zerob l then Int.one else Int.zero))
    SEP (bytes_at sh l b).

Definition erased_spec :=
  DECLARE C._erased
  WITH sh: share, h: val, H: handshake
  PRE [ tptr t_hs ]
    PROP (readable_share sh)
    PARAMS (h)
    SEP (hs_rep sh h H)
  POST [ tint ]
    PROP () RETURN (Vint (if hse_erasedb H then Int.one else Int.zero))
    SEP (hs_rep sh h H).

End Specs.

Definition hse_V : varspecs := QPvarspecs WgNoise.contracts.hs_session_erases.whole_prog.

(* The kernel structs and arrays have the same layout in the harness's compspecs as in noise.c's. *)
#[local] Instance hse_cce : change_composite_env Noise.CS HCS.
Proof. make_cs_preserve Noise.CS HCS. Defined.

(* A byte buffer, written in noise.c's compspecs, is the same array in the harness's. *)
Lemma hse_bytes_at_HCS sh l b :
  bytes_at sh l b = @data_at HCS sh (tarray tuchar (Zlength l)) (bytes l) b.
Proof.
  unfold bytes_at. erewrite (@data_at_change_composite Noise.CS HCS _ sh (tarray tuchar (Zlength l)));
    [reflexivity | apply JMeq_refl | reflexivity].
Qed.

(* A nonzero byte makes the buffer not all zero. *)
Lemma hse_zerob_false l i :
  0 <= i < Zlength l -> Byte.unsigned (Znth i l) <> 0 -> hse_zerob l = false.
Proof.
  intros Hi Hn. destruct (hse_zerob l) eqn:E; [| reflexivity]. exfalso.
  unfold hse_zerob in E. rewrite forallb_forall in E.
  specialize (E (Znth i l) ltac:(apply Znth_In; lia)).
  apply Byte.same_if_eq in E. rewrite E in Hn. apply Hn. reflexivity.
Qed.

(* A zero prefix extended by a zero byte is a zero prefix. *)
Lemma hse_zerob_step l i :
  0 <= i < Zlength l -> hse_zerob (sublist 0 i l) = true -> Byte.unsigned (Znth i l) = 0 ->
  hse_zerob (sublist 0 (i + 1) l) = true.
Proof.
  intros Hi Hp Hz. rewrite (sublist_split 0 i (i + 1)) by lia. rewrite sublist_len_1 by lia.
  unfold hse_zerob in *. rewrite forallb_app, Hp. simpl.
  replace (Znth i l) with Byte.zero by (rewrite <- (Byte.repr_unsigned (Znth i l)), Hz; reflexivity).
  reflexivity.
Qed.

(* zero's body: the loop keeps "the bytes read so far are all zero" and returns 0 at the first nonzero one. *)
Lemma hse_body_zero : @semax_body hse_V [] HCS C.f_zero zero_spec.
Proof.
  start_function.
  rewrite hse_bytes_at_HCS.
  forward_for_simple_bound (Zlength l) (EX i: Z,
    PROP (hse_zerob (sublist 0 i l) = true)
    LOCAL (temp C._bytes b; temp C._n (Vlong (Int64.repr (Zlength l))))
    SEP (@data_at HCS sh (tarray tuchar (Zlength l)) (bytes l) b)).
  - entailer!.
  - cbv beta. Intros. forward.
    { entailer!. unfold Vubyte; simpl. pose proof (Byte.unsigned_range_2 (Znth i l)).
      rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    unfold bytes. rewrite Znth_map by lia.
    forward_if.
    + (* a nonzero byte: zero returns 0 *)
      forward. rewrite (hse_zerob_false l i) by assumption. rewrite hse_bytes_at_HCS. entailer!.
    + forward. entailer!. apply hse_zerob_step; assumption.
  - (* every byte is zero: zero returns 1 *)
    forward. rewrite sublist_same in * by lia. rewrite hse_bytes_at_HCS.
    match goal with Hz: hse_zerob l = true |- _ => rewrite Hz end. entailer!.
Qed.

Section NoiseFields.
#[local] Existing Instance Noise.CS.

(* The fields of a handshake that erased does not read, with its lock lk. *)
Definition hse_rest (sh: share) (h: val) (H: handshake) (lk: val) : mpred :=
  field_at sh t_hs [StructField I._last_initiation_consumption] (Vlong (hs_lic H)) h *
  field_at sh t_hs [StructField I._static_identity] (hs_sid H) h *
  field_at sh t_hs [StructField I._remote_static] (bytes (hs_rstatic H)) h *
  field_at sh t_hs [StructField I._precomputed_static_static] (bytes (hs_ss H)) h *
  field_at sh t_hs [StructField I._preshared_key] (bytes (hs_psk H)) h *
  field_at sh t_hs [StructField I._hash] (bytes (hs_hash H)) h *
  field_at sh t_hs [StructField I._latest_timestamp] (bytes (hs_ts H)) h *
  field_at sh t_hs [StructField I._remote_index] (Vint (hs_rindex H)) h *
  field_at sh t_hs [StructField I._lock] lk h *
  spacer sh 36 40 h * spacer sh 300 304 h.

(* The address of a field of a handshake is the same in the harness's compspecs as in noise.c's. *)
Lemma hse_field_address f h :
  field_address t_hs [StructField f] h = @field_address HCS t_hs [StructField f] h.
Proof.
  unfold field_address.
  pose proof (@field_compatible_change_composite Noise.CS HCS _ t_hs eq_refl [StructField f] h) as E.
  destruct (@field_compatible_dec Noise.CS t_hs [StructField f] h) as [A|A];
  destruct (@field_compatible_dec HCS t_hs [StructField f] h) as [B|B]; try tauto.
Qed.

(* A 32-byte field of a handshake is a byte buffer at the field's address. *)
Lemma hse_field_eph sh l h : Zlength l = 32 ->
  field_at sh t_hs [StructField I._ephemeral_private] (bytes l) h =
  bytes_at sh l (@field_address HCS t_hs [StructField I._ephemeral_private] h).
Proof. intros E. rewrite field_at_data_at, hse_field_address. unfold bytes_at. rewrite E. reflexivity. Qed.
Lemma hse_field_reph sh l h : Zlength l = 32 ->
  field_at sh t_hs [StructField I._remote_ephemeral] (bytes l) h =
  bytes_at sh l (@field_address HCS t_hs [StructField I._remote_ephemeral] h).
Proof. intros E. rewrite field_at_data_at, hse_field_address. unfold bytes_at. rewrite E. reflexivity. Qed.
Lemma hse_field_ck sh l h : Zlength l = 32 ->
  field_at sh t_hs [StructField I._chaining_key] (bytes l) h =
  bytes_at sh l (@field_address HCS t_hs [StructField I._chaining_key] h).
Proof. intros E. rewrite field_at_data_at, hse_field_address. unfold bytes_at. rewrite E. reflexivity. Qed.

(* A handshake, opened for erased: its state field in the harness's compspecs (erased loads it), its three
   32-byte buffers that erased passes to zero, and the rest. *)
Lemma hse_hs_rep_open sh h H :
  hs_rep sh h H =
  EX lk: val, !! hs_ok H &&
    (@field_at HCS sh t_hs [StructField I._state] (Vint (hs_state H)) h *
     bytes_at sh (hs_eph H) (@field_address HCS t_hs [StructField I._ephemeral_private] h) *
     bytes_at sh (hs_reph H) (@field_address HCS t_hs [StructField I._remote_ephemeral] h) *
     bytes_at sh (hs_ck H) (@field_address HCS t_hs [StructField I._chaining_key] h) *
     hse_rest sh h H lk).
Proof.
  unfold hs_rep, hse_rest. apply pred_ext.
  - Intros lk. Exists lk. pose proof H0 as (E1 & _ & E3 & _ & _ & _ & E7 & _).
    rewrite <- (hse_field_eph sh _ h E1), <- (hse_field_reph sh _ h E3), <- (hse_field_ck sh _ h E7).
    erewrite <- (@field_at_change_composite Noise.CS HCS _ sh t_hs [StructField I._state]);
      [| apply JMeq_refl | reflexivity].
    entailer!.
  - Intros lk. pose proof H0 as (E1 & _ & E3 & _ & _ & _ & E7 & _).
    rewrite <- (hse_field_eph sh _ h E1), <- (hse_field_reph sh _ h E3), <- (hse_field_ck sh _ h E7).
    erewrite <- (@field_at_change_composite Noise.CS HCS _ sh t_hs [StructField I._state]);
      [| apply JMeq_refl | reflexivity].
    entailer!. Exists lk. cancel.
Qed.

End NoiseFields.

(* A field of a handshake whose state field is accessible is accessible too. *)
Ltac hse_fc :=
  match goal with Hf: field_compatible t_hs [StructField I._state] _ |- _ =>
    destruct Hf as (A1 & A2 & A3 & A4 & A5 & A6); repeat split; auto;
    compute; repeat first [left; reflexivity | right] end.

(* The values of the short-circuit temporaries: a case analysis on the four tests, against the test of the
   previous conjunct. *)
Ltac hse_cases :=
  match goal with |- context [hs_state ?H] =>
    destruct (Int.eq (hs_state H) HS_ZEROED), (hse_zerob (hs_eph H)), (hse_zerob (hs_reph H)),
      (hse_zerob (hs_ck H)); simpl in *; try reflexivity;
    match goal with
    | Hc: Int.repr 0 <> Int.zero |- _ => exfalso; apply Hc; reflexivity
    | Hc: Int.zero <> Int.zero |- _ => exfalso; apply Hc; reflexivity
    | Hc: Int.one = Int.zero |- _ => exfalso; apply Int.one_not_zero; exact Hc
    end
  end.

(* erased's body: the state test and the three calls of zero, joined by &&. *)
Lemma hse_body_erased : @semax_body hse_V [zero_spec] HCS C.f_erased erased_spec.
Proof.
  start_function.
  rewrite hse_hs_rep_open. Intros lk.
  pose proof H0 as (E1 & _ & E3 & _ & _ & _ & E7 & _).
  forward.
  forward_if (PROP () LOCAL (temp C._t'1 (Vint (if andb (Int.eq (hs_state H) HS_ZEROED) (hse_zerob (hs_eph H))
                                                then Int.one else Int.zero)); temp C._h h)
    SEP (@field_at HCS sh t_hs [StructField I._state] (Vint (hs_state H)) h;
         bytes_at sh (hs_eph H) (@field_address HCS t_hs [StructField I._ephemeral_private] h);
         bytes_at sh (hs_reph H) (@field_address HCS t_hs [StructField I._remote_ephemeral] h);
         bytes_at sh (hs_ck H) (@field_address HCS t_hs [StructField I._chaining_key] h);
         hse_rest sh h H lk)).
  - forward_call (sh, @field_address HCS t_hs [StructField I._ephemeral_private] h, hs_eph H).
    { entailer!. simpl. rewrite E1. f_equal. unfold field_address. rewrite if_true; [reflexivity |]. hse_fc. }
    forward.
    entailer!. rewrite H1. destruct (hse_zerob (hs_eph H)); reflexivity.
  - forward. entailer!. unfold HS_ZEROED. rewrite Int.eq_false by exact H1. reflexivity.
  - (* the remote ephemeral, when the state and the ephemeral private key are erased *)
    forward_if (PROP () LOCAL (temp C._t'3 (Vint (if andb (andb (Int.eq (hs_state H) HS_ZEROED)
                                  (hse_zerob (hs_eph H))) (hse_zerob (hs_reph H)) then Int.one else Int.zero));
                               temp C._h h)
    SEP (@field_at HCS sh t_hs [StructField I._state] (Vint (hs_state H)) h;
         bytes_at sh (hs_eph H) (@field_address HCS t_hs [StructField I._ephemeral_private] h);
         bytes_at sh (hs_reph H) (@field_address HCS t_hs [StructField I._remote_ephemeral] h);
         bytes_at sh (hs_ck H) (@field_address HCS t_hs [StructField I._chaining_key] h);
         hse_rest sh h H lk)).
    + forward_call (sh, @field_address HCS t_hs [StructField I._remote_ephemeral] h, hs_reph H).
      { entailer!. simpl. rewrite E3. f_equal. unfold field_address. rewrite if_true; [reflexivity |]. hse_fc. }
      forward. entailer!. hse_cases.
    + forward. entailer!. hse_cases.
    + (* the chaining key, when the state and both ephemerals are erased *)
      forward_if (PROP () LOCAL (temp C._t'5 (Vint (if hse_erasedb H then Int.one else Int.zero)); temp C._h h)
    SEP (@field_at HCS sh t_hs [StructField I._state] (Vint (hs_state H)) h;
         bytes_at sh (hs_eph H) (@field_address HCS t_hs [StructField I._ephemeral_private] h);
         bytes_at sh (hs_reph H) (@field_address HCS t_hs [StructField I._remote_ephemeral] h);
         bytes_at sh (hs_ck H) (@field_address HCS t_hs [StructField I._chaining_key] h);
         hse_rest sh h H lk)).
      * forward_call (sh, @field_address HCS t_hs [StructField I._chaining_key] h, hs_ck H).
        { entailer!. simpl. rewrite E7. f_equal. unfold field_address. rewrite if_true; [reflexivity |]. hse_fc. }
        forward. entailer!. unfold hse_erasedb. hse_cases.
      * forward. entailer!. unfold hse_erasedb. hse_cases.
      * forward. rewrite hse_hs_rep_open. Exists lk. entailer!.
Qed.

(* the bodies, each with its callees only *)
Theorem hse_statics_bodies :
  @semax_body hse_V [] HCS C.f_zero zero_spec /\
  @semax_body hse_V [zero_spec] HCS C.f_erased erased_spec.
Proof. split; [apply hse_body_zero | apply hse_body_erased]. Qed.
