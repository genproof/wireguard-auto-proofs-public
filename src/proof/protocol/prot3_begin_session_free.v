(* Helper lemma of the group begin_session: a keypair with its (unhashed) entry is
   the whole kzalloc'd block, for kfree_sensitive. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.

#[local] Existing Instance Noise.CS.
Local Open Scope logic.

Lemma prot3_begin_session_kp_free CSw k K E :
  keypair_rep CSw k K * entry_out Ews k E |--
  @malloc_token CSw Ews (tarray tuchar SIZEOF_KEYPAIR) k * data_at_ Ews (tarray tuchar SIZEOF_KEYPAIR) k.
Proof.
  unfold keypair_rep, entry_out, entry_at. Intros lk r.
  assert (FE: data_at Ews t_entry_s (entry_val E nullval false) k =
              field_at Ews t_kp (DOT I._entry) (entry_val E nullval false) k).
  { rewrite field_at_data_at. f_equal. rewrite field_compatible_field_address by auto with field_compatible.
    simpl. rewrite isptr_offset_val_zero; auto. apply H. }
  rewrite FE; clear FE.
  cancel.
  rewrite <- (@memory_block_data_at__tarray_tuchar_eq CSw) by (unfold SIZEOF_KEYPAIR; rep_lia).
  assert (D: @data_at_ Noise.CS Ews t_kp k |-- memory_block Ews SIZEOF_KEYPAIR k).
  { rewrite data_at__memory_block. Intros. apply derives_refl. }
  eapply derives_trans; [| apply D]. clear D.
  unfold_data_at (@data_at_ Noise.CS Ews t_kp k).
  cancel.
Qed.
