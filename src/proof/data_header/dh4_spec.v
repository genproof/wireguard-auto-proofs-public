(* the unit DataHeader (patch/data_header.c, DEVIATIONS S24):
   receive.c's length gate validate_header_len as wg_validate_header_len(type, len).  Its model, its one
   specification (no memory: a function of the type word and the length) and its piece.

   dh4_len type len = the header length validate_header_len returns, 0 = reject:
     len < sizeof(message_header) = 4                       -> 0
     type = MESSAGE_DATA (4) and len >= MESSAGE_MINIMUM_LENGTH (= sizeof(message_data) + 16 = 32)
                                                            -> sizeof(message_data) = 16
     type = MESSAGE_HANDSHAKE_INITIATION (1) and len = 148  -> 148
     type = MESSAGE_HANDSHAKE_RESPONSE (2) and len = 92     -> 92
     type = MESSAGE_HANDSHAKE_COOKIE (3) and len = 64       -> 64
     else                                                   -> 0 *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require WgNoise.units.DataHeader.
Require Import WgNoise.proof.common.pieces.
Require WgNoise.data_header.code.

Local Open Scope Z_scope.

Definition _wg_validate_header_len : ident := WgNoise.data_header.code._wg_validate_header_len.

Definition dh4_len (type len: Z) : Z :=
  if len <? 4 then 0
  else if andb (type =? 4) (32 <=? len) then 16
  else if andb (type =? 1) (len =? 148) then 148
  else if andb (type =? 2) (len =? 92) then 92
  else if andb (type =? 3) (len =? 64) then 64
  else 0.

(* no memory: the specification does not depend on the compspecs *)
Definition wg_validate_header_len_spec :=
  DECLARE _wg_validate_header_len
  WITH type: Z, len: Z
  PRE [ tuint, tulong ]
    PROP (0 <= type <= Int.max_unsigned; 0 <= len <= Int64.max_unsigned)
    PARAMS (Vint (Int.repr type); Vlong (Int64.repr len))
    SEP ()
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr (dh4_len type len))) SEP ().

(* the unit *)
Definition u_data_header : unit_ctx :=
  mk_unit DataHeader.CS (QPvarspecs DataHeader.qp) WgNoise.data_header.code.prog.

(* the piece: no imports *)
Definition dh4_G : funspecs := [wg_validate_header_len_spec].
Definition dh4_imports (cs: compspecs) : funspecs := [].
