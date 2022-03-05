Require Import Rupicola.Examples.Net.IPChecksum.IPChecksum.

Require Import ExtrOcamlNatBigInt ExtrOcamlZBigInt.
Extraction "ip_spec_naive.ml" Spec.ip_checksum Byte.of_nat.
Extraction "ip_impl_naive.ml" Impl.ip_checksum_impl Byte.of_nat.

Require Import
        Coq.ZArith.ZArith
        Coq.extraction.ExtrOcamlZInt
        Coq.extraction.ExtrOcamlNatInt
        Coq.extraction.ExtrOcamlNativeString.
Extract Inlined Constant Byte.to_N => "Char.code".
Extract Inlined Constant Z.land => "(land)".
Extract Inlined Constant Z.lor => "(lor)".
Extract Inlined Constant Z.lxor => "(lxor)".
Extract Inlined Constant Z.shiftl => "Int.shift_left".
Extract Inlined Constant Z.shiftr => "Int.shift_right".

Extraction "ip_spec_opt.ml" Spec.ip_checksum.
Extraction "ip_impl_opt.ml" Impl.ip_checksum_impl.
