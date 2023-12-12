module MiTLS.Hashing.Flags
open MiTLS
open MiTLS.Hashing.Spec
assume val crf : alg -> Tot bool
