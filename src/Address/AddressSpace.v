Require Import SpecCert.Interval.

Parameters (address_space:     Interval)
           (smram_space:       Interval)
           (smram_is_in_space: is_included_in smram_space address_space).
