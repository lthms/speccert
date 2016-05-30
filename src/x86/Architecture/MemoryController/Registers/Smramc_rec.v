(* see: specs/intel/5th-gen-core-family-datasheet-vol-2.pdf *)
Record SmramcRegister := {
  d_open: bool;
  d_lock: bool;

  (* following proofs are justified by:
   * “When D_LCK=1, then D_OPEN is reset to 0 and all 
   * writeable fields in this register are locked (become RO).”
   *)
  lock_is_close: d_lock = true -> d_open = false;
  open_is_unlocked: d_open = true -> d_lock = false
}.
