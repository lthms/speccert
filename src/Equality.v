Class Eq
      (T: Type)
  := { eq: forall t t': T, Prop
     ; eq_refl: forall t: T, eq t t
     ; eq_sym: forall t t': T, eq t t' -> eq t' t
     ; eq_trans: forall t t' t'': T, eq t t' -> eq t' t'' -> eq t t''
     ; eq_dec: forall t t': T, {eq t t'} + {~ eq t t'} }.