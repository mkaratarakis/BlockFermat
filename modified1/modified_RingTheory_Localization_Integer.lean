def IsInteger (a : S) : Prop :=
  a ∈ (algebraMap R S).rangeS
#align is_localization.is_integer IsLocalization.IsInteger

def commonDenom {ι : Type*} (s : Finset ι) (f : ι → S) : M :=
  (exist_integer_multiples M s f).choose
#align is_localization.common_denom IsLocalization.commonDenom

def integerMultiple {ι : Type*} (s : Finset ι) (f : ι → S) (i : s) : R :=
  ((exist_integer_multiples M s f).choose_spec i i.prop).choose
#align is_localization.integer_multiple IsLocalization.integerMultiple

def commonDenomOfFinset (s : Finset S) : M :=
  commonDenom M s id
#align is_localization.common_denom_of_finset IsLocalization.commonDenomOfFinset

def finsetIntegerMultiple [DecidableEq R] (s : Finset S) : Finset R :=
  s.attach.image fun t => integerMultiple M s id t
#align is_localization.finset_integer_multiple IsLocalization.finsetIntegerMultiple