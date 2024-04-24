def SModEq (x y : M) : Prop :=
  (Submodule.Quotient.mk x : M ⧸ U) = Submodule.Quotient.mk y
#align smodeq SModEq

def :
    x ≡ y [SMOD U] ↔ (Submodule.Quotient.mk x : M ⧸ U) = Submodule.Quotient.mk y :=
  Iff.rfl
#align smodeq.def SModEq.def