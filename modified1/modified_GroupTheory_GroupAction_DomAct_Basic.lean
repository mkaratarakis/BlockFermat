def DomMulAct (M : Type*) := MulOpposite M

@[inherit_doc] postfix:max "ᵈᵐᵃ" => DomMulAct
@[inherit_doc] postfix:max "ᵈᵃᵃ" => DomAddAct

namespace DomMulAct

/-- Equivalence between `M` and `Mᵈᵐᵃ`. -/
@[to_additive "Equivalence between `M` and `Mᵈᵐᵃ`."]
def mk : M ≃ Mᵈᵐᵃ := MulOpposite.opEquiv

/-!
### Copy instances from `Mᵐᵒᵖ`