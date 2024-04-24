def ConjAct : Type _ :=
  G
#align conj_act ConjAct

def ofConjAct : ConjAct G ≃* G where
  toFun := id
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_mul' := fun _ _ => rfl
#align conj_act.of_conj_act ConjAct.ofConjAct

def toConjAct : G ≃* ConjAct G :=
  ofConjAct.symm
#align conj_act.to_conj_act ConjAct.toConjAct

def rec {C : ConjAct G → Sort*} (h : ∀ g, C (toConjAct g)) : ∀ g, C g :=
  h
#align conj_act.rec ConjAct.rec

def (g : ConjAct G) (h : G) : g • h = ofConjAct g * h * (ofConjAct g)⁻¹ :=
  rfl
#align conj_act.smul_def ConjAct.smul_def

def (g : ConjAct Mˣ) (h : M) : g • h = ofConjAct g * h * ↑(ofConjAct g)⁻¹ :=
  rfl
#align conj_act.units_smul_def ConjAct.units_smul_def

def _root_.MulAut.conjNormal {H : Subgroup G} [H.Normal] : G →* MulAut H :=
  (MulDistribMulAction.toMulAut (ConjAct G) H).comp toConjAct.toMonoidHom
#align mul_aut.conj_normal MulAut.conjNormal