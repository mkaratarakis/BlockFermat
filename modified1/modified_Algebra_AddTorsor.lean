def vaddConst (p : P) : G ≃ P where
  toFun v := v +ᵥ p
  invFun p' := p' -ᵥ p
  left_inv _ := vadd_vsub _ _
  right_inv _ := vsub_vadd _ _
#align equiv.vadd_const Equiv.vaddConst

def constVSub (p : P) : P ≃ G where
  toFun := (p -ᵥ ·)
  invFun := (-· +ᵥ p)
  left_inv p' := by simp
  right_inv v := by simp [vsub_vadd_eq_vsub_sub]
#align equiv.const_vsub Equiv.constVSub

def constVAdd (v : G) : Equiv.Perm P where
  toFun := (v +ᵥ ·)
  invFun := (-v +ᵥ ·)
  left_inv p := by simp [vadd_vadd]
  right_inv p := by simp [vadd_vadd]
#align equiv.const_vadd Equiv.constVAdd

def constVAddHom : Multiplicative G →* Equiv.Perm P where
  toFun v := constVAdd P (Multiplicative.toAdd v)
  map_one' := constVAdd_zero G P
  map_mul' := constVAdd_add P
#align equiv.const_vadd_hom Equiv.constVAddHom

def pointReflection (x : P) : Perm P :=
  (constVSub x).trans (vaddConst x)
#align equiv.point_reflection Equiv.pointReflection

structure to the nonempty type `P`,
acted on by an `AddGroup G` with a transitive and free action given
by the `+ᵥ` operation and a corresponding subtraction given by the
`-ᵥ` operation. In the case of a vector space, it is an affine
space. -/
class AddTorsor (G : outParam (Type*)) (P : Type*) [outParam <| AddGroup G] extends AddAction G P,
  VSub G P where
  [nonempty : Nonempty P]
  /-- Torsor subtraction and addition with the same element cancels out. -/
  vsub_vadd' : ∀ p₁ p₂ : P, (p₁ -ᵥ p₂ : G) +ᵥ p₂ = p₁
  /-- Torsor addition and subtraction with the same element cancels out. -/
  vadd_vsub' : ∀ (g : G) (p : P), g +ᵥ p -ᵥ p = g
#align add_torsor AddTorsor