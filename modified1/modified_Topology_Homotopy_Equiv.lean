def toFun' (e : X ≃ₕ Y) : X → Y := e.toFun

instance : CoeFun (X ≃ₕ Y) fun _ => X → Y := ⟨toFun'⟩

@[simp]
theorem toFun_eq_coe (h : HomotopyEquiv X Y) : (h.toFun : X → Y) = h :=
  rfl
#align continuous_map.homotopy_equiv.to_fun_eq_coe ContinuousMap.HomotopyEquiv.toFun_eq_coe

def toHomotopyEquiv (h : X ≃ₜ Y) : X ≃ₕ Y where
  toFun := h
  invFun := h.symm
  left_inv := by rw [symm_comp_toContinuousMap]
  right_inv := by rw [toContinuousMap_comp_symm]
#align homeomorph.to_homotopy_equiv Homeomorph.toHomotopyEquiv

def symm (h : X ≃ₕ Y) : Y ≃ₕ X where
  toFun := h.invFun
  invFun := h.toFun
  left_inv := h.right_inv
  right_inv := h.left_inv
#align continuous_map.homotopy_equiv.symm ContinuousMap.HomotopyEquiv.symm

def Simps.apply (h : X ≃ₕ Y) : X → Y :=
  h
#align continuous_map.homotopy_equiv.simps.apply ContinuousMap.HomotopyEquiv.Simps.apply

def Simps.symm_apply (h : X ≃ₕ Y) : Y → X :=
  h.symm
#align continuous_map.homotopy_equiv.simps.symm_apply ContinuousMap.HomotopyEquiv.Simps.symm_apply

def refl (X : Type u) [TopologicalSpace X] : X ≃ₕ X :=
  (Homeomorph.refl X).toHomotopyEquiv
#align continuous_map.homotopy_equiv.refl ContinuousMap.HomotopyEquiv.refl

def trans (h₁ : X ≃ₕ Y) (h₂ : Y ≃ₕ Z) : X ≃ₕ Z where
  toFun := h₂.toFun.comp h₁.toFun
  invFun := h₁.invFun.comp h₂.invFun
  left_inv := by
    refine Homotopic.trans ?_ h₁.left_inv
    exact ((Homotopic.refl _).hcomp h₂.left_inv).hcomp (Homotopic.refl _)
  right_inv := by
    refine Homotopic.trans ?_ h₂.right_inv
    exact ((Homotopic.refl _).hcomp h₁.right_inv).hcomp (Homotopic.refl _)
#align continuous_map.homotopy_equiv.trans ContinuousMap.HomotopyEquiv.trans

def prodCongr (h₁ : X ≃ₕ Y) (h₂ : Z ≃ₕ Z') : (X × Z) ≃ₕ (Y × Z') where
  toFun := h₁.toFun.prodMap h₂.toFun
  invFun := h₁.invFun.prodMap h₂.invFun
  left_inv := h₁.left_inv.prodMap h₂.left_inv
  right_inv := h₁.right_inv.prodMap h₂.right_inv

/-- If `X i` is homotopy equivalent to `Y i` for each `i`, then the space of functions (a.k.a. the
indexed product) `∀ i, X i` is homotopy equivalent to `∀ i, Y i`. -/
def piCongrRight {ι : Type*} {X Y : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, TopologicalSpace (Y i)] (h : ∀ i, X i ≃ₕ Y i) :
    (∀ i, X i) ≃ₕ (∀ i, Y i) where
  toFun := .piMap fun i ↦ (h i).toFun
  invFun := .piMap fun i ↦ (h i).invFun
  left_inv := .piMap fun i ↦ (h i).left_inv
  right_inv := .piMap fun i ↦ (h i).right_inv

end HomotopyEquiv

end ContinuousMap

open ContinuousMap

namespace Homeomorph

@[simp]
theorem refl_toHomotopyEquiv (X : Type u) [TopologicalSpace X] :
    (Homeomorph.refl X).toHomotopyEquiv = HomotopyEquiv.refl X :=
  rfl
#align homeomorph.refl_to_homotopy_equiv Homeomorph.refl_toHomotopyEquiv

structure HomotopyEquiv (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y] where
  toFun : C(X, Y)
  invFun : C(Y, X)
  left_inv : (invFun.comp toFun).Homotopic (ContinuousMap.id X)
  right_inv : (toFun.comp invFun).Homotopic (ContinuousMap.id Y)
#align continuous_map.homotopy_equiv ContinuousMap.HomotopyEquiv