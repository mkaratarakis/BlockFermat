def symm (h : α ≃ᵤ β) : β ≃ᵤ α
    where
  uniformContinuous_toFun := h.uniformContinuous_invFun
  uniformContinuous_invFun := h.uniformContinuous_toFun
  toEquiv := h.toEquiv.symm
#align uniform_equiv.symm UniformEquiv.symm

def Simps.apply (h : α ≃ᵤ β) : α → β :=
  h
#align uniform_equiv.simps.apply UniformEquiv.Simps.apply

def Simps.symm_apply (h : α ≃ᵤ β) : β → α :=
  h.symm
#align uniform_equiv.simps.symm_apply UniformEquiv.Simps.symm_apply

def refl (α : Type*) [UniformSpace α] : α ≃ᵤ α
    where
  uniformContinuous_toFun := uniformContinuous_id
  uniformContinuous_invFun := uniformContinuous_id
  toEquiv := Equiv.refl α
#align uniform_equiv.refl UniformEquiv.refl

def trans (h₁ : α ≃ᵤ β) (h₂ : β ≃ᵤ γ) : α ≃ᵤ γ
    where
  uniformContinuous_toFun := h₂.uniformContinuous_toFun.comp h₁.uniformContinuous_toFun
  uniformContinuous_invFun := h₁.uniformContinuous_invFun.comp h₂.uniformContinuous_invFun
  toEquiv := Equiv.trans h₁.toEquiv h₂.toEquiv
#align uniform_equiv.trans UniformEquiv.trans

def toHomeomorph (e : α ≃ᵤ β) : α ≃ₜ β :=
  { e.toEquiv with
    continuous_toFun := e.continuous
    continuous_invFun := e.continuous_symm }
#align uniform_equiv.to_homeomorph UniformEquiv.toHomeomorph

def changeInv (f : α ≃ᵤ β) (g : β → α) (hg : Function.RightInverse g f) : α ≃ᵤ β :=
  have : g = f.symm :=
    funext fun x => calc
      g x = f.symm (f (g x)) := (f.left_inv (g x)).symm
      _ = f.symm x := by rw [hg x]
  { toFun := f
    invFun := g
    left_inv := by convert f.left_inv
    right_inv := by convert f.right_inv using 1
    uniformContinuous_toFun := f.uniformContinuous
    uniformContinuous_invFun := by convert f.symm.uniformContinuous }
#align uniform_equiv.change_inv UniformEquiv.changeInv

def ofUniformEmbedding (f : α → β) (hf : UniformEmbedding f) : α ≃ᵤ Set.range f
    where
  uniformContinuous_toFun := hf.toUniformInducing.uniformContinuous.subtype_mk _
  uniformContinuous_invFun := by
    rw [hf.toUniformInducing.uniformContinuous_iff, Equiv.invFun_as_coe,
      Equiv.self_comp_ofInjective_symm]
    exact uniformContinuous_subtype_val
  toEquiv := Equiv.ofInjective f hf.inj
#align uniform_equiv.of_uniform_embedding UniformEquiv.ofUniformEmbedding

def setCongr {s t : Set α} (h : s = t) : s ≃ᵤ t
    where
  uniformContinuous_toFun := uniformContinuous_subtype_val.subtype_mk _
  uniformContinuous_invFun := uniformContinuous_subtype_val.subtype_mk _
  toEquiv := Equiv.setCongr h
#align uniform_equiv.set_congr UniformEquiv.setCongr

def prodCongr (h₁ : α ≃ᵤ β) (h₂ : γ ≃ᵤ δ) : α × γ ≃ᵤ β × δ
    where
  uniformContinuous_toFun :=
    (h₁.uniformContinuous.comp uniformContinuous_fst).prod_mk
      (h₂.uniformContinuous.comp uniformContinuous_snd)
  uniformContinuous_invFun :=
    (h₁.symm.uniformContinuous.comp uniformContinuous_fst).prod_mk
      (h₂.symm.uniformContinuous.comp uniformContinuous_snd)
  toEquiv := h₁.toEquiv.prodCongr h₂.toEquiv
#align uniform_equiv.prod_congr UniformEquiv.prodCongr

def prodComm : α × β ≃ᵤ β × α
    where
  uniformContinuous_toFun := uniformContinuous_snd.prod_mk uniformContinuous_fst
  uniformContinuous_invFun := uniformContinuous_snd.prod_mk uniformContinuous_fst
  toEquiv := Equiv.prodComm α β
#align uniform_equiv.prod_comm UniformEquiv.prodComm

def prodAssoc : (α × β) × γ ≃ᵤ α × β × γ
    where
  uniformContinuous_toFun :=
    (uniformContinuous_fst.comp uniformContinuous_fst).prod_mk
      ((uniformContinuous_snd.comp uniformContinuous_fst).prod_mk uniformContinuous_snd)
  uniformContinuous_invFun := by -- Porting note: the `rw` was not necessary in Lean 3
    rw [Equiv.invFun, Equiv.prodAssoc]
    exact (uniformContinuous_fst.prod_mk (uniformContinuous_fst.comp
    uniformContinuous_snd)).prod_mk (uniformContinuous_snd.comp uniformContinuous_snd)
  toEquiv := Equiv.prodAssoc α β γ
#align uniform_equiv.prod_assoc UniformEquiv.prodAssoc

def prodPunit : α × PUnit ≃ᵤ α where
  toEquiv := Equiv.prodPUnit α
  uniformContinuous_toFun := uniformContinuous_fst
  uniformContinuous_invFun := uniformContinuous_id.prod_mk uniformContinuous_const
#align uniform_equiv.prod_punit UniformEquiv.prodPunit

def punitProd : PUnit × α ≃ᵤ α :=
  (prodComm _ _).trans (prodPunit _)
#align uniform_equiv.punit_prod UniformEquiv.punitProd

def piCongrLeft {ι ι' : Type*} {β : ι' → Type*} [∀ j, UniformSpace (β j)]
    (e : ι ≃ ι') : (∀ i, β (e i)) ≃ᵤ ∀ j, β j where
  uniformContinuous_toFun := uniformContinuous_pi.mpr <| e.forall_congr_left.mp fun i ↦ by
    simpa only [Equiv.toFun_as_coe, Equiv.piCongrLeft_apply_apply] using
      Pi.uniformContinuous_proj _ i
  uniformContinuous_invFun := Pi.uniformContinuous_precomp' _ e
  toEquiv := Equiv.piCongrLeft _ e

/-- `Equiv.piCongrRight` as a uniform isomorphism: this is the natural isomorphism
`Π i, β₁ i ≃ᵤ Π j, β₂ i` obtained from uniform isomorphisms `β₁ i ≃ᵤ β₂ i` for each `i`. -/
@[simps! apply toEquiv]
def piCongrRight {ι : Type*} {β₁ β₂ : ι → Type*} [∀ i, UniformSpace (β₁ i)]
    [∀ i, UniformSpace (β₂ i)] (F : ∀ i, β₁ i ≃ᵤ β₂ i) : (∀ i, β₁ i) ≃ᵤ ∀ i, β₂ i where
  uniformContinuous_toFun := Pi.uniformContinuous_postcomp' _ fun i ↦ (F i).uniformContinuous
  uniformContinuous_invFun := Pi.uniformContinuous_postcomp' _ fun i ↦ (F i).symm.uniformContinuous
  toEquiv := Equiv.piCongrRight fun i => (F i).toEquiv

@[simp]
theorem piCongrRight_symm {ι : Type*} {β₁ β₂ : ι → Type*} [∀ i, UniformSpace (β₁ i)]
    [∀ i, UniformSpace (β₂ i)] (F : ∀ i, β₁ i ≃ᵤ β₂ i) :
    (piCongrRight F).symm = piCongrRight fun i => (F i).symm :=
  rfl

/-- `Equiv.piCongr` as a uniform isomorphism: this is the natural isomorphism
`Π i₁, β₁ i ≃ᵤ Π i₂, β₂ i₂` obtained from a bijection `ι₁ ≃ ι₂` and isomorphisms
`β₁ i₁ ≃ᵤ β₂ (e i₁)` for each `i₁ : ι₁`. -/
@[simps! apply toEquiv]
def piCongr {ι₁ ι₂ : Type*} {β₁ : ι₁ → Type*} {β₂ : ι₂ → Type*}
    [∀ i₁, UniformSpace (β₁ i₁)] [∀ i₂, UniformSpace (β₂ i₂)]
    (e : ι₁ ≃ ι₂) (F : ∀ i₁, β₁ i₁ ≃ᵤ β₂ (e i₁)) : (∀ i₁, β₁ i₁) ≃ᵤ ∀ i₂, β₂ i₂ :=
  (UniformEquiv.piCongrRight F).trans (UniformEquiv.piCongrLeft e)

/-- Uniform equivalence between `ULift α` and `α`. -/
def ulift : ULift.{v, u} α ≃ᵤ α :=
  { Equiv.ulift with
    uniformContinuous_toFun := uniformContinuous_comap
    uniformContinuous_invFun := by
      have hf : UniformInducing (@Equiv.ulift.{v, u} α).toFun := ⟨rfl⟩
      simp_rw [hf.uniformContinuous_iff]
      exact uniformContinuous_id }
#align uniform_equiv.ulift UniformEquiv.ulift

def funUnique (ι α : Type*) [Unique ι] [UniformSpace α] : (ι → α) ≃ᵤ α
    where
  toEquiv := Equiv.funUnique ι α
  uniformContinuous_toFun := Pi.uniformContinuous_proj _ _
  uniformContinuous_invFun := uniformContinuous_pi.mpr fun _ => uniformContinuous_id
#align uniform_equiv.fun_unique UniformEquiv.funUnique

def piFinTwo (α : Fin 2 → Type u) [∀ i, UniformSpace (α i)] : (∀ i, α i) ≃ᵤ α 0 × α 1
    where
  toEquiv := piFinTwoEquiv α
  uniformContinuous_toFun := (Pi.uniformContinuous_proj _ 0).prod_mk (Pi.uniformContinuous_proj _ 1)
  uniformContinuous_invFun :=
    uniformContinuous_pi.mpr <| Fin.forall_fin_two.2 ⟨uniformContinuous_fst, uniformContinuous_snd⟩
#align uniform_equiv.pi_fin_two UniformEquiv.piFinTwo

def finTwoArrow (α : Type*) [UniformSpace α] : (Fin 2 → α) ≃ᵤ α × α :=
  { piFinTwo fun _ => α with toEquiv := finTwoArrowEquiv α }
#align uniform_equiv.fin_two_arrow UniformEquiv.finTwoArrow

def image (e : α ≃ᵤ β) (s : Set α) : s ≃ᵤ e '' s
    where
  uniformContinuous_toFun := (e.uniformContinuous.comp uniformContinuous_subtype_val).subtype_mk _
  uniformContinuous_invFun :=
    (e.symm.uniformContinuous.comp uniformContinuous_subtype_val).subtype_mk _
  toEquiv := e.toEquiv.image s
#align uniform_equiv.image UniformEquiv.image

def Equiv.toUniformEquivOfUniformInducing [UniformSpace α] [UniformSpace β] (f : α ≃ β)
    (hf : UniformInducing f) : α ≃ᵤ β :=
  { f with
    uniformContinuous_toFun := hf.uniformContinuous
    uniformContinuous_invFun := hf.uniformContinuous_iff.2 <| by simpa using uniformContinuous_id }
#align equiv.to_uniform_equiv_of_uniform_inducing Equiv.toUniformEquivOfUniformInducing

structure UniformEquiv (α : Type*) (β : Type*) [UniformSpace α] [UniformSpace β] extends
  α ≃ β where
  /-- Uniform continuity of the function -/
  uniformContinuous_toFun : UniformContinuous toFun
  /-- Uniform continuity of the inverse -/
  uniformContinuous_invFun : UniformContinuous invFun
#align uniform_equiv UniformEquiv