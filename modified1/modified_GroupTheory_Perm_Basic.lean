def equivUnitsEnd : Perm α ≃* Units (Function.End α) where
  -- Porting note: needed to add `.toFun`.
  toFun e := ⟨e.toFun, e.symm.toFun, e.self_comp_symm, e.symm_comp_self⟩
  invFun u :=
    ⟨(u : Function.End α), (↑u⁻¹ : Function.End α), congr_fun u.inv_val, congr_fun u.val_inv⟩
  left_inv _ := ext fun _ => rfl
  right_inv _ := Units.ext rfl
  map_mul' _ _ := rfl
#align equiv.perm.equiv_units_End Equiv.Perm.equivUnitsEnd

def _root_.MonoidHom.toHomPerm {G : Type*} [Group G] (f : G →* Function.End α) : G →* Perm α :=
  equivUnitsEnd.symm.toMonoidHom.comp f.toHomUnits
#align monoid_hom.to_hom_perm MonoidHom.toHomPerm

def : (1 : Perm α) = Equiv.refl α :=
  rfl
#align equiv.perm.one_def Equiv.Perm.one_def

def (f g : Perm α) : f * g = g.trans f :=
  rfl
#align equiv.perm.mul_def Equiv.Perm.mul_def

def (f : Perm α) : f⁻¹ = f.symm :=
  rfl
#align equiv.perm.inv_def Equiv.Perm.inv_def

def sumCongrHom (α β : Type*) : Perm α × Perm β →* Perm (Sum α β) where
  toFun a := sumCongr a.1 a.2
  map_one' := sumCongr_one
  map_mul' _ _ := (sumCongr_mul _ _ _ _).symm
#align equiv.perm.sum_congr_hom Equiv.Perm.sumCongrHom

def sigmaCongrRightHom {α : Type*} (β : α → Type*) : (∀ a, Perm (β a)) →* Perm (Σa, β a) where
  toFun := sigmaCongrRight
  map_one' := sigmaCongrRight_one
  map_mul' _ _ := (sigmaCongrRight_mul _ _).symm
#align equiv.perm.sigma_congr_right_hom Equiv.Perm.sigmaCongrRightHom

def subtypeCongrHom (p : α → Prop) [DecidablePred p] :
    Perm { a // p a } × Perm { a // ¬p a } →* Perm α where
  toFun pair := Perm.subtypeCongr pair.fst pair.snd
  map_one' := Perm.subtypeCongr.refl
  map_mul' _ _ := (Perm.subtypeCongr.trans _ _ _ _).symm
#align equiv.perm.subtype_congr_hom Equiv.Perm.subtypeCongrHom

def extendDomainHom : Perm α →* Perm β where
  toFun e := extendDomain e f
  map_one' := extendDomain_one f
  map_mul' e e' := (extendDomain_mul f e e').symm
#align equiv.perm.extend_domain_hom Equiv.Perm.extendDomainHom

def subtypePerm (f : Perm α) (h : ∀ x, p x ↔ p (f x)) : Perm { x // p x } where
  toFun := fun x => ⟨f x, (h _).1 x.2⟩
  invFun := fun x => ⟨f⁻¹ x, (h (f⁻¹ x)).2 <| by simpa using x.2⟩
  left_inv _ := by simp only [Perm.inv_apply_self, Subtype.coe_eta, Subtype.coe_mk]
  right_inv _ := by simp only [Perm.apply_inv_self, Subtype.coe_eta, Subtype.coe_mk]
#align equiv.perm.subtype_perm Equiv.Perm.subtypePerm

def ofSubtype : Perm (Subtype p) →* Perm α where
  toFun f := extendDomain f (Equiv.refl (Subtype p))
  map_one' := Equiv.Perm.extendDomain_one _
  map_mul' f g := (Equiv.Perm.extendDomain_mul _ f g).symm
#align equiv.perm.of_subtype Equiv.Perm.ofSubtype

def subtypeEquivSubtypePerm (p : α → Prop) [DecidablePred p] :
    Perm (Subtype p) ≃ { f : Perm α // ∀ a, ¬p a → f a = a } where
  toFun f := ⟨ofSubtype f, fun _ => f.ofSubtype_apply_of_not_mem⟩
  invFun f :=
    (f : Perm α).subtypePerm fun a =>
      ⟨Decidable.not_imp_not.1 fun hfa => f.val.injective (f.prop _ hfa) ▸ hfa,
        Decidable.not_imp_not.1 fun ha hfa => ha <| f.prop a ha ▸ hfa⟩
  left_inv := Equiv.Perm.subtypePerm_ofSubtype
  right_inv f :=
    Subtype.ext ((Equiv.Perm.ofSubtype_subtypePerm _) fun a => Not.decidable_imp_symm <| f.prop a)
#align equiv.perm.subtype_equiv_subtype_perm Equiv.Perm.subtypeEquivSubtypePerm

structure on `Equiv.Perm α`.
-/


universe u v

namespace Equiv

variable {α : Type u} {β : Type v}

namespace Perm

instance permGroup : Group (Perm α) where
  mul f g := Equiv.trans g f
  one := Equiv.refl α
  inv := Equiv.symm
  mul_assoc f g h := (trans_assoc _ _ _).symm
  one_mul := trans_refl
  mul_one := refl_trans
  mul_left_inv := self_trans_symm
#align equiv.perm.perm_group Equiv.Perm.permGroup