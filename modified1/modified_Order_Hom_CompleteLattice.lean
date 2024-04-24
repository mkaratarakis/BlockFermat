def OrderIso.toCompleteLatticeHom [CompleteLattice α] [CompleteLattice β]
    (f : OrderIso α β) : CompleteLatticeHom α β where
  toFun := f
  map_sInf' := sInfHomClass.map_sInf f
  map_sSup' := sSupHomClass.map_sSup f

instance [SupSet α] [SupSet β] [sSupHomClass F α β] : CoeTC F (sSupHom α β) :=
  ⟨fun f => ⟨f, map_sSup f⟩⟩

instance [InfSet α] [InfSet β] [sInfHomClass F α β] : CoeTC F (sInfHom α β) :=
  ⟨fun f => ⟨f, map_sInf f⟩⟩

instance [CompleteLattice α] [CompleteLattice β] [FrameHomClass F α β] : CoeTC F (FrameHom α β) :=
  ⟨fun f => ⟨f, map_sSup f⟩⟩

instance [CompleteLattice α] [CompleteLattice β] [CompleteLatticeHomClass F α β] :
    CoeTC F (CompleteLatticeHom α β) :=
  ⟨fun f => ⟨f, map_sSup f⟩⟩

/-! ### Supremum homomorphisms -/

def copy (f : sSupHom α β) (f' : α → β) (h : f' = f) : sSupHom α β
    where
  toFun := f'
  map_sSup' := h.symm ▸ f.map_sSup'
#align Sup_hom.copy sSupHom.copy

def id : sSupHom α α :=
  ⟨id, fun s => by rw [id, Set.image_id]⟩
#align Sup_hom.id sSupHom.id

def comp (f : sSupHom β γ) (g : sSupHom α β) : sSupHom α γ
    where
  toFun := f ∘ g
  map_sSup' s := by rw [comp_apply, map_sSup, map_sSup, Set.image_image]; simp only [Function.comp]
#align Sup_hom.comp sSupHom.comp

def copy (f : sInfHom α β) (f' : α → β) (h : f' = f) : sInfHom α β
    where
  toFun := f'
  map_sInf' := h.symm ▸ f.map_sInf'
#align Inf_hom.copy sInfHom.copy

def id : sInfHom α α :=
  ⟨id, fun s => by rw [id, Set.image_id]⟩
#align Inf_hom.id sInfHom.id

def comp (f : sInfHom β γ) (g : sInfHom α β) : sInfHom α γ
    where
  toFun := f ∘ g
  map_sInf' s := by rw [comp_apply, map_sInf, map_sInf, Set.image_image]; simp only [Function.comp]
#align Inf_hom.comp sInfHom.comp

def toLatticeHom (f : FrameHom α β) : LatticeHom α β :=
  f
#align frame_hom.to_lattice_hom FrameHom.toLatticeHom

def copy (f : FrameHom α β) (f' : α → β) (h : f' = f) : FrameHom α β :=
  { (f : sSupHom α β).copy f' h with toInfTopHom := f.toInfTopHom.copy f' h }
#align frame_hom.copy FrameHom.copy

def id : FrameHom α α :=
  { sSupHom.id α with toInfTopHom := InfTopHom.id α }
#align frame_hom.id FrameHom.id

def comp (f : FrameHom β γ) (g : FrameHom α β) : FrameHom α γ :=
  { (f : sSupHom β γ).comp (g : sSupHom α β) with
    toInfTopHom := f.toInfTopHom.comp g.toInfTopHom }
#align frame_hom.comp FrameHom.comp

def tosSupHom (f : CompleteLatticeHom α β) : sSupHom α β :=
  f
#align complete_lattice_hom.to_Sup_hom CompleteLatticeHom.tosSupHom

def toBoundedLatticeHom (f : CompleteLatticeHom α β) : BoundedLatticeHom α β :=
  f
#align complete_lattice_hom.to_bounded_lattice_hom CompleteLatticeHom.toBoundedLatticeHom

def copy (f : CompleteLatticeHom α β) (f' : α → β) (h : f' = f) :
    CompleteLatticeHom α β :=
  { f.tosSupHom.copy f' h with tosInfHom := f.tosInfHom.copy f' h }
#align complete_lattice_hom.copy CompleteLatticeHom.copy

def id : CompleteLatticeHom α α :=
  { sSupHom.id α, sInfHom.id α with toFun := id }
#align complete_lattice_hom.id CompleteLatticeHom.id

def comp (f : CompleteLatticeHom β γ) (g : CompleteLatticeHom α β) : CompleteLatticeHom α γ :=
  { f.tosSupHom.comp g.tosSupHom with tosInfHom := f.tosInfHom.comp g.tosInfHom }
#align complete_lattice_hom.comp CompleteLatticeHom.comp

def dual : sSupHom α β ≃ sInfHom αᵒᵈ βᵒᵈ
    where
  toFun f := ⟨toDual ∘ f ∘ ofDual, f.map_sSup'⟩
  invFun f := ⟨ofDual ∘ f ∘ toDual, f.map_sInf'⟩
  left_inv _ := sSupHom.ext fun _ => rfl
  right_inv _ := sInfHom.ext fun _ => rfl
#align Sup_hom.dual sSupHom.dual

def dual : sInfHom α β ≃ sSupHom αᵒᵈ βᵒᵈ
    where
  toFun f :=
    { toFun := toDual ∘ f ∘ ofDual
      map_sSup' := fun _ => congr_arg toDual (map_sInf f _) }
  invFun f :=
    { toFun := ofDual ∘ f ∘ toDual
      map_sInf' := fun _ => congr_arg ofDual (map_sSup f _) }
  left_inv _ := sInfHom.ext fun _ => rfl
  right_inv _ := sSupHom.ext fun _ => rfl
#align Inf_hom.dual sInfHom.dual

def dual : CompleteLatticeHom α β ≃ CompleteLatticeHom αᵒᵈ βᵒᵈ
    where
  toFun f := ⟨sSupHom.dual f.tosSupHom, fun s ↦ f.map_sInf' s⟩
  invFun f := ⟨sSupHom.dual f.tosSupHom, fun s ↦ f.map_sInf' s⟩
  left_inv _ := ext fun _ => rfl
  right_inv _ := ext fun _ => rfl
#align complete_lattice_hom.dual CompleteLatticeHom.dual

def setPreimage (f : α → β) : CompleteLatticeHom (Set β) (Set α)
    where
  toFun := preimage f
  map_sSup' s := preimage_sUnion.trans <| by simp only [Set.sSup_eq_sUnion, Set.sUnion_image]
  map_sInf' s := preimage_sInter.trans <| by simp only [Set.sInf_eq_sInter, Set.sInter_image]
#align complete_lattice_hom.set_preimage CompleteLatticeHom.setPreimage

def sSupHom.setImage (f : α → β) : sSupHom (Set α) (Set β)
    where
  toFun := image f
  map_sSup' := Set.image_sSup
#align Sup_hom.set_image sSupHom.setImage

def Equiv.toOrderIsoSet (e : α ≃ β) : Set α ≃o Set β
    where
  toFun s := e '' s
  invFun s := e.symm '' s
  left_inv s := by simp only [← image_comp, Equiv.symm_comp_self, id, image_id']
  right_inv s := by simp only [← image_comp, Equiv.self_comp_symm, id, image_id']
  map_rel_iff' :=
    ⟨fun h => by simpa using @monotone_image _ _ e.symm _ _ h, fun h => monotone_image h⟩
#align equiv.to_order_iso_set Equiv.toOrderIsoSet

def supsSupHom : sSupHom (α × α) α where
  toFun x := x.1 ⊔ x.2
  map_sSup' s := by simp_rw [Prod.fst_sSup, Prod.snd_sSup, sSup_image, iSup_sup_eq]
#align sup_Sup_hom supsSupHom

def infsInfHom : sInfHom (α × α) α where
  toFun x := x.1 ⊓ x.2
  map_sInf' s := by simp_rw [Prod.fst_sInf, Prod.snd_sInf, sInf_image, iInf_inf_eq]
#align inf_Inf_hom infsInfHom

structure sSupHom (α β : Type*) [SupSet α] [SupSet β] where
  /-- The underlying function of a sSupHom. -/
  toFun : α → β
  /-- The proposition that a `sSupHom` commutes with arbitrary suprema/joins. -/
  map_sSup' (s : Set α) : toFun (sSup s) = sSup (toFun '' s)
#align Sup_hom sSupHom

structure sInfHom (α β : Type*) [InfSet α] [InfSet β] where
  /-- The underlying function of an `sInfHom`. -/
  toFun : α → β
  /-- The proposition that a `sInfHom` commutes with arbitrary infima/meets -/
  map_sInf' (s : Set α) : toFun (sInf s) = sInf (toFun '' s)
#align Inf_hom sInfHom

structure FrameHom (α β : Type*) [CompleteLattice α] [CompleteLattice β] extends
  InfTopHom α β where
  /-- The proposition that frame homomorphisms commute with arbitrary suprema/joins. -/
  map_sSup' (s : Set α) : toFun (sSup s) = sSup (toFun '' s)
#align frame_hom FrameHom

structure CompleteLatticeHom (α β : Type*) [CompleteLattice α] [CompleteLattice β] extends
  sInfHom α β where
  /-- The proposition that complete lattice homomorphism commutes with arbitrary suprema/joins. -/
  map_sSup' (s : Set α) : toFun (sSup s) = sSup (toFun '' s)
#align complete_lattice_hom CompleteLatticeHom