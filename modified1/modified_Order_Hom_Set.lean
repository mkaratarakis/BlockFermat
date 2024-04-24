def setCongr (s t : Set α) (h : s = t) :
    s ≃o t where
  toEquiv := Equiv.setCongr h
  map_rel_iff' := Iff.rfl
#align order_iso.set_congr OrderIso.setCongr

def Set.univ : (Set.univ : Set α) ≃o α where
  toEquiv := Equiv.Set.univ α
  map_rel_iff' := Iff.rfl
#align order_iso.set.univ OrderIso.Set.univ

def OrderEmbedding.orderIso [LE α] [LE β] {f : α ↪o β} :
    α ≃o Set.range f :=
  { Equiv.ofInjective _ f.injective with
    map_rel_iff' := f.map_rel_iff }

/-- If a function `f` is strictly monotone on a set `s`, then it defines an order isomorphism
between `s` and its image. -/
protected noncomputable def StrictMonoOn.orderIso {α β} [LinearOrder α] [Preorder β] (f : α → β)
    (s : Set α) (hf : StrictMonoOn f s) :
    s ≃o f '' s where
  toEquiv := hf.injOn.bijOn_image.equiv _
  map_rel_iff' := hf.le_iff_le (Subtype.property _) (Subtype.property _)
#align strict_mono_on.order_iso StrictMonoOn.orderIso

def orderIso :
    α ≃o Set.range f where
  toEquiv := Equiv.ofInjective f h_mono.injective
  map_rel_iff' := h_mono.le_iff_le
#align strict_mono.order_iso StrictMono.orderIso

def orderIsoOfSurjective : α ≃o β :=
  (h_mono.orderIso f).trans <|
    (OrderIso.setCongr _ _ h_surj.range_eq).trans OrderIso.Set.univ
#align strict_mono.order_iso_of_surjective StrictMono.orderIsoOfSurjective

def OrderIso.compl : α ≃o αᵒᵈ where
  toFun := OrderDual.toDual ∘ HasCompl.compl
  invFun := HasCompl.compl ∘ OrderDual.ofDual
  left_inv := compl_compl
  right_inv := compl_compl (α := αᵒᵈ)
  map_rel_iff' := compl_le_compl_iff_le
#align order_iso.compl OrderIso.compl