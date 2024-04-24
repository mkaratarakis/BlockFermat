def prod [Zero M] [CommMonoid N] (f : α →₀ M) (g : α → M → N) : N :=
  ∏ a in f.support, g a (f a)
#align finsupp.prod Finsupp.prod

def liftAddHom [AddZeroClass M] [AddCommMonoid N] : (α → M →+ N) ≃+ ((α →₀ M) →+ N)
    where
  toFun F :=
    { toFun := fun f ↦ f.sum fun x ↦ F x
      map_zero' := Finset.sum_empty
      map_add' := fun _ _ => sum_add_index' (fun x => (F x).map_zero) fun x => (F x).map_add }
  invFun F x := F.comp (singleAddHom x)
  left_inv F := by
    ext
    simp [singleAddHom]
  right_inv F := by
  -- Porting note: This was `ext` and used the wrong lemma
    apply Finsupp.addHom_ext'
    simp [singleAddHom, AddMonoidHom.comp, Function.comp]
  map_add' F G := by
    ext x
    exact sum_add
#align finsupp.lift_add_hom Finsupp.liftAddHom