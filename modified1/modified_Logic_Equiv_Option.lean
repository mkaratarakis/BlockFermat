def optionCongr (e : α ≃ β) : Option α ≃ Option β where
  toFun := Option.map e
  invFun := Option.map e.symm
  left_inv x := (Option.map_map _ _ _).trans <| e.symm_comp_self.symm ▸ congr_fun Option.map_id x
  right_inv x := (Option.map_map _ _ _).trans <| e.self_comp_symm.symm ▸ congr_fun Option.map_id x
#align equiv.option_congr Equiv.optionCongr

def removeNone_aux (x : α) : β :=
  if h : (e (some x)).isSome then Option.get _ h
  else
    Option.get _ <|
      show (e none).isSome by
        rw [← Option.ne_none_iff_isSome]
        intro hn
        rw [Option.not_isSome_iff_eq_none, ← hn] at h
        exact Option.some_ne_none _ (e.injective h)
-- Porting note: private
-- #align equiv.remove_none_aux Equiv.removeNone_aux

def removeNone : α ≃ β where
  toFun := removeNone_aux e
  invFun := removeNone_aux e.symm
  left_inv := removeNone_aux_inv e
  right_inv := removeNone_aux_inv e.symm
#align equiv.remove_none Equiv.removeNone

def optionSubtype [DecidableEq β] (x : β) :
    { e : Option α ≃ β // e none = x } ≃ (α ≃ { y : β // y ≠ x }) where
  toFun e :=
    { toFun := fun a =>
        ⟨(e : Option α ≃ β) a, ((EquivLike.injective _).ne_iff' e.property).2 (some_ne_none _)⟩,
      invFun := fun b =>
        get _
          (ne_none_iff_isSome.1
            (((EquivLike.injective _).ne_iff'
              ((apply_eq_iff_eq_symm_apply _).1 e.property).symm).2 b.property)),
      left_inv := fun a => by
        rw [← some_inj, some_get]
        exact symm_apply_apply (e : Option α ≃ β) a,
      right_inv := fun b => by
        ext
        simp }
  invFun e :=
    ⟨{  toFun := fun a => casesOn' a x (Subtype.val ∘ e),
        invFun := fun b => if h : b = x then none else e.symm ⟨b, h⟩,
        left_inv := fun a => by
          cases a with
          | none => simp
          | some a =>
            simp only [casesOn'_some, Function.comp_apply, Subtype.coe_eta,
              symm_apply_apply, dite_eq_ite]
            exact if_neg (e a).property,
        right_inv := fun b => by
          by_cases h : b = x <;> simp [h] },
      rfl⟩
  left_inv e := by
    ext a
    cases a
    · simpa using e.property.symm
    -- Porting note: this cases had been by `simpa`,
    -- but `simp` here is mysteriously slow, even after squeezing.
    -- `rfl` closes the goal quickly, so we use that.
    · rfl
  right_inv e := by
    ext a
    rfl
#align equiv.option_subtype Equiv.optionSubtype