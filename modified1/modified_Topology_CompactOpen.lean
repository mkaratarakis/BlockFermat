def coev (b : Y) : C(X, Y × X) :=
  { toFun := Prod.mk b }
#align continuous_map.coev ContinuousMap.coev

def curry (f : C(X × Y, Z)) : C(X, C(Y, Z)) where
  toFun a := ⟨Function.curry f a, f.continuous.comp <| by continuity⟩
  continuous_toFun := (continuous_comp f).comp continuous_coev
#align continuous_map.curry ContinuousMap.curry

def curry' (f : C(X × Y, Z)) (a : X) : C(Y, Z) := curry f a
#align continuous_map.curry' ContinuousMap.curry'

def uncurry [LocallyCompactSpace Y] (f : C(X, C(Y, Z))) : C(X × Y, Z) :=
  ⟨_, continuous_uncurry_of_continuous f⟩
#align continuous_map.uncurry ContinuousMap.uncurry

def const' : C(Y, C(X, Y)) :=
  curry ContinuousMap.fst
#align continuous_map.const' ContinuousMap.const'

def curry [LocallyCompactSpace X] [LocallyCompactSpace Y] : C(X × Y, Z) ≃ₜ C(X, C(Y, Z)) :=
  ⟨⟨ContinuousMap.curry, uncurry, by intro; ext; rfl, by intro; ext; rfl⟩,
    continuous_curry, continuous_uncurry⟩
#align homeomorph.curry Homeomorph.curry

def continuousMapOfUnique [Unique X] : Y ≃ₜ C(X, Y) where
  toFun := const X
  invFun f := f default
  left_inv _ := rfl
  right_inv f := by
    ext x
    rw [Unique.eq_default x]
    rfl
  continuous_toFun := continuous_const'
  continuous_invFun := continuous_eval_const _
#align homeomorph.continuous_map_of_unique Homeomorph.continuousMapOfUnique