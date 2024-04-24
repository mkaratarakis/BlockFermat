def lmk (s : Finset ι) : (∀ i : (↑s : Set ι), M i) →ₗ[R] Π₀ i, M i where
  toFun := mk s
  map_add' _ _ := mk_add
  map_smul' c x := mk_smul c x
#align dfinsupp.lmk DFinsupp.lmk

def lsingle (i) : M i →ₗ[R] Π₀ i, M i :=
  { DFinsupp.singleAddHom _ _ with
    toFun := single i
    map_smul' := single_smul }
#align dfinsupp.lsingle DFinsupp.lsingle

def lapply (i : ι) : (Π₀ i, M i) →ₗ[R] M i where
  toFun f := f i
  map_add' f g := add_apply f g i
  map_smul' c f := smul_apply c f i
#align dfinsupp.lapply DFinsupp.lapply

def lsum [Semiring S] [Module S N] [SMulCommClass R S N] :
    (∀ i, M i →ₗ[R] N) ≃ₗ[S] (Π₀ i, M i) →ₗ[R] N where
  toFun F :=
    { toFun := sumAddHom fun i => (F i).toAddMonoidHom
      map_add' := (DFinsupp.liftAddHom fun (i : ι) => (F i).toAddMonoidHom).map_add
      map_smul' := fun c f => by
        dsimp
        apply DFinsupp.induction f
        · rw [smul_zero, AddMonoidHom.map_zero, smul_zero]
        · intro a b f _ _ hf
          rw [smul_add, AddMonoidHom.map_add, AddMonoidHom.map_add, smul_add, hf, ← single_smul,
            sumAddHom_single, sumAddHom_single, LinearMap.toAddMonoidHom_coe,
            LinearMap.map_smul] }
  invFun F i := F.comp (lsingle i)
  left_inv F := by
    ext
    simp
  right_inv F := by
    refine DFinsupp.lhom_ext' (fun i ↦ ?_)
    ext
    simp
  map_add' F G := by
    refine DFinsupp.lhom_ext' (fun i ↦ ?_)
    ext
    simp
  map_smul' c F := by
    refine DFinsupp.lhom_ext' (fun i ↦ ?_)
    ext
    simp
#align dfinsupp.lsum DFinsupp.lsum

def mapRange.linearMap (f : ∀ i, β₁ i →ₗ[R] β₂ i) : (Π₀ i, β₁ i) →ₗ[R] Π₀ i, β₂ i :=
  { mapRange.addMonoidHom fun i => (f i).toAddMonoidHom with
    toFun := mapRange (fun i x => f i x) fun i => (f i).map_zero
    map_smul' := fun r => mapRange_smul _ (fun i => (f i).map_zero) _ fun i => (f i).map_smul r }
#align dfinsupp.map_range.linear_map DFinsupp.mapRange.linearMap

def mapRange.linearEquiv (e : ∀ i, β₁ i ≃ₗ[R] β₂ i) : (Π₀ i, β₁ i) ≃ₗ[R] Π₀ i, β₂ i :=
  { mapRange.addEquiv fun i => (e i).toAddEquiv,
    mapRange.linearMap fun i => (e i).toLinearMap with
    toFun := mapRange (fun i x => e i x) fun i => (e i).map_zero
    invFun := mapRange (fun i x => (e i).symm x) fun i => (e i).symm.map_zero }
#align dfinsupp.map_range.linear_equiv DFinsupp.mapRange.linearEquiv

def coprodMap (f : ∀ i : ι, M i →ₗ[R] N) : (Π₀ i, M i) →ₗ[R] N :=
  (DFinsupp.lsum ℕ fun _ : ι => LinearMap.id) ∘ₗ DFinsupp.mapRange.linearMap f
#align dfinsupp.coprod_map DFinsupp.coprodMap

structure on `Π₀ i, M i`
is defined in `Data.DFinsupp`.

In this file we define `LinearMap` versions of various maps:

* `DFinsupp.lsingle a : M →ₗ[R] Π₀ i, M i`: `DFinsupp.single a` as a linear map;

* `DFinsupp.lmk s : (Π i : (↑s : Set ι), M i) →ₗ[R] Π₀ i, M i`: `DFinsupp.single a` as a linear map;

* `DFinsupp.lapply i : (Π₀ i, M i) →ₗ[R] M`: the map `fun f ↦ f i` as a linear map;

* `DFinsupp.lsum`: `DFinsupp.sum` or `DFinsupp.liftAddHom` as a `LinearMap`;

## Implementation notes