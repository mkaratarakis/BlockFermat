def coeAddMonoidHom : MultilinearMap R M₁ M₂ →+ (((i : ι) → M₁ i) → M₂) where
  toFun := DFunLike.coe; map_zero' := rfl; map_add' _ _ := rfl

@[simp]
theorem coe_sum {α : Type*} (f : α → MultilinearMap R M₁ M₂) (s : Finset α) :
    ⇑(∑ a in s, f a) = ∑ a in s, ⇑(f a) :=
  map_sum coeAddMonoidHom f s

theorem sum_apply {α : Type*} (f : α → MultilinearMap R M₁ M₂) (m : ∀ i, M₁ i) {s : Finset α} :
    (∑ a in s, f a) m = ∑ a in s, f a m := by simp
#align multilinear_map.sum_apply MultilinearMap.sum_apply

def toLinearMap [DecidableEq ι] (m : ∀ i, M₁ i) (i : ι) : M₁ i →ₗ[R] M₂ where
  toFun x := f (update m i x)
  map_add' x y := by simp
  map_smul' c x := by simp
#align multilinear_map.to_linear_map MultilinearMap.toLinearMap

def prod (f : MultilinearMap R M₁ M₂) (g : MultilinearMap R M₁ M₃) : MultilinearMap R M₁ (M₂ × M₃)
    where
  toFun m := (f m, g m)
  map_add' m i x y := by simp
  map_smul' m i c x := by simp
#align multilinear_map.prod MultilinearMap.prod

def pi {ι' : Type*} {M' : ι' → Type*} [∀ i, AddCommMonoid (M' i)] [∀ i, Module R (M' i)]
    (f : ∀ i, MultilinearMap R M₁ (M' i)) : MultilinearMap R M₁ (∀ i, M' i) where
  toFun m i := f i m
  map_add' _ _ _ _ := funext fun j => (f j).map_add _ _ _ _
  map_smul' _ _ _ _ := funext fun j => (f j).map_smul _ _ _ _
#align multilinear_map.pi MultilinearMap.pi

def ofSubsingleton [Subsingleton ι] (i : ι) :
    (M₂ →ₗ[R] M₃) ≃ MultilinearMap R (fun _ : ι ↦ M₂) M₃ where
  toFun f :=
    { toFun := fun x ↦ f (x i)
      map_add' := by intros; simp [update_eq_const_of_subsingleton]
      map_smul' := by intros; simp [update_eq_const_of_subsingleton] }
  invFun f :=
    { toFun := fun x ↦ f fun _ ↦ x
      map_add' := fun x y ↦ by simpa [update_eq_const_of_subsingleton] using f.map_add 0 i x y
      map_smul' := fun c x ↦ by simpa [update_eq_const_of_subsingleton] using f.map_smul 0 i c x }
  left_inv f := rfl
  right_inv f := by ext x; refine congr_arg f ?_; exact (eq_const_of_subsingleton _ _).symm
#align multilinear_map.of_subsingleton MultilinearMap.ofSubsingletonₓ

def constOfIsEmpty [IsEmpty ι] (m : M₂) : MultilinearMap R M₁ M₂ where
  toFun := Function.const _ m
  map_add' _ := isEmptyElim
  map_smul' _ := isEmptyElim
#align multilinear_map.const_of_is_empty MultilinearMap.constOfIsEmpty

def restr {k n : ℕ} (f : MultilinearMap R (fun _ : Fin n => M') M₂) (s : Finset (Fin n))
    (hk : s.card = k) (z : M') : MultilinearMap R (fun _ : Fin k => M') M₂ where
  toFun v := f fun j => if h : j ∈ s then v ((DFunLike.coe (s.orderIsoOfFin hk).symm) ⟨j, h⟩) else z
  /- Porting note: The proofs of the following two lemmas used to only use `erw` followed by `simp`,
  but it seems `erw` no longer unfolds or unifies well enough to work without more help. -/
  map_add' v i x y := by
    have : DFunLike.coe (s.orderIsoOfFin hk).symm = (s.orderIsoOfFin hk).toEquiv.symm := rfl
    simp only [this]
    erw [dite_comp_equiv_update (s.orderIsoOfFin hk).toEquiv,
      dite_comp_equiv_update (s.orderIsoOfFin hk).toEquiv,
      dite_comp_equiv_update (s.orderIsoOfFin hk).toEquiv]
    simp
  map_smul' v i c x := by
    have : DFunLike.coe (s.orderIsoOfFin hk).symm = (s.orderIsoOfFin hk).toEquiv.symm := rfl
    simp only [this]
    erw [dite_comp_equiv_update (s.orderIsoOfFin hk).toEquiv,
      dite_comp_equiv_update (s.orderIsoOfFin hk).toEquiv]
    simp
#align multilinear_map.restr MultilinearMap.restr

def compLinearMap (g : MultilinearMap R M₁' M₂) (f : ∀ i, M₁ i →ₗ[R] M₁' i) : MultilinearMap R M₁ M₂
    where
  toFun m := g fun i => f i (m i)
  map_add' m i x y := by
    have : ∀ j z, f j (update m i z j) = update (fun k => f k (m k)) i (f i z) j := fun j z =>
      Function.apply_update (fun k => f k) _ _ _ _
    simp [this]
  map_smul' m i c x := by
    have : ∀ j z, f j (update m i z j) = update (fun k => f k (m k)) i (f i z) j := fun j z =>
      Function.apply_update (fun k => f k) _ _ _ _
    simp [this]
#align multilinear_map.comp_linear_map MultilinearMap.compLinearMap

def codRestrict (f : MultilinearMap R M₁ M₂) (p : Submodule R M₂) (h : ∀ v, f v ∈ p) :
    MultilinearMap R M₁ p where
  toFun v := ⟨f v, h v⟩
  map_add' _ _ _ _ := Subtype.ext <| MultilinearMap.map_add _ _ _ _ _
  map_smul' _ _ _ _ := Subtype.ext <| MultilinearMap.map_smul _ _ _ _ _
#align multilinear_map.cod_restrict MultilinearMap.codRestrict

def restrictScalars (f : MultilinearMap A M₁ M₂) : MultilinearMap R M₁ M₂ where
  toFun := f
  map_add' := f.map_add
  map_smul' m i := (f.toLinearMap m i).map_smul_of_tower
#align multilinear_map.restrict_scalars MultilinearMap.restrictScalars

def domDomCongr (σ : ι₁ ≃ ι₂) (m : MultilinearMap R (fun _ : ι₁ => M₂) M₃) :
    MultilinearMap R (fun _ : ι₂ => M₂) M₃ where
  toFun v := m fun i => v (σ i)
  map_add' v i a b := by
    letI := σ.injective.decidableEq
    simp_rw [Function.update_apply_equiv_apply v]
    rw [m.map_add]
  map_smul' v i a b := by
    letI := σ.injective.decidableEq
    simp_rw [Function.update_apply_equiv_apply v]
    rw [m.map_smul]
#align multilinear_map.dom_dom_congr MultilinearMap.domDomCongr

def domDomCongrEquiv (σ : ι₁ ≃ ι₂) :
    MultilinearMap R (fun _ : ι₁ => M₂) M₃ ≃+ MultilinearMap R (fun _ : ι₂ => M₂) M₃ where
  toFun := domDomCongr σ
  invFun := domDomCongr σ.symm
  left_inv m := by
    ext
    simp [domDomCongr]
  right_inv m := by
    ext
    simp [domDomCongr]
  map_add' a b := by
    ext
    simp [domDomCongr]
#align multilinear_map.dom_dom_congr_equiv MultilinearMap.domDomCongrEquiv

def domDomRestrict (f : MultilinearMap R M₁ M₂) (P : ι → Prop) [DecidablePred P]
    (z : (i : {a : ι // ¬ P a}) → M₁ i) :
    MultilinearMap R (fun (i : {a : ι // P a}) => M₁ i) M₂ where
  toFun x := f (fun j ↦ if h : P j then x ⟨j, h⟩ else z ⟨j, h⟩)
  map_add' x i a b := by
    classical
    simp only
    repeat (rw [domDomRestrict_aux])
    simp only [MultilinearMap.map_add]
  map_smul' z i c a := by
    classical
    simp only
    repeat (rw [domDomRestrict_aux])
    simp only [MultilinearMap.map_smul]

@[simp]
lemma domDomRestrict_apply (f : MultilinearMap R M₁ M₂) (P : ι → Prop)
    [DecidablePred P] (x : (i : {a // P a}) → M₁ i) (z : (i : {a // ¬ P a}) → M₁ i) :
    f.domDomRestrict P z x = f (fun j => if h : P j then x ⟨j, h⟩ else z ⟨j, h⟩) := rfl

-- TODO: Should add a ref here when available.
/-- The "derivative" of a multilinear map, as a linear map from `(i : ι) → M₁ i` to `M₂`.
For continuous multilinear maps, this will indeed be the derivative. -/
def linearDeriv [DecidableEq ι] [Fintype ι] (f : MultilinearMap R M₁ M₂)
    (x : (i : ι) → M₁ i) : ((i : ι) → M₁ i) →ₗ[R] M₂ :=
  ∑ i : ι, (f.toLinearMap x i).comp (LinearMap.proj i)

@[simp]
lemma linearDeriv_apply [DecidableEq ι] [Fintype ι] (f : MultilinearMap R M₁ M₂)
    (x y : (i : ι) → M₁ i) :
    f.linearDeriv x y = ∑ i, f (update x i (y i)) := by
  unfold linearDeriv
  simp only [LinearMap.coeFn_sum, LinearMap.coe_comp, LinearMap.coe_proj, Finset.sum_apply,
    Function.comp_apply, Function.eval, toLinearMap_apply]

end Semiring

end MultilinearMap

namespace LinearMap

variable [Semiring R] [∀ i, AddCommMonoid (M₁ i)] [AddCommMonoid M₂] [AddCommMonoid M₃]
  [AddCommMonoid M'] [∀ i, Module R (M₁ i)] [Module R M₂] [Module R M₃] [Module R M']

/-- Composing a multilinear map with a linear map gives again a multilinear map. -/
def compMultilinearMap (g : M₂ →ₗ[R] M₃) (f : MultilinearMap R M₁ M₂) : MultilinearMap R M₁ M₃ where
  toFun := g ∘ f
  map_add' m i x y := by simp
  map_smul' m i c x := by simp
#align linear_map.comp_multilinear_map LinearMap.compMultilinearMap

def ofSubsingletonₗ [Subsingleton ι] (i : ι) :
    (M₂ →ₗ[R] M₃) ≃ₗ[S] MultilinearMap R (fun _ : ι ↦ M₂) M₃ :=
  { ofSubsingleton R M₂ M₃ i with
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl }

end OfSubsingleton

/-- The dependent version of `MultilinearMap.domDomCongrLinearEquiv`. -/
@[simps apply symm_apply]
def domDomCongrLinearEquiv' {ι' : Type*} (σ : ι ≃ ι') :
    MultilinearMap R M₁ M₂ ≃ₗ[S] MultilinearMap R (fun i => M₁ (σ.symm i)) M₂ where
  toFun f :=
    { toFun := f ∘ (σ.piCongrLeft' M₁).symm
      map_add' := fun m i => by
        letI := σ.decidableEq
        rw [← σ.apply_symm_apply i]
        intro x y
        simp only [comp_apply, piCongrLeft'_symm_update, f.map_add]
      map_smul' := fun m i c => by
        letI := σ.decidableEq
        rw [← σ.apply_symm_apply i]
        intro x
        simp only [Function.comp, piCongrLeft'_symm_update, f.map_smul] }
  invFun f :=
    { toFun := f ∘ σ.piCongrLeft' M₁
      map_add' := fun m i => by
        letI := σ.symm.decidableEq
        rw [← σ.symm_apply_apply i]
        intro x y
        simp only [comp_apply, piCongrLeft'_update, f.map_add]
      map_smul' := fun m i c => by
        letI := σ.symm.decidableEq
        rw [← σ.symm_apply_apply i]
        intro x
        simp only [Function.comp, piCongrLeft'_update, f.map_smul] }
  map_add' f₁ f₂ := by
    ext
    simp only [Function.comp, coe_mk, add_apply]
  map_smul' c f := by
    ext
    simp only [Function.comp, coe_mk, smul_apply, RingHom.id_apply]
  left_inv f := by
    ext
    simp only [coe_mk, comp_apply, Equiv.symm_apply_apply]
  right_inv f := by
    ext
    simp only [coe_mk, comp_apply, Equiv.apply_symm_apply]
#align multilinear_map.dom_dom_congr_linear_equiv' MultilinearMap.domDomCongrLinearEquiv'

def constLinearEquivOfIsEmpty [IsEmpty ι] : M₂ ≃ₗ[S] MultilinearMap R M₁ M₂ where
  toFun := MultilinearMap.constOfIsEmpty R _
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := f 0
  left_inv _ := rfl
  right_inv f := ext fun _ => MultilinearMap.congr_arg f <| Subsingleton.elim _ _
#align multilinear_map.const_linear_equiv_of_is_empty MultilinearMap.constLinearEquivOfIsEmpty

def domDomCongrLinearEquiv {ι₁ ι₂} (σ : ι₁ ≃ ι₂) :
    MultilinearMap R (fun _ : ι₁ => M₂) M₃ ≃ₗ[S] MultilinearMap R (fun _ : ι₂ => M₂) M₃ :=
  { (domDomCongrEquiv σ :
      MultilinearMap R (fun _ : ι₁ => M₂) M₃ ≃+ MultilinearMap R (fun _ : ι₂ => M₂) M₃) with
    map_smul' := fun c f => by
      ext
      simp [MultilinearMap.domDomCongr] }
#align multilinear_map.dom_dom_congr_linear_equiv MultilinearMap.domDomCongrLinearEquiv

def compLinearMapₗ (f : Π (i : ι), M₁ i →ₗ[R] M₁' i) :
    (MultilinearMap R M₁' M₂) →ₗ[R] MultilinearMap R M₁ M₂ where
  toFun := fun g ↦ g.compLinearMap f
  map_add' := fun _ _ ↦ rfl
  map_smul' := fun _ _ ↦ rfl

/-- If `f` is a collection of linear maps, then the construction `MultilinearMap.compLinearMap`
sending a multilinear map `g` to `g (f₁ ⬝ , ..., fₙ ⬝ )` is linear in `g` and multilinear in
`f₁, ..., fₙ`. -/
@[simps] def compLinearMapMultilinear :
  @MultilinearMap R ι (fun i ↦ M₁ i →ₗ[R] M₁' i)
    ((MultilinearMap R M₁' M₂) →ₗ[R] MultilinearMap R M₁ M₂) _ _ _
      (fun i ↦ LinearMap.module) _ where
  toFun := MultilinearMap.compLinearMapₗ
  map_add' := by
    intro _ f i f₁ f₂
    ext g x
    change (g fun j ↦ update f i (f₁ + f₂) j <| x j) =
        (g fun j ↦ update f i f₁ j <|x j) + g fun j ↦ update f i f₂ j (x j)
    let c : Π (i : ι), (M₁ i →ₗ[R] M₁' i) → M₁' i := fun i f ↦ f (x i)
    convert g.map_add (fun j ↦ f j (x j)) i (f₁ (x i)) (f₂ (x i)) with j j j
    · exact Function.apply_update c f i (f₁ + f₂) j
    · exact Function.apply_update c f i f₁ j
    · exact Function.apply_update c f i f₂ j
  map_smul' := by
    intro _ f i a f₀
    ext g x
    change (g fun j ↦ update f i (a • f₀) j <| x j) = a • g fun j ↦ update f i f₀ j (x j)
    let c : Π (i : ι), (M₁ i →ₗ[R] M₁' i) → M₁' i := fun i f ↦ f (x i)
    convert g.map_smul (fun j ↦ f j (x j)) i a (f₀ (x i)) with j j j
    · exact Function.apply_update c f i (a • f₀) j
    · exact Function.apply_update c f i f₀ j

/--
Let `M₁ᵢ` and `M₁ᵢ'` be two families of `R`-modules and `M₂` an `R`-module.
Let us denote `Π i, M₁ᵢ` and `Π i, M₁ᵢ'` by `M` and `M'` respectively.
If `g` is a multilinear map `M' → M₂`, then `g` can be reinterpreted as a multilinear
map from `Π i, M₁ᵢ ⟶ M₁ᵢ'` to `M ⟶ M₂` via `(fᵢ) ↦ v ↦ g(fᵢ vᵢ)`.
-/
@[simps!] def piLinearMap :
    MultilinearMap R M₁' M₂ →ₗ[R]
    MultilinearMap R (fun i ↦ M₁ i →ₗ[R] M₁' i) (MultilinearMap R M₁ M₂) where
  toFun g := (LinearMap.applyₗ g).compMultilinearMap compLinearMapMultilinear
  map_add' := by aesop
  map_smul' := by aesop

end

/-- If one multiplies by `c i` the coordinates in a finset `s`, then the image under a multilinear
map is multiplied by `∏ i in s, c i`. This is mainly an auxiliary statement to prove the result when
`s = univ`, given in `map_smul_univ`, although it can be useful in its own right as it does not
require the index set `ι` to be finite. -/
theorem map_piecewise_smul [DecidableEq ι] (c : ι → R) (m : ∀ i, M₁ i) (s : Finset ι) :
    f (s.piecewise (fun i => c i • m i) m) = (∏ i in s, c i) • f m := by
  refine' s.induction_on (by simp) _
  intro j s j_not_mem_s Hrec
  have A :
    Function.update (s.piecewise (fun i => c i • m i) m) j (m j) =
      s.piecewise (fun i => c i • m i) m := by
    ext i
    by_cases h : i = j
    · rw [h]
      simp [j_not_mem_s]
    · simp [h]
  rw [s.piecewise_insert, f.map_smul, A, Hrec]
  simp [j_not_mem_s, mul_smul]
#align multilinear_map.map_piecewise_smul MultilinearMap.map_piecewise_smul

def mkPiAlgebra : MultilinearMap R (fun _ : ι => A) A where
  toFun m := ∏ i, m i
  map_add' m i x y := by simp [Finset.prod_update_of_mem, add_mul]
  map_smul' m i c x := by simp [Finset.prod_update_of_mem]
#align multilinear_map.mk_pi_algebra MultilinearMap.mkPiAlgebra

def mkPiAlgebraFin : MultilinearMap R (fun _ : Fin n => A) A where
  toFun m := (List.ofFn m).prod
  map_add' {dec} m i x y := by
    rw [Subsingleton.elim dec (by infer_instance)]
    have : (List.finRange n).indexOf i < n := by
      simpa using List.indexOf_lt_length.2 (List.mem_finRange i)
    simp [List.ofFn_eq_map, (List.nodup_finRange n).map_update, List.prod_set, add_mul, this,
      mul_add, add_mul]
  map_smul' {dec} m i c x := by
    rw [Subsingleton.elim dec (by infer_instance)]
    have : (List.finRange n).indexOf i < n := by
      simpa using List.indexOf_lt_length.2 (List.mem_finRange i)
    simp [List.ofFn_eq_map, (List.nodup_finRange n).map_update, List.prod_set, this]
#align multilinear_map.mk_pi_algebra_fin MultilinearMap.mkPiAlgebraFin

def smulRight (f : MultilinearMap R M₁ R) (z : M₂) : MultilinearMap R M₁ M₂ :=
  (LinearMap.smulRight LinearMap.id z).compMultilinearMap f
#align multilinear_map.smul_right MultilinearMap.smulRight

def mkPiRing [Fintype ι] (z : M₂) : MultilinearMap R (fun _ : ι => R) M₂ :=
  (MultilinearMap.mkPiAlgebra R ι R).smulRight z
#align multilinear_map.mk_pi_ring MultilinearMap.mkPiRing

def piRingEquiv [Fintype ι] : M₂ ≃ₗ[R] MultilinearMap R (fun _ : ι => R) M₂ where
  toFun z := MultilinearMap.mkPiRing R ι z
  invFun f := f fun _ => 1
  map_add' z z' := by
    ext m
    simp [smul_add]
  map_smul' c z := by
    ext m
    simp [smul_smul, mul_comm]
  left_inv z := by simp
  right_inv f := f.mkPiRing_apply_one_eq_self
#align multilinear_map.pi_ring_equiv MultilinearMap.piRingEquiv

def LinearMap.uncurryLeft (f : M 0 →ₗ[R] MultilinearMap R (fun i : Fin n => M i.succ) M₂) :
    MultilinearMap R M M₂ where
  toFun m := f (m 0) (tail m)
  map_add' := @fun dec m i x y => by
    -- Porting note: `clear` not necessary in Lean 3 due to not being in the instance cache
    rw [Subsingleton.elim dec (by clear dec; infer_instance)]; clear dec
    by_cases h : i = 0
    · subst i
      simp only [update_same, map_add, tail_update_zero, MultilinearMap.add_apply]
    · simp_rw [update_noteq (Ne.symm h)]
      revert x y
      rw [← succ_pred i h]
      intro x y
      rw [tail_update_succ, MultilinearMap.map_add, tail_update_succ, tail_update_succ]
  map_smul' := @fun dec m i c x => by
    -- Porting note: `clear` not necessary in Lean 3 due to not being in the instance cache
    rw [Subsingleton.elim dec (by clear dec; infer_instance)]; clear dec
    by_cases h : i = 0
    · subst i
      simp only [update_same, map_smul, tail_update_zero, MultilinearMap.smul_apply]
    · simp_rw [update_noteq (Ne.symm h)]
      revert x
      rw [← succ_pred i h]
      intro x
      rw [tail_update_succ, tail_update_succ, MultilinearMap.map_smul]
#align linear_map.uncurry_left LinearMap.uncurryLeft

def MultilinearMap.curryLeft (f : MultilinearMap R M M₂) :
    M 0 →ₗ[R] MultilinearMap R (fun i : Fin n => M i.succ) M₂ where
  toFun x :=
    { toFun := fun m => f (cons x m)
      map_add' := @fun dec m i y y' => by
        -- Porting note: `clear` not necessary in Lean 3 due to not being in the instance cache
        rw [Subsingleton.elim dec (by clear dec; infer_instance)]
        simp
      map_smul' := @fun dec m i y c => by
        -- Porting note: `clear` not necessary in Lean 3 due to not being in the instance cache
        rw [Subsingleton.elim dec (by clear dec; infer_instance)]
        simp }
  map_add' x y := by
    ext m
    exact cons_add f m x y
  map_smul' c x := by
    ext m
    exact cons_smul f m c x
#align multilinear_map.curry_left MultilinearMap.curryLeft

def multilinearCurryLeftEquiv :
    (M 0 →ₗ[R] MultilinearMap R (fun i : Fin n => M i.succ) M₂) ≃ₗ[R] MultilinearMap R M M₂ where
  toFun := LinearMap.uncurryLeft
  map_add' f₁ f₂ := by
    ext m
    rfl
  map_smul' c f := by
    ext m
    rfl
  invFun := MultilinearMap.curryLeft
  left_inv := LinearMap.curry_uncurryLeft
  right_inv := MultilinearMap.uncurry_curryLeft
#align multilinear_curry_left_equiv multilinearCurryLeftEquiv

def MultilinearMap.uncurryRight
    (f : MultilinearMap R (fun i : Fin n => M (castSucc i)) (M (last n) →ₗ[R] M₂)) :
    MultilinearMap R M M₂ where
  toFun m := f (init m) (m (last n))
  map_add' {dec} m i x y := by
    -- Porting note: `clear` not necessary in Lean 3 due to not being in the instance cache
    rw [Subsingleton.elim dec (by clear dec; infer_instance)]; clear dec
    by_cases h : i.val < n
    · have : last n ≠ i := Ne.symm (ne_of_lt h)
      simp_rw [update_noteq this]
      revert x y
      rw [(castSucc_castLT i h).symm]
      intro x y
      rw [init_update_castSucc, MultilinearMap.map_add, init_update_castSucc,
        init_update_castSucc, LinearMap.add_apply]
    · revert x y
      rw [eq_last_of_not_lt h]
      intro x y
      simp_rw [init_update_last, update_same, LinearMap.map_add]
  map_smul' {dec} m i c x := by
    -- Porting note: `clear` not necessary in Lean 3 due to not being in the instance cache
    rw [Subsingleton.elim dec (by clear dec; infer_instance)]; clear dec
    by_cases h : i.val < n
    · have : last n ≠ i := Ne.symm (ne_of_lt h)
      simp_rw [update_noteq this]
      revert x
      rw [(castSucc_castLT i h).symm]
      intro x
      rw [init_update_castSucc, init_update_castSucc, MultilinearMap.map_smul,
        LinearMap.smul_apply]
    · revert x
      rw [eq_last_of_not_lt h]
      intro x
      simp_rw [update_same, init_update_last, map_smul]
#align multilinear_map.uncurry_right MultilinearMap.uncurryRight

def MultilinearMap.curryRight (f : MultilinearMap R M M₂) :
    MultilinearMap R (fun i : Fin n => M (Fin.castSucc i)) (M (last n) →ₗ[R] M₂) where
  toFun m :=
    { toFun := fun x => f (snoc m x)
      map_add' := fun x y => by simp_rw [f.snoc_add]
      map_smul' := fun c x => by simp only [f.snoc_smul, RingHom.id_apply] }
  map_add' := @fun dec m i x y => by
    rw [Subsingleton.elim dec (by clear dec; infer_instance)]; clear dec
    ext z
    change f (snoc (update m i (x + y)) z) = f (snoc (update m i x) z) + f (snoc (update m i y) z)
    rw [snoc_update, snoc_update, snoc_update, f.map_add]
  map_smul' := @fun dec m i c x => by
    rw [Subsingleton.elim dec (by clear dec; infer_instance)]; clear dec
    ext z
    change f (snoc (update m i (c • x)) z) = c • f (snoc (update m i x) z)
    rw [snoc_update, snoc_update, f.map_smul]
#align multilinear_map.curry_right MultilinearMap.curryRight

def multilinearCurryRightEquiv :
    MultilinearMap R (fun i : Fin n => M (castSucc i)) (M (last n) →ₗ[R] M₂) ≃ₗ[R]
      MultilinearMap R M M₂ where
  toFun := MultilinearMap.uncurryRight
  map_add' f₁ f₂ := by
    ext m
    rfl
  map_smul' c f := by
    ext m
    rw [smul_apply]
    rfl
  invFun := MultilinearMap.curryRight
  left_inv := MultilinearMap.curry_uncurryRight
  right_inv := MultilinearMap.uncurry_curryRight
#align multilinear_curry_right_equiv multilinearCurryRightEquiv

def currySum (f : MultilinearMap R (fun _ : Sum ι ι' => M') M₂) :
    MultilinearMap R (fun _ : ι => M') (MultilinearMap R (fun _ : ι' => M') M₂) where
  toFun u :=
    { toFun := fun v => f (Sum.elim u v)
      map_add' := fun v i x y => by
        letI := Classical.decEq ι
        simp only [← Sum.update_elim_inr, f.map_add]
      map_smul' := fun v i c x => by
        letI := Classical.decEq ι
        simp only [← Sum.update_elim_inr, f.map_smul] }
  map_add' u i x y :=
    ext fun v => by
      letI := Classical.decEq ι'
      simp only [MultilinearMap.coe_mk, add_apply, ← Sum.update_elim_inl, f.map_add]
  map_smul' u i c x :=
    ext fun v => by
      letI := Classical.decEq ι'
      simp only [MultilinearMap.coe_mk, smul_apply, ← Sum.update_elim_inl, f.map_smul]
#align multilinear_map.curry_sum MultilinearMap.currySum

def uncurrySum (f : MultilinearMap R (fun _ : ι => M') (MultilinearMap R (fun _ : ι' => M') M₂)) :
    MultilinearMap R (fun _ : Sum ι ι' => M') M₂ where
  toFun u := f (u ∘ Sum.inl) (u ∘ Sum.inr)
  map_add' u i x y := by
    letI := (@Sum.inl_injective ι ι').decidableEq
    letI := (@Sum.inr_injective ι ι').decidableEq
    cases i <;>
      simp only [MultilinearMap.map_add, add_apply, Sum.update_inl_comp_inl,
        Sum.update_inl_comp_inr, Sum.update_inr_comp_inl, Sum.update_inr_comp_inr]
  map_smul' u i c x := by
    letI := (@Sum.inl_injective ι ι').decidableEq
    letI := (@Sum.inr_injective ι ι').decidableEq
    cases i <;>
      simp only [MultilinearMap.map_smul, smul_apply, Sum.update_inl_comp_inl,
        Sum.update_inl_comp_inr, Sum.update_inr_comp_inl, Sum.update_inr_comp_inr]
#align multilinear_map.uncurry_sum MultilinearMap.uncurrySum

def currySumEquiv :
    MultilinearMap R (fun _ : Sum ι ι' => M') M₂ ≃ₗ[R]
      MultilinearMap R (fun _ : ι => M') (MultilinearMap R (fun _ : ι' => M') M₂) where
  toFun := currySum
  invFun := uncurrySum
  left_inv f := ext fun u => by simp
  right_inv f := by
    ext
    simp
  map_add' f g := by
    ext
    rfl
  map_smul' c f := by
    ext
    rfl
#align multilinear_map.curry_sum_equiv MultilinearMap.currySumEquiv

def curryFinFinset {k l n : ℕ} {s : Finset (Fin n)} (hk : s.card = k) (hl : sᶜ.card = l) :
    MultilinearMap R (fun _ : Fin n => M') M₂ ≃ₗ[R]
      MultilinearMap R (fun _ : Fin k => M') (MultilinearMap R (fun _ : Fin l => M') M₂) :=
  (domDomCongrLinearEquiv R R M' M₂ (finSumEquivOfFinset hk hl).symm).trans
    (currySumEquiv R (Fin k) M₂ M' (Fin l))
#align multilinear_map.curry_fin_finset MultilinearMap.curryFinFinset

def map [Nonempty ι] (f : MultilinearMap R M₁ M₂) (p : ∀ i, Submodule R (M₁ i)) : SubMulAction R M₂
    where
  carrier := f '' { v | ∀ i, v i ∈ p i }
  smul_mem' := fun c _ ⟨x, hx, hf⟩ => by
    let ⟨i⟩ := ‹Nonempty ι›
    letI := Classical.decEq ι
    refine' ⟨update x i (c • x i), fun j => if hij : j = i then _ else _, hf ▸ _⟩
    · rw [hij, update_same]
      exact (p i).smul_mem _ (hx i)
    · rw [update_noteq hij]
      exact hx j
    · rw [f.map_smul, update_eq_self]
#align multilinear_map.map MultilinearMap.map

def range [Nonempty ι] (f : MultilinearMap R M₁ M₂) : SubMulAction R M₂ :=
  f.map fun _ => ⊤
#align multilinear_map.range MultilinearMap.range

structure by pointwise addition and multiplication.

## Main definitions

structure MultilinearMap (R : Type uR) {ι : Type uι} (M₁ : ι → Type v₁) (M₂ : Type v₂) [Semiring R]
  [∀ i, AddCommMonoid (M₁ i)] [AddCommMonoid M₂] [∀ i, Module R (M₁ i)] [Module R M₂] where
  /-- The underlying multivariate function of a multilinear map. -/
  toFun : (∀ i, M₁ i) → M₂
  /-- A multilinear map is additive in every argument. -/
  map_add' :
    ∀ [DecidableEq ι] (m : ∀ i, M₁ i) (i : ι) (x y : M₁ i),
      toFun (update m i (x + y)) = toFun (update m i x) + toFun (update m i y)
  /-- A multilinear map is compatible with scalar multiplication in every argument. -/
  map_smul' :
    ∀ [DecidableEq ι] (m : ∀ i, M₁ i) (i : ι) (c : R) (x : M₁ i),
      toFun (update m i (c • x)) = c • toFun (update m i x)
#align multilinear_map MultilinearMap