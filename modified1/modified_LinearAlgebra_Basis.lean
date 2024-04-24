def coord : M →ₗ[R] R :=
  Finsupp.lapply i ∘ₗ ↑b.repr
#align basis.coord Basis.coord

def sumCoords : M →ₗ[R] R :=
  (Finsupp.lsum ℕ fun _ => LinearMap.id) ∘ₗ (b.repr : M →ₗ[R] ι →₀ R)
#align basis.sum_coords Basis.sumCoords

def map : Basis ι R M' :=
  ofRepr (f.symm.trans b.repr)
#align basis.map Basis.map

def mapCoeffs : Basis ι R' M := by
  letI : Module R' R := Module.compHom R (↑f.symm : R' →+* R)
  haveI : IsScalarTower R' R M :=
    { smul_assoc := fun x y z => by
        -- Porting note: `dsimp [(· • ·)]` is unavailable because
        --               `HSMul.hsmul` becomes `SMul.smul`.
        change (f.symm x * y) • z = x • (y • z)
        rw [mul_smul, ← h, f.apply_symm_apply] }
  exact ofRepr <| (b.repr.restrictScalars R').trans <|
    Finsupp.mapRange.linearEquiv (Module.compHom.toLinearEquiv f.symm).symm
#align basis.map_coeffs Basis.mapCoeffs

def reindex : Basis ι' R M :=
  .ofRepr (b.repr.trans (Finsupp.domLCongr e))
#align basis.reindex Basis.reindex

def reindexRange : Basis (range b) R M :=
  haveI := Classical.dec (Nontrivial R)
  if h : Nontrivial R then
    letI := h
    b.reindex (Equiv.ofInjective b (Basis.injective b))
  else
    letI : Subsingleton R := not_nontrivial_iff_subsingleton.mp h
    .ofRepr (Module.subsingletonEquiv R M (range b))
#align basis.reindex_range Basis.reindexRange

def reindexFinsetRange : Basis (Finset.univ.image b) R M :=
  b.reindexRange.reindex ((Equiv.refl M).subtypeEquiv (by simp))
#align basis.reindex_finset_range Basis.reindexFinsetRange

def constr : (ι → M') ≃ₗ[S] M →ₗ[R] M' where
  toFun f := (Finsupp.total M' M' R id).comp <| Finsupp.lmapDomain R R f ∘ₗ ↑b.repr
  invFun f i := f (b i)
  left_inv f := by
    ext
    simp
  right_inv f := by
    refine' b.ext fun i => _
    simp
  map_add' f g := by
    refine' b.ext fun i => _
    simp
  map_smul' c f := by
    refine' b.ext fun i => _
    simp
#align basis.constr Basis.constr

def (f : ι → M') :
    constr (M' := M') b S f = Finsupp.total M' M' R id ∘ₗ Finsupp.lmapDomain R R f ∘ₗ ↑b.repr :=
  rfl
#align basis.constr_def Basis.constr_def

def S f, LinearMap.range_comp, LinearMap.range_comp, LinearEquiv.range, ←
    Finsupp.supported_univ, Finsupp.lmapDomain_supported, ← Set.image_univ, ←
    Finsupp.span_image_eq_map_total, Set.image_id]
#align basis.constr_range Basis.constr_range

def equiv : M ≃ₗ[R] M' :=
  b.repr.trans (b'.reindex e.symm).repr.symm
#align basis.equiv Basis.equiv

def prod : Basis (Sum ι ι') R (M × M') :=
  ofRepr ((b.repr.prod b'.repr).trans (Finsupp.sumFinsuppLEquivProdFinsupp R).symm)
#align basis.prod Basis.prod

def singleton (ι R : Type*) [Unique ι] [Semiring R] : Basis ι R R :=
  ofRepr
    { toFun := fun x => Finsupp.single default x
      invFun := fun f => f default
      left_inv := fun x => by simp
      right_inv := fun f => Finsupp.unique_ext (by simp)
      map_add' := fun x y => by simp
      map_smul' := fun c x => by simp }
#align basis.singleton Basis.singleton

def empty [Subsingleton M] [IsEmpty ι] : Basis ι R M :=
  ofRepr 0
#align basis.empty Basis.empty

def Basis.equivFun [Finite ι] (b : Basis ι R M) : M ≃ₗ[R] ι → R :=
  LinearEquiv.trans b.repr
    ({ Finsupp.equivFunOnFinite with
        toFun := (↑)
        map_add' := Finsupp.coe_add
        map_smul' := Finsupp.coe_smul } :
      (ι →₀ R) ≃ₗ[R] ι → R)
#align basis.equiv_fun Basis.equivFun

def Module.fintypeOfFintype [Fintype ι] (b : Basis ι R M) [Fintype R] : Fintype M :=
  haveI := Classical.decEq ι
  Fintype.ofEquiv _ b.equivFun.toEquiv.symm
#align module.fintype_of_fintype Module.fintypeOfFintype

def Basis.ofEquivFun [Finite ι] (e : M ≃ₗ[R] ι → R) : Basis ι R M :=
  .ofRepr <| e.trans <| LinearEquiv.symm <| Finsupp.linearEquivFunOnFinite R R ι
#align basis.of_equiv_fun Basis.ofEquivFun

def equiv' (f : M → M') (g : M' → M) (hf : ∀ i, f (b i) ∈ range b') (hg : ∀ i, g (b' i) ∈ range b)
    (hgf : ∀ i, g (f (b i)) = b i) (hfg : ∀ i, f (g (b' i)) = b' i) : M ≃ₗ[R] M' :=
  { constr (M' := M') b R (f ∘ b) with
    invFun := constr (M' := M) b' R (g ∘ b')
    left_inv :=
      have : (constr (M' := M) b' R (g ∘ b')).comp (constr (M' := M') b R (f ∘ b)) = LinearMap.id :=
        b.ext fun i =>
          Exists.elim (hf i) fun i' hi' => by
            rw [LinearMap.comp_apply, b.constr_basis, Function.comp_apply, ← hi', b'.constr_basis,
              Function.comp_apply, hi', hgf, LinearMap.id_apply]
      fun x => congr_arg (fun h : M →ₗ[R] M => h x) this
    right_inv :=
      have : (constr (M' := M') b R (f ∘ b)).comp (constr (M' := M) b' R (g ∘ b')) = LinearMap.id :=
        b'.ext fun i =>
          Exists.elim (hg i) fun i' hi' => by
            rw [LinearMap.comp_apply, b'.constr_basis, Function.comp_apply, ← hi', b.constr_basis,
              Function.comp_apply, hi', hfg, LinearMap.id_apply]
      fun x => congr_arg (fun h : M' →ₗ[R] M' => h x) this }
#align basis.equiv' Basis.equiv'

def mk : Basis ι R M :=
  .ofRepr
    { hli.repr.comp (LinearMap.id.codRestrict _ fun _ => hsp Submodule.mem_top) with
      invFun := Finsupp.total _ _ _ v
      left_inv := fun x => hli.total_repr ⟨x, _⟩
      right_inv := fun _ => hli.repr_eq rfl }
#align basis.mk Basis.mk

def span : Basis ι R (span R (range v)) :=
  Basis.mk (linearIndependent_span hli) <| by
    intro x _
    have : ∀ i, v i ∈ span R (range v) := fun i ↦ subset_span (Set.mem_range_self _)
    have h₁ : (((↑) : span R (range v) → M) '' range fun i => ⟨v i, this i⟩) = range v := by
      simp only [SetLike.coe_sort_coe, ← Set.range_comp]
      rfl
    have h₂ : map (Submodule.subtype (span R (range v))) (span R (range fun i => ⟨v i, this i⟩)) =
        span R (range v) := by
      rw [← span_image, Submodule.coeSubtype]
      -- Porting note: why doesn't `rw [h₁]` work here?
      exact congr_arg _ h₁
    have h₃ : (x : M) ∈ map (Submodule.subtype (span R (range v)))
        (span R (Set.range fun i => Subtype.mk (v i) _)) := by
      rw [h₂]
      apply Subtype.mem x
    rcases mem_map.1 h₃ with ⟨y, hy₁, hy₂⟩
    have h_x_eq_y : x = y := by
      rw [Subtype.ext_iff, ← hy₂]
      simp
    rwa [h_x_eq_y]
#align basis.span Basis.span

def groupSMul {G : Type*} [Group G] [DistribMulAction G R] [DistribMulAction G M]
    [IsScalarTower G R M] [SMulCommClass G R M] (v : Basis ι R M) (w : ι → G) : Basis ι R M :=
  Basis.mk (LinearIndependent.group_smul v.linearIndependent w) (groupSMul_span_eq_top v.span_eq).ge
#align basis.group_smul Basis.groupSMul

def unitsSMul (v : Basis ι R M) (w : ι → Rˣ) : Basis ι R M :=
  Basis.mk (LinearIndependent.units_smul v.linearIndependent w)
    (units_smul_span_eq_top v.span_eq).ge
#align basis.units_smul Basis.unitsSMul

def isUnitSMul (v : Basis ι R M) {w : ι → R} (hw : ∀ i, IsUnit (w i)) : Basis ι R M :=
  unitsSMul v fun i => (hw i).unit
#align basis.is_unit_smul Basis.isUnitSMul

def mkFinCons {n : ℕ} {N : Submodule R M} (y : M) (b : Basis (Fin n) R N)
    (hli : ∀ (c : R), ∀ x ∈ N, c • y + x = 0 → c = 0) (hsp : ∀ z : M, ∃ c : R, z + c • y ∈ N) :
    Basis (Fin (n + 1)) R M :=
  have span_b : Submodule.span R (Set.range (N.subtype ∘ b)) = N := by
    rw [Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  Basis.mk (v := Fin.cons y (N.subtype ∘ b))
    ((b.linearIndependent.map' N.subtype (Submodule.ker_subtype _)).fin_cons' _ _
      (by
        rintro c ⟨x, hx⟩ hc
        rw [span_b] at hx
        exact hli c x hx hc))
    fun x _ => by
      rw [Fin.range_cons, Submodule.mem_span_insert', span_b]
      exact hsp x
#align basis.mk_fin_cons Basis.mkFinCons

def mkFinConsOfLE {n : ℕ} {N O : Submodule R M} (y : M) (yO : y ∈ O)
    (b : Basis (Fin n) R N) (hNO : N ≤ O) (hli : ∀ (c : R), ∀ x ∈ N, c • y + x = 0 → c = 0)
    (hsp : ∀ z ∈ O, ∃ c : R, z + c • y ∈ N) : Basis (Fin (n + 1)) R O :=
  mkFinCons ⟨y, yO⟩ (b.map (Submodule.comapSubtypeEquivOfLe hNO).symm)
    (fun c x hc hx => hli c x (Submodule.mem_comap.mp hc) (congr_arg ((↑) : O → M) hx))
    fun z => hsp z z.2
#align basis.mk_fin_cons_of_le Basis.mkFinConsOfLE

def finTwoProd (R : Type*) [Semiring R] : Basis (Fin 2) R (R × R) :=
  Basis.ofEquivFun (LinearEquiv.finTwoArrow R R).symm
#align basis.fin_two_prod Basis.finTwoProd

def Submodule.inductionOnRankAux (b : Basis ι R M) (P : Submodule R M → Sort*)
    (ih : ∀ N : Submodule R M,
      (∀ N' ≤ N, ∀ x ∈ N, (∀ (c : R), ∀ y ∈ N', c • x + y = (0 : M) → c = 0) → P N') → P N)
    (n : ℕ) (N : Submodule R M)
    (rank_le : ∀ {m : ℕ} (v : Fin m → N), LinearIndependent R ((↑) ∘ v : Fin m → M) → m ≤ n) :
    P N := by
  haveI : DecidableEq M := Classical.decEq M
  have Pbot : P ⊥ := by
    apply ih
    intro N _ x x_mem x_ortho
    exfalso
    rw [mem_bot] at x_mem
    simpa [x_mem] using x_ortho 1 0 N.zero_mem
  induction' n with n rank_ih generalizing N
  · suffices N = ⊥ by rwa [this]
    apply Basis.eq_bot_of_rank_eq_zero b _ fun m hv => Nat.le_zero.mp (rank_le _ hv)
  apply ih
  intro N' N'_le x x_mem x_ortho
  apply rank_ih
  intro m v hli
  refine' Nat.succ_le_succ_iff.mp (rank_le (Fin.cons ⟨x, x_mem⟩ fun i => ⟨v i, N'_le (v i).2⟩) _)
  convert hli.fin_cons' x _ ?_
  · ext i
    refine' Fin.cases _ _ i <;> simp
  · intro c y hcy
    refine' x_ortho c y (Submodule.span_le.mpr _ y.2) hcy
    rintro _ ⟨z, rfl⟩
    exact (v z).2
#align submodule.induction_on_rank_aux Submodule.inductionOnRankAux

def Basis.restrictScalars : Basis ι R (span R (Set.range b)) :=
  Basis.span (b.linearIndependent.restrict_scalars (smul_left_injective R one_ne_zero))
#align basis.restrict_scalars Basis.restrictScalars

structure Basis where
  /-- `Basis.ofRepr` constructs a basis given an assignment of coordinates to each vector. -/
  ofRepr ::
    /-- `repr` is the linear equivalence sending a vector `x` to its coordinates:
    the `c`s such that `x = ∑ i, c i`. -/
    repr : M ≃ₗ[R] ι →₀ R
#align basis Basis