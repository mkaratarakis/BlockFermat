def mk₂'ₛₗ (f : M → N → P) (H1 : ∀ m₁ m₂ n, f (m₁ + m₂) n = f m₁ n + f m₂ n)
    (H2 : ∀ (c : R) (m n), f (c • m) n = ρ₁₂ c • f m n)
    (H3 : ∀ m n₁ n₂, f m (n₁ + n₂) = f m n₁ + f m n₂)
    (H4 : ∀ (c : S) (m n), f m (c • n) = σ₁₂ c • f m n) : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P
    where
  toFun m :=
    { toFun := f m
      map_add' := H3 m
      map_smul' := fun c => H4 c m }
  map_add' m₁ m₂ := LinearMap.ext <| H1 m₁ m₂
  map_smul' c m := LinearMap.ext <| H2 c m
#align linear_map.mk₂'ₛₗ LinearMap.mk₂'ₛₗ

def mk₂' (f : M → N → Pₗ) (H1 : ∀ m₁ m₂ n, f (m₁ + m₂) n = f m₁ n + f m₂ n)
    (H2 : ∀ (c : R) (m n), f (c • m) n = c • f m n)
    (H3 : ∀ m n₁ n₂, f m (n₁ + n₂) = f m n₁ + f m n₂)
    (H4 : ∀ (c : S) (m n), f m (c • n) = c • f m n) : M →ₗ[R] N →ₗ[S] Pₗ :=
  mk₂'ₛₗ (RingHom.id R) (RingHom.id S) f H1 H2 H3 H4
#align linear_map.mk₂' LinearMap.mk₂'

def flip (f : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P) : N →ₛₗ[σ₁₂] M →ₛₗ[ρ₁₂] P :=
  mk₂'ₛₗ σ₁₂ ρ₁₂ (fun n m => f m n) (fun n₁ n₂ m => (f m).map_add _ _)
    (fun c n  m  => (f m).map_smulₛₗ _ _)
    (fun n m₁ m₂ => by simp only [map_add, add_apply])
    -- Note: #8386 changed `map_smulₛₗ` into `map_smulₛₗ _`.

def domRestrict₂ (f : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P) (q : Submodule S N) : M →ₛₗ[ρ₁₂] q →ₛₗ[σ₁₂] P
    where
  toFun m := (f m).domRestrict q
  map_add' m₁ m₂ := LinearMap.ext fun _ => by simp only [map_add, domRestrict_apply, add_apply]
  map_smul' c m :=
    LinearMap.ext fun _ => by simp only [f.map_smulₛₗ, domRestrict_apply, smul_apply]
#align linear_map.dom_restrict₂ LinearMap.domRestrict₂

def domRestrict₁₂ (f : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P) (p : Submodule R M) (q : Submodule S N) :
    p →ₛₗ[ρ₁₂] q →ₛₗ[σ₁₂] P :=
  (f.domRestrict p).domRestrict₂ q
#align linear_map.dom_restrict₁₂ LinearMap.domRestrict₁₂

def restrictScalars₁₂ (B : M →ₗ[R] N →ₗ[S] Pₗ) : M →ₗ[R'] N →ₗ[S'] Pₗ :=
  LinearMap.mk₂' R' S'
    (B · ·)
    B.map_add₂
    (fun r' m _ ↦ by
      dsimp only
      rw [← smul_one_smul R r' m, map_smul₂, smul_one_smul])
    (fun _ ↦ map_add _)
    (fun _ x ↦ (B x).map_smul_of_tower _)

theorem restrictScalars₁₂_injective : Function.Injective
    (LinearMap.restrictScalars₁₂ R' S' : (M →ₗ[R] N →ₗ[S] Pₗ) → (M →ₗ[R'] N →ₗ[S'] Pₗ)) :=
  fun _ _ h ↦ ext₂ (congr_fun₂ h : _)

@[simp]
theorem restrictScalars₁₂_inj {B B' : M →ₗ[R] N →ₗ[S] Pₗ} :
    B.restrictScalars₁₂ R' S' = B'.restrictScalars₁₂ R' S' ↔ B = B' :=
  (restrictScalars₁₂_injective R' S').eq_iff

end restrictScalars

end Semiring

section CommSemiring

variable {R : Type*} [CommSemiring R] {R₂ : Type*} [CommSemiring R₂]
variable {R₃ : Type*} [CommSemiring R₃] {R₄ : Type*} [CommSemiring R₄]
variable {M : Type*} {N : Type*} {P : Type*} {Q : Type*}
variable {Mₗ : Type*} {Nₗ : Type*} {Pₗ : Type*} {Qₗ Qₗ' : Type*}
variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q]
variable [AddCommMonoid Mₗ] [AddCommMonoid Nₗ] [AddCommMonoid Pₗ]
variable [AddCommMonoid Qₗ] [AddCommMonoid Qₗ']
variable [Module R M] [Module R₂ N] [Module R₃ P] [Module R₄ Q]
variable [Module R Mₗ] [Module R Nₗ] [Module R Pₗ] [Module R Qₗ] [Module R Qₗ']
variable {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃}
variable {σ₄₂ : R₄ →+* R₂} {σ₄₃ : R₄ →+* R₃}
variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomCompTriple σ₄₂ σ₂₃ σ₄₃]
variable (R)

/-- Create a bilinear map from a function that is linear in each component.

This is a shorthand for `mk₂'` for the common case when `R = S`. -/
def mk₂ (f : M → Nₗ → Pₗ) (H1 : ∀ m₁ m₂ n, f (m₁ + m₂) n = f m₁ n + f m₂ n)
    (H2 : ∀ (c : R) (m n), f (c • m) n = c • f m n)
    (H3 : ∀ m n₁ n₂, f m (n₁ + n₂) = f m n₁ + f m n₂)
    (H4 : ∀ (c : R) (m n), f m (c • n) = c • f m n) : M →ₗ[R] Nₗ →ₗ[R] Pₗ :=
  mk₂' R R f H1 H2 H3 H4
#align linear_map.mk₂ LinearMap.mk₂

def lflip : (M →ₛₗ[σ₁₃] N →ₛₗ[σ₂₃] P) →ₗ[R₃] N →ₛₗ[σ₂₃] M →ₛₗ[σ₁₃] P
    where
  toFun := flip
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
#align linear_map.lflip LinearMap.lflip

def lcomp (f : M →ₗ[R] Nₗ) : (Nₗ →ₗ[R] Pₗ) →ₗ[R] M →ₗ[R] Pₗ :=
  flip <| LinearMap.comp (flip id) f
#align linear_map.lcomp LinearMap.lcomp

def lcompₛₗ (f : M →ₛₗ[σ₁₂] N) : (N →ₛₗ[σ₂₃] P) →ₗ[R₃] M →ₛₗ[σ₁₃] P :=
  flip <| LinearMap.comp (flip id) f
#align linear_map.lcompₛₗ LinearMap.lcompₛₗ

def llcomp : (Nₗ →ₗ[R] Pₗ) →ₗ[R] (M →ₗ[R] Nₗ) →ₗ[R] M →ₗ[R] Pₗ :=
  flip
    { toFun := lcomp R Pₗ
      map_add' := fun _f _f' => ext₂ fun g _x => g.map_add _ _
      map_smul' := fun (_c : R) _f => ext₂ fun g _x => g.map_smul _ _ }
#align linear_map.llcomp LinearMap.llcomp

def compl₂ (g : Q →ₛₗ[σ₄₂] N) : M →ₛₗ[σ₁₃] Q →ₛₗ[σ₄₃] P :=
  (lcompₛₗ _ _ g).comp f
#align linear_map.compl₂ LinearMap.compl₂

def compl₁₂ (f : Mₗ →ₗ[R] Nₗ →ₗ[R] Pₗ) (g : Qₗ →ₗ[R] Mₗ) (g' : Qₗ' →ₗ[R] Nₗ) :
    Qₗ →ₗ[R] Qₗ' →ₗ[R] Pₗ :=
  (f.comp g).compl₂ g'
#align linear_map.compl₁₂ LinearMap.compl₁₂

def compr₂ (f : M →ₗ[R] Nₗ →ₗ[R] Pₗ) (g : Pₗ →ₗ[R] Qₗ) : M →ₗ[R] Nₗ →ₗ[R] Qₗ :=
  llcomp R Nₗ Pₗ Qₗ g ∘ₗ f
#align linear_map.compr₂ LinearMap.compr₂

def lsmul : R →ₗ[R] M →ₗ[R] M :=
  mk₂ R (· • ·) add_smul (fun _ _ _ => mul_smul _ _ _) smul_add fun r s m => by
    simp only [smul_smul, smul_eq_mul, mul_comm]
#align linear_map.lsmul LinearMap.lsmul