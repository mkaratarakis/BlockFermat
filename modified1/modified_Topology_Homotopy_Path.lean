def eval (F : Homotopy p₀ p₁) (t : I) : Path x₀ x₁ where
  toFun := F.toHomotopy.curry t
  source' := by simp
  target' := by simp
#align path.homotopy.eval Path.Homotopy.eval

def refl (p : Path x₀ x₁) : Homotopy p p :=
  ContinuousMap.HomotopyRel.refl p.toContinuousMap {0, 1}
#align path.homotopy.refl Path.Homotopy.refl

def symm (F : Homotopy p₀ p₁) : Homotopy p₁ p₀ :=
  ContinuousMap.HomotopyRel.symm F
#align path.homotopy.symm Path.Homotopy.symm

def trans (F : Homotopy p₀ p₁) (G : Homotopy p₁ p₂) : Homotopy p₀ p₂ :=
  ContinuousMap.HomotopyRel.trans F G
#align path.homotopy.trans Path.Homotopy.trans

def cast {p₀ p₁ q₀ q₁ : Path x₀ x₁} (F : Homotopy p₀ p₁) (h₀ : p₀ = q₀) (h₁ : p₁ = q₁) :
    Homotopy q₀ q₁ :=
  ContinuousMap.HomotopyRel.cast F (congr_arg _ h₀) (congr_arg _ h₁)
#align path.homotopy.cast Path.Homotopy.cast

def hcomp (F : Homotopy p₀ q₀) (G : Homotopy p₁ q₁) : Homotopy (p₀.trans p₁) (q₀.trans q₁) where
  toFun x :=
    if (x.2 : ℝ) ≤ 1 / 2 then (F.eval x.1).extend (2 * x.2) else (G.eval x.1).extend (2 * x.2 - 1)
  continuous_toFun := continuous_if_le (continuous_induced_dom.comp continuous_snd) continuous_const
    (F.toHomotopy.continuous.comp (by continuity)).continuousOn
    (G.toHomotopy.continuous.comp (by continuity)).continuousOn fun x hx => by norm_num [hx]
  map_zero_left x := by simp [Path.trans]
  map_one_left x := by simp [Path.trans]
  prop' x t ht := by
    cases' ht with ht ht
    · set_option tactic.skipAssignedInstances false in norm_num [ht]
    · rw [Set.mem_singleton_iff] at ht
      set_option tactic.skipAssignedInstances false in norm_num [ht]
#align path.homotopy.hcomp Path.Homotopy.hcomp

def reparam (p : Path x₀ x₁) (f : I → I) (hf : Continuous f) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
    Homotopy p (p.reparam f hf hf₀ hf₁) where
  toFun x := p ⟨σ x.1 * x.2 + x.1 * f x.2,
    show (σ x.1 : ℝ) • (x.2 : ℝ) + (x.1 : ℝ) • (f x.2 : ℝ) ∈ I from
      convex_Icc _ _ x.2.2 (f x.2).2 (by unit_interval) (by unit_interval) (by simp)⟩
  map_zero_left x := by norm_num
  map_one_left x := by norm_num
  prop' t x hx := by
    cases' hx with hx hx
    · rw [hx]
      simp [hf₀]
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      simp [hf₁]
  continuous_toFun := by
    -- Porting note: was `continuity` in auto-param
    refine continuous_const.path_eval ?_
    apply Continuous.subtype_mk
    apply Continuous.add <;> apply Continuous.mul
    · exact continuous_induced_dom.comp (unitInterval.continuous_symm.comp continuous_fst)
    · continuity
    · continuity
    · continuity
#align path.homotopy.reparam Path.Homotopy.reparam

def symm₂ {p q : Path x₀ x₁} (F : p.Homotopy q) : p.symm.Homotopy q.symm where
  toFun x := F ⟨x.1, σ x.2⟩
  map_zero_left := by simp [Path.symm]
  map_one_left := by simp [Path.symm]
  prop' t x hx := by
    cases' hx with hx hx
    · rw [hx]
      simp
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      simp
#align path.homotopy.symm₂ Path.Homotopy.symm₂

def map {p q : Path x₀ x₁} (F : p.Homotopy q) (f : C(X, Y)) :
    Homotopy (p.map f.continuous) (q.map f.continuous) where
  toFun := f ∘ F
  map_zero_left := by simp
  map_one_left := by simp
  prop' t x hx := by
    cases' hx with hx hx
    · simp [hx]
    · rw [Set.mem_singleton_iff] at hx
      simp [hx]
#align path.homotopy.map Path.Homotopy.map

def Homotopic (p₀ p₁ : Path x₀ x₁) : Prop :=
  Nonempty (p₀.Homotopy p₁)
#align path.homotopic Path.Homotopic

def setoid (x₀ x₁ : X) : Setoid (Path x₀ x₁) :=
  ⟨Homotopic, equivalence⟩
#align path.homotopic.setoid Path.Homotopic.setoid

def Quotient (x₀ x₁ : X) :=
  Quotient (Homotopic.setoid x₀ x₁)
#align path.homotopic.quotient Path.Homotopic.Quotient

def Quotient.comp (P₀ : Path.Homotopic.Quotient x₀ x₁) (P₁ : Path.Homotopic.Quotient x₁ x₂) :
    Path.Homotopic.Quotient x₀ x₂ :=
  Quotient.map₂ Path.trans (fun (_ : Path x₀ x₁) _ hp (_ : Path x₁ x₂) _ hq => hcomp hp hq) P₀ P₁
#align path.homotopic.quotient.comp Path.Homotopic.Quotient.comp

def Quotient.mapFn (P₀ : Path.Homotopic.Quotient x₀ x₁) (f : C(X, Y)) :
    Path.Homotopic.Quotient (f x₀) (f x₁) :=
  Quotient.map (fun q : Path x₀ x₁ => q.map f.continuous) (fun _ _ h => Path.Homotopic.map h f) P₀
#align path.homotopic.quotient.map_fn Path.Homotopic.Quotient.mapFn

def toHomotopyConst (p : Path x₀ x₁) :
    (ContinuousMap.const Y x₀).Homotopy (ContinuousMap.const Y x₁) where
  toContinuousMap := p.toContinuousMap.comp ContinuousMap.fst
  map_zero_left _ := p.source
  map_one_left _ := p.target

end Path

/-- Two constant continuous maps with nonempty domain are homotopic if and only if their values are
joined by a path in the codomain. -/
@[simp]
theorem ContinuousMap.homotopic_const_iff [Nonempty Y] :
    (ContinuousMap.const Y x₀).Homotopic (ContinuousMap.const Y x₁) ↔ Joined x₀ x₁ := by
  inhabit Y
  refine ⟨fun ⟨H⟩ ↦ ⟨⟨(H.toContinuousMap.comp .prodSwap).curry default, ?_, ?_⟩⟩,
    fun ⟨p⟩ ↦ ⟨p.toHomotopyConst⟩⟩ <;> simp

namespace ContinuousMap.Homotopy

/-- Given a homotopy `H : f ∼ g`, get the path traced by the point `x` as it moves from
`f x` to `g x`.
-/
def evalAt {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f g : C(X, Y)}
    (H : ContinuousMap.Homotopy f g) (x : X) : Path (f x) (g x) where
  toFun t := H (t, x)
  source' := H.apply_zero x
  target' := H.apply_one x
#align continuous_map.homotopy.eval_at ContinuousMap.Homotopy.evalAt