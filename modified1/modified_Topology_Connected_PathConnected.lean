def simps.apply : I → X :=
  γ
#align path.simps.apply Path.simps.apply

def refl (x : X) : Path x x where
  toFun _t := x
  continuous_toFun := continuous_const
  source' := rfl
  target' := rfl
#align path.refl Path.refl

def symm (γ : Path x y) : Path y x where
  toFun := γ ∘ σ
  continuous_toFun := by continuity
  source' := by simpa [-Path.target] using γ.target
  target' := by simpa [-Path.source] using γ.source
#align path.symm Path.symm

def extend : ℝ → X :=
  IccExtend zero_le_one γ
#align path.extend Path.extend

def ofLine {f : ℝ → X} (hf : ContinuousOn f I) (h₀ : f 0 = x) (h₁ : f 1 = y) : Path x y where
  toFun := f ∘ ((↑) : unitInterval → ℝ)
  continuous_toFun := hf.comp_continuous continuous_subtype_val Subtype.prop
  source' := h₀
  target' := h₁
#align path.of_line Path.ofLine

def

set_option tactic.skipAssignedInstances false in
/-- Concatenation of two paths from `x` to `y` and from `y` to `z`, putting the first
path on `[0, 1/2]` and the second one on `[1/2, 1]`. -/
@[trans]
def trans (γ : Path x y) (γ' : Path y z) : Path x z where
  toFun := (fun t : ℝ => if t ≤ 1 / 2 then γ.extend (2 * t) else γ'.extend (2 * t - 1)) ∘ (↑)
  continuous_toFun := by
    refine'
      (Continuous.if_le _ _ continuous_id continuous_const (by norm_num)).comp
        continuous_subtype_val <;>
    continuity
  source' := by norm_num
  target' := by norm_num
#align path.trans Path.trans

def map' (γ : Path x y) {f : X → Y} (h : ContinuousOn f (range γ)) : Path (f x) (f y) where
  toFun := f ∘ γ
  continuous_toFun := h.comp_continuous γ.continuous (fun x ↦ mem_range_self x)
  source' := by simp
  target' := by simp

/-- Image of a path from `x` to `y` by a continuous map -/
def map (γ : Path x y) {f : X → Y} (h : Continuous f) :
    Path (f x) (f y) := γ.map' h.continuousOn
#align path.map Path.map

def cast (γ : Path x y) {x' y'} (hx : x' = x) (hy : y' = y) : Path x' y' where
  toFun := γ
  continuous_toFun := γ.continuous
  source' := by simp [hx]
  target' := by simp [hy]
#align path.cast Path.cast

def prod (γ₁ : Path a₁ a₂) (γ₂ : Path b₁ b₂) : Path (a₁, b₁) (a₂, b₂) where
  toContinuousMap := ContinuousMap.prodMk γ₁.toContinuousMap γ₂.toContinuousMap
  source' := by simp
  target' := by simp
#align path.prod Path.prod

def pi (γ : ∀ i, Path (as i) (bs i)) : Path as bs where
  toContinuousMap := ContinuousMap.pi fun i => (γ i).toContinuousMap
  source' := by simp
  target' := by simp
#align path.pi Path.pi

def mul [Mul X] [ContinuousMul X] {a₁ b₁ a₂ b₂ : X} (γ₁ : Path a₁ b₁) (γ₂ : Path a₂ b₂) :
    Path (a₁ * a₂) (b₁ * b₂) :=
  (γ₁.prod γ₂).map continuous_mul
#align path.mul Path.mul

def truncate {X : Type*} [TopologicalSpace X] {a b : X} (γ : Path a b) (t₀ t₁ : ℝ) :
    Path (γ.extend <| min t₀ t₁) (γ.extend t₁) where
  toFun s := γ.extend (min (max s t₀) t₁)
  continuous_toFun :=
    γ.continuous_extend.comp ((continuous_subtype_val.max continuous_const).min continuous_const)
  source' := by
    simp only [min_def, max_def']
    norm_cast
    split_ifs with h₁ h₂ h₃ h₄
    · simp [γ.extend_of_le_zero h₁]
    · congr
      linarith
    · have h₄ : t₁ ≤ 0 := le_of_lt (by simpa using h₂)
      simp [γ.extend_of_le_zero h₄, γ.extend_of_le_zero h₁]
    all_goals rfl
  target' := by
    simp only [min_def, max_def']
    norm_cast
    split_ifs with h₁ h₂ h₃
    · simp [γ.extend_of_one_le h₂]
    · rfl
    · have h₄ : 1 ≤ t₀ := le_of_lt (by simpa using h₁)
      simp [γ.extend_of_one_le h₄, γ.extend_of_one_le (h₄.trans h₃)]
    · rfl
#align path.truncate Path.truncate

def truncateOfLE {X : Type*} [TopologicalSpace X] {a b : X} (γ : Path a b) {t₀ t₁ : ℝ}
    (h : t₀ ≤ t₁) : Path (γ.extend t₀) (γ.extend t₁) :=
  (γ.truncate t₀ t₁).cast (by rw [min_eq_left h]) rfl
#align path.truncate_of_le Path.truncateOfLE

def reparam (γ : Path x y) (f : I → I) (hfcont : Continuous f) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
    Path x y where
  toFun := γ ∘ f
  continuous_toFun := by continuity
  source' := by simp [hf₀]
  target' := by simp [hf₁]
#align path.reparam Path.reparam

def Joined (x y : X) : Prop :=
  Nonempty (Path x y)
#align joined Joined

def Joined.somePath (h : Joined x y) : Path x y :=
  Nonempty.some h
#align joined.some_path Joined.somePath

def pathSetoid : Setoid X where
  r := Joined
  iseqv := Equivalence.mk Joined.refl Joined.symm Joined.trans
#align path_setoid pathSetoid

def ZerothHomotopy :=
  Quotient (pathSetoid X)
#align zeroth_homotopy ZerothHomotopy

def JoinedIn (F : Set X) (x y : X) : Prop :=
  ∃ γ : Path x y, ∀ t, γ t ∈ F
#align joined_in JoinedIn

def JoinedIn.somePath (h : JoinedIn F x y) : Path x y :=
  Classical.choose h
#align joined_in.some_path JoinedIn.somePath

def pathComponent (x : X) :=
  { y | Joined x y }
#align path_component pathComponent

def pathComponentIn (x : X) (F : Set X) :=
  { y | JoinedIn F x y }
#align path_component_in pathComponentIn

def IsPathConnected (F : Set X) : Prop :=
  ∃ x ∈ F, ∀ {y}, y ∈ F → JoinedIn F x y
#align is_path_connected IsPathConnected

def somePath (x y : X) : Path x y :=
  Nonempty.some (joined x y)
#align path_connected_space.some_path PathConnectedSpace.somePath

structure Path (x y : X) extends C(I, X) where
  /-- The start point of a `Path`. -/
  source' : toFun 0 = x
  /-- The end point of a `Path`. -/
  target' : toFun 1 = y
#align path Path