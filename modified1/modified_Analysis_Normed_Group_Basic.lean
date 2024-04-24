def NormedGroup.ofSeparation [SeminormedGroup E] (h : ∀ x : E, ‖x‖ = 0 → x = 1) :
    NormedGroup E where
  dist_eq := ‹SeminormedGroup E›.dist_eq
  toMetricSpace :=
    { eq_of_dist_eq_zero := fun hxy =>
        div_eq_one.1 <| h _ <| by exact (‹SeminormedGroup E›.dist_eq _ _).symm.trans hxy }
      -- Porting note: the `rwa` no longer worked, but it was easy enough to provide the term.
      -- however, notice that if you make `x` and `y` accessible, then the following does work:
      -- `have := ‹SeminormedGroup E›.dist_eq x y; rwa [← this]`, so I'm not sure why the `rwa`
      -- was broken.
#align normed_group.of_separation NormedGroup.ofSeparation

def NormedCommGroup.ofSeparation [SeminormedCommGroup E] (h : ∀ x : E, ‖x‖ = 0 → x = 1) :
    NormedCommGroup E :=
  { ‹SeminormedCommGroup E›, NormedGroup.ofSeparation h with }
#align normed_comm_group.of_separation NormedCommGroup.ofSeparation

def SeminormedGroup.ofMulDist [Norm E] [Group E] [PseudoMetricSpace E]
    (h₁ : ∀ x : E, ‖x‖ = dist x 1) (h₂ : ∀ x y z : E, dist x y ≤ dist (x * z) (y * z)) :
    SeminormedGroup E where
  dist_eq x y := by
    rw [h₁]; apply le_antisymm
    · simpa only [div_eq_mul_inv, ← mul_right_inv y] using h₂ _ _ _
    · simpa only [div_mul_cancel, one_mul] using h₂ (x / y) 1 y
#align seminormed_group.of_mul_dist SeminormedGroup.ofMulDist

def SeminormedGroup.ofMulDist' [Norm E] [Group E] [PseudoMetricSpace E]
    (h₁ : ∀ x : E, ‖x‖ = dist x 1) (h₂ : ∀ x y z : E, dist (x * z) (y * z) ≤ dist x y) :
    SeminormedGroup E where
  dist_eq x y := by
    rw [h₁]; apply le_antisymm
    · simpa only [div_mul_cancel, one_mul] using h₂ (x / y) 1 y
    · simpa only [div_eq_mul_inv, ← mul_right_inv y] using h₂ _ _ _
#align seminormed_group.of_mul_dist' SeminormedGroup.ofMulDist'

def SeminormedCommGroup.ofMulDist [Norm E] [CommGroup E] [PseudoMetricSpace E]
    (h₁ : ∀ x : E, ‖x‖ = dist x 1) (h₂ : ∀ x y z : E, dist x y ≤ dist (x * z) (y * z)) :
    SeminormedCommGroup E :=
  { SeminormedGroup.ofMulDist h₁ h₂ with
    mul_comm := mul_comm }
#align seminormed_comm_group.of_mul_dist SeminormedCommGroup.ofMulDist

def SeminormedCommGroup.ofMulDist' [Norm E] [CommGroup E] [PseudoMetricSpace E]
    (h₁ : ∀ x : E, ‖x‖ = dist x 1) (h₂ : ∀ x y z : E, dist (x * z) (y * z) ≤ dist x y) :
    SeminormedCommGroup E :=
  { SeminormedGroup.ofMulDist' h₁ h₂ with
    mul_comm := mul_comm }
#align seminormed_comm_group.of_mul_dist' SeminormedCommGroup.ofMulDist'

def NormedGroup.ofMulDist [Norm E] [Group E] [MetricSpace E] (h₁ : ∀ x : E, ‖x‖ = dist x 1)
    (h₂ : ∀ x y z : E, dist x y ≤ dist (x * z) (y * z)) : NormedGroup E :=
  { SeminormedGroup.ofMulDist h₁ h₂ with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }
#align normed_group.of_mul_dist NormedGroup.ofMulDist

def NormedGroup.ofMulDist' [Norm E] [Group E] [MetricSpace E] (h₁ : ∀ x : E, ‖x‖ = dist x 1)
    (h₂ : ∀ x y z : E, dist (x * z) (y * z) ≤ dist x y) : NormedGroup E :=
  { SeminormedGroup.ofMulDist' h₁ h₂ with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }
#align normed_group.of_mul_dist' NormedGroup.ofMulDist'

def NormedCommGroup.ofMulDist [Norm E] [CommGroup E] [MetricSpace E]
    (h₁ : ∀ x : E, ‖x‖ = dist x 1) (h₂ : ∀ x y z : E, dist x y ≤ dist (x * z) (y * z)) :
    NormedCommGroup E :=
  { NormedGroup.ofMulDist h₁ h₂ with
    mul_comm := mul_comm }
#align normed_comm_group.of_mul_dist NormedCommGroup.ofMulDist

def NormedCommGroup.ofMulDist' [Norm E] [CommGroup E] [MetricSpace E]
    (h₁ : ∀ x : E, ‖x‖ = dist x 1) (h₂ : ∀ x y z : E, dist (x * z) (y * z) ≤ dist x y) :
    NormedCommGroup E :=
  { NormedGroup.ofMulDist' h₁ h₂ with
    mul_comm := mul_comm }
#align normed_comm_group.of_mul_dist' NormedCommGroup.ofMulDist'

def GroupSeminorm.toSeminormedGroup [Group E] (f : GroupSeminorm E) : SeminormedGroup E where
  dist x y := f (x / y)
  norm := f
  dist_eq x y := rfl
  dist_self x := by simp only [div_self', map_one_eq_zero]
  dist_triangle := le_map_div_add_map_div f
  dist_comm := map_div_rev f
  edist_dist x y := by exact ENNReal.coe_nnreal_eq _
  -- Porting note: how did `mathlib3` solve this automatically?
#align group_seminorm.to_seminormed_group GroupSeminorm.toSeminormedGroup

def GroupSeminorm.toSeminormedCommGroup [CommGroup E] (f : GroupSeminorm E) :
    SeminormedCommGroup E :=
  { f.toSeminormedGroup with
    mul_comm := mul_comm }
#align group_seminorm.to_seminormed_comm_group GroupSeminorm.toSeminormedCommGroup

def GroupNorm.toNormedGroup [Group E] (f : GroupNorm E) : NormedGroup E :=
  { f.toGroupSeminorm.toSeminormedGroup with
    eq_of_dist_eq_zero := fun h => div_eq_one.1 <| eq_one_of_map_eq_zero f h }
#align group_norm.to_normed_group GroupNorm.toNormedGroup

def GroupNorm.toNormedCommGroup [CommGroup E] (f : GroupNorm E) : NormedCommGroup E :=
  { f.toNormedGroup with
    mul_comm := mul_comm }
#align group_norm.to_normed_comm_group GroupNorm.toNormedCommGroup

def evalMulNorm : PositivityExt where eval {u α} _zα _pα e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@Norm.norm $β $instDist $a) =>
    let _inst ← synthInstanceQ q(SeminormedGroup $β)
    assertInstancesCommute
    pure (.nonnegative q(norm_nonneg' $a))
  | _, _, _ => throwError "not ‖ · ‖"

/-- Extension for the `positivity` tactic: additive norms are nonnegative, via `norm_nonneg`. -/
@[positivity Norm.norm _]
def evalAddNorm : PositivityExt where eval {u α} _zα _pα e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@Norm.norm $β $instDist $a) =>
    let _inst ← synthInstanceQ q(SeminormedAddGroup $β)
    assertInstancesCommute
    pure (.nonnegative q(norm_nonneg $a))
  | _, _, _ => throwError "not ‖ · ‖"

end Mathlib.Meta.Positivity

@[to_additive (attr := simp) norm_zero]
theorem norm_one' : ‖(1 : E)‖ = 0 := by rw [← dist_one_right, dist_self]
#align norm_one' norm_one'

def normGroupSeminorm : GroupSeminorm E :=
  ⟨norm, norm_one', norm_mul_le', norm_inv'⟩
#align norm_group_seminorm normGroupSeminorm

def SeminormedGroup.induced [Group E] [SeminormedGroup F] [MonoidHomClass 𝓕 E F] (f : 𝓕) :
    SeminormedGroup E :=
  { PseudoMetricSpace.induced f toPseudoMetricSpace with
    -- Porting note: needed to add the instance explicitly, and `‹PseudoMetricSpace F›` failed
    norm := fun x => ‖f x‖
    dist_eq := fun x y => by simp only [map_div, ← dist_eq_norm_div]; rfl }
#align seminormed_group.induced SeminormedGroup.induced

def SeminormedCommGroup.induced
    [CommGroup E] [SeminormedGroup F] [MonoidHomClass 𝓕 E F] (f : 𝓕) :
    SeminormedCommGroup E :=
  { SeminormedGroup.induced E F f with
    mul_comm := mul_comm }
#align seminormed_comm_group.induced SeminormedCommGroup.induced

def NormedGroup.induced
    [Group E] [NormedGroup F] [MonoidHomClass 𝓕 E F] (f : 𝓕) (h : Injective f) :
    NormedGroup E :=
  { SeminormedGroup.induced E F f, MetricSpace.induced f h _ with }
#align normed_group.induced NormedGroup.induced

def NormedCommGroup.induced [CommGroup E] [NormedGroup F] [MonoidHomClass 𝓕 E F] (f : 𝓕)
    (h : Injective f) : NormedCommGroup E :=
  { SeminormedGroup.induced E F f, MetricSpace.induced f h _ with
    mul_comm := mul_comm }
#align normed_comm_group.induced NormedCommGroup.induced

def normGroupNorm : GroupNorm E :=
  { normGroupSeminorm _ with eq_one_of_map_eq_zero' := fun _ => norm_eq_zero''.1 }
#align norm_group_norm normGroupNorm

def (x : ULift E) : ‖x‖ = ‖x.down‖ :=
  rfl
#align ulift.norm_def ULift.norm_def

def (x : ULift E) : ‖x‖₊ = ‖x.down‖₊ :=
  rfl
#align ulift.nnnorm_def ULift.nnnorm_def

def (x : E × F) : ‖x‖ = max ‖x.1‖ ‖x.2‖ :=
  rfl
#align prod.norm_def Prod.norm_def

def (x : E × F) : ‖x‖₊ = max ‖x.1‖₊ ‖x.2‖₊ :=
  rfl
#align prod.nnorm_def Prod.nnorm_def

def Pi.norm_def

@[to_additive Pi.nnnorm_def]
theorem Pi.nnnorm_def' : ‖f‖₊ = Finset.univ.sup fun b => ‖f b‖₊ :=
  Subtype.eta _ _
#align pi.nnnorm_def' Pi.nnnorm_def'

def Pi.nnnorm_def

/-- The seminorm of an element in a product space is `≤ r` if and only if the norm of each
component is. -/
@[to_additive pi_norm_le_iff_of_nonneg "The seminorm of an element in a product space is `≤ r` if
and only if the norm of each component is."]
theorem pi_norm_le_iff_of_nonneg' (hr : 0 ≤ r) : ‖x‖ ≤ r ↔ ∀ i, ‖x i‖ ≤ r := by
  simp only [← dist_one_right, dist_pi_le_iff hr, Pi.one_apply]
#align pi_norm_le_iff_of_nonneg' pi_norm_le_iff_of_nonneg'

structure from the seminorm properties. Note that in most cases this instance
creates bad definitional equalities (e.g., it does not take into account a possibly existing
`UniformSpace` instance on `E`). -/
@[to_additive (attr := reducible)
  "Construct a seminormed group from a seminorm, i.e., registering the pseudodistance
and the pseudometric space structure from the seminorm properties. Note that in most cases this
instance creates bad definitional equalities (e.g., it does not take into account a possibly
existing `UniformSpace` instance on `E`)."]
def GroupSeminorm.toSeminormedGroup [Group E] (f : GroupSeminorm E) : SeminormedGroup E where
  dist x y := f (x / y)
  norm := f
  dist_eq x y := rfl
  dist_self x := by simp only [div_self', map_one_eq_zero]
  dist_triangle := le_map_div_add_map_div f
  dist_comm := map_div_rev f
  edist_dist x y := by exact ENNReal.coe_nnreal_eq _
  -- Porting note: how did `mathlib3` solve this automatically?
#align group_seminorm.to_seminormed_group GroupSeminorm.toSeminormedGroup

structure from the seminorm properties. Note that in most cases this instance
creates bad definitional equalities (e.g., it does not take into account a possibly existing
`UniformSpace` instance on `E`). -/
@[to_additive (attr := reducible)
  "Construct a seminormed group from a seminorm, i.e., registering the pseudodistance
and the pseudometric space structure from the seminorm properties. Note that in most cases this
instance creates bad definitional equalities (e.g., it does not take into account a possibly
existing `UniformSpace` instance on `E`)."]
def GroupSeminorm.toSeminormedCommGroup [CommGroup E] (f : GroupSeminorm E) :
    SeminormedCommGroup E :=
  { f.toSeminormedGroup with
    mul_comm := mul_comm }
#align group_seminorm.to_seminormed_comm_group GroupSeminorm.toSeminormedCommGroup

structure from the norm properties. Note that in most cases this instance creates bad definitional
equalities (e.g., it does not take into account a possibly existing `UniformSpace` instance on
`E`). -/
@[to_additive (attr := reducible)
  "Construct a normed group from a norm, i.e., registering the distance and the metric
space structure from the norm properties. Note that in most cases this instance creates bad
definitional equalities (e.g., it does not take into account a possibly existing `UniformSpace`
instance on `E`)."]
def GroupNorm.toNormedGroup [Group E] (f : GroupNorm E) : NormedGroup E :=
  { f.toGroupSeminorm.toSeminormedGroup with
    eq_of_dist_eq_zero := fun h => div_eq_one.1 <| eq_one_of_map_eq_zero f h }
#align group_norm.to_normed_group GroupNorm.toNormedGroup

structure from the norm properties. Note that in most cases this instance creates bad definitional
equalities (e.g., it does not take into account a possibly existing `UniformSpace` instance on
`E`). -/
@[to_additive (attr := reducible)
  "Construct a normed group from a norm, i.e., registering the distance and the metric
space structure from the norm properties. Note that in most cases this instance creates bad
definitional equalities (e.g., it does not take into account a possibly existing `UniformSpace`
instance on `E`)."]
def GroupNorm.toNormedCommGroup [CommGroup E] (f : GroupNorm E) : NormedCommGroup E :=
  { f.toNormedGroup with
    mul_comm := mul_comm }
#align group_norm.to_normed_comm_group GroupNorm.toNormedCommGroup

structure on the domain. -/
@[to_additive (attr := reducible) "A group homomorphism from an `AddGroup` to a
`SeminormedAddGroup` induces a `SeminormedAddGroup` structure on the domain."]
def SeminormedGroup.induced [Group E] [SeminormedGroup F] [MonoidHomClass 𝓕 E F] (f : 𝓕) :
    SeminormedGroup E :=
  { PseudoMetricSpace.induced f toPseudoMetricSpace with
    -- Porting note: needed to add the instance explicitly, and `‹PseudoMetricSpace F›` failed
    norm := fun x => ‖f x‖
    dist_eq := fun x y => by simp only [map_div, ← dist_eq_norm_div]; rfl }
#align seminormed_group.induced SeminormedGroup.induced

structure on the domain. -/
@[to_additive (attr := reducible) "A group homomorphism from an `AddCommGroup` to a
`SeminormedAddGroup` induces a `SeminormedAddCommGroup` structure on the domain."]
def SeminormedCommGroup.induced
    [CommGroup E] [SeminormedGroup F] [MonoidHomClass 𝓕 E F] (f : 𝓕) :
    SeminormedCommGroup E :=
  { SeminormedGroup.induced E F f with
    mul_comm := mul_comm }
#align seminormed_comm_group.induced SeminormedCommGroup.induced

structure on the domain. -/
@[to_additive (attr := reducible) "An injective group homomorphism from an `AddGroup` to a
`NormedAddGroup` induces a `NormedAddGroup` structure on the domain."]
def NormedGroup.induced
    [Group E] [NormedGroup F] [MonoidHomClass 𝓕 E F] (f : 𝓕) (h : Injective f) :
    NormedGroup E :=
  { SeminormedGroup.induced E F f, MetricSpace.induced f h _ with }
#align normed_group.induced NormedGroup.induced

structure on the domain. -/
@[to_additive (attr := reducible) "An injective group homomorphism from a `CommGroup` to a
`NormedCommGroup` induces a `NormedCommGroup` structure on the domain."]
def NormedCommGroup.induced [CommGroup E] [NormedGroup F] [MonoidHomClass 𝓕 E F] (f : 𝓕)
    (h : Injective f) : NormedCommGroup E :=
  { SeminormedGroup.induced E F f, MetricSpace.induced f h _ with
    mul_comm := mul_comm }
#align normed_comm_group.induced NormedCommGroup.induced