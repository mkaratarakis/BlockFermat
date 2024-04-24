def Simps.apply (F : Homotopy f₀ f₁) : I × X → Y :=
  F
#align continuous_map.homotopy.simps.apply ContinuousMap.Homotopy.Simps.apply

def curry (F : Homotopy f₀ f₁) : C(I, C(X, Y)) :=
  F.toContinuousMap.curry
#align continuous_map.homotopy.curry ContinuousMap.Homotopy.curry

def extend (F : Homotopy f₀ f₁) : C(ℝ, C(X, Y)) :=
  F.curry.IccExtend zero_le_one
#align continuous_map.homotopy.extend ContinuousMap.Homotopy.extend

def refl (f : C(X, Y)) : Homotopy f f where
  toFun x := f x.2
  map_zero_left _ := rfl
  map_one_left _ := rfl
#align continuous_map.homotopy.refl ContinuousMap.Homotopy.refl

def symm {f₀ f₁ : C(X, Y)} (F : Homotopy f₀ f₁) : Homotopy f₁ f₀ where
  toFun x := F (σ x.1, x.2)
  map_zero_left := by norm_num
  map_one_left := by norm_num
#align continuous_map.homotopy.symm ContinuousMap.Homotopy.symm

def trans {f₀ f₁ f₂ : C(X, Y)} (F : Homotopy f₀ f₁) (G : Homotopy f₁ f₂) : Homotopy f₀ f₂ where
  toFun x := if (x.1 : ℝ) ≤ 1 / 2 then F.extend (2 * x.1) x.2 else G.extend (2 * x.1 - 1) x.2
  continuous_toFun := by
    refine'
      continuous_if_le (continuous_induced_dom.comp continuous_fst) continuous_const
        (F.continuous.comp (by continuity)).continuousOn
        (G.continuous.comp (by continuity)).continuousOn _
    rintro x hx
    norm_num [hx]
  map_zero_left x := by set_option tactic.skipAssignedInstances false in norm_num
  map_one_left x := by set_option tactic.skipAssignedInstances false in norm_num
#align continuous_map.homotopy.trans ContinuousMap.Homotopy.trans

def cast {f₀ f₁ g₀ g₁ : C(X, Y)} (F : Homotopy f₀ f₁) (h₀ : f₀ = g₀) (h₁ : f₁ = g₁) :
    Homotopy g₀ g₁ where
  toFun := F
  map_zero_left := by simp [← h₀]
  map_one_left := by simp [← h₁]
#align continuous_map.homotopy.cast ContinuousMap.Homotopy.cast

def compContinuousMap {g₀ g₁ : C(Y, Z)} (G : Homotopy g₀ g₁) (f : C(X, Y)) :
    Homotopy (g₀.comp f) (g₁.comp f) where
  toContinuousMap := G.comp (.prodMap (.id _) f)
  map_zero_left _ := G.map_zero_left _
  map_one_left _ := G.map_one_left _

/-- If we have a `Homotopy f₀ f₁` and a `Homotopy g₀ g₁`, then we can compose them and get a
`Homotopy (g₀.comp f₀) (g₁.comp f₁)`.
-/
@[simps]
def hcomp {f₀ f₁ : C(X, Y)} {g₀ g₁ : C(Y, Z)} (F : Homotopy f₀ f₁) (G : Homotopy g₀ g₁) :
    Homotopy (g₀.comp f₀) (g₁.comp f₁) where
  toFun x := G (x.1, F x)
  map_zero_left := by simp
  map_one_left := by simp
#align continuous_map.homotopy.hcomp ContinuousMap.Homotopy.hcomp

def prodMk {f₀ f₁ : C(X, Y)} {g₀ g₁ : C(X, Z)} (F : Homotopy f₀ f₁) (G : Homotopy g₀ g₁) :
    Homotopy (f₀.prodMk g₀) (f₁.prodMk g₁) where
  toContinuousMap := F.prodMk G
  map_zero_left _ := Prod.ext (F.map_zero_left _) (G.map_zero_left _)
  map_one_left _ := Prod.ext (F.map_one_left _) (G.map_one_left _)

/-- Let `F` be a homotopy between `f₀ : C(X, Y)` and `f₁ : C(X, Y)`. Let `G` be a homotopy between
`g₀ : C(Z, Z')` and `g₁ : C(Z, Z')`. Then `F.prodMap G` is the homotopy between `f₀.prodMap g₀` and
`f₁.prodMap g₁` that sends `(t, x, z)` to `(F (t, x), G (t, z))`. -/
def prodMap {f₀ f₁ : C(X, Y)} {g₀ g₁ : C(Z, Z')} (F : Homotopy f₀ f₁) (G : Homotopy g₀ g₁) :
    Homotopy (f₀.prodMap g₀) (f₁.prodMap g₁) :=
  .prodMk (.hcomp (.refl .fst) F) (.hcomp (.refl .snd) G)

/-- Given a family of homotopies `F i` between `f₀ i : C(X, Y i)` and `f₁ i : C(X, Y i)`, returns a
homotopy between `ContinuousMap.pi f₀` and `ContinuousMap.pi f₁`. -/
protected def pi {Y : ι → Type*} [∀ i, TopologicalSpace (Y i)] {f₀ f₁ : ∀ i, C(X, Y i)}
    (F : ∀ i, Homotopy (f₀ i) (f₁ i)) :
    Homotopy (.pi f₀) (.pi f₁) where
  toContinuousMap := .pi fun i ↦ F i
  map_zero_left x := funext fun i ↦ (F i).map_zero_left x
  map_one_left x := funext fun i ↦ (F i).map_one_left x

/-- Given a family of homotopies `F i` between `f₀ i : C(X i, Y i)` and `f₁ i : C(X i, Y i)`,
returns a homotopy between `ContinuousMap.piMap f₀` and `ContinuousMap.piMap f₁`. -/
protected def piMap {X Y : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)]
    {f₀ f₁ : ∀ i, C(X i, Y i)} (F : ∀ i, Homotopy (f₀ i) (f₁ i)) :
    Homotopy (.piMap f₀) (.piMap f₁) :=
  .pi fun i ↦ .hcomp (.refl <| .eval i) (F i)

end Homotopy

/-- Given continuous maps `f₀` and `f₁`, we say `f₀` and `f₁` are homotopic if there exists a
`Homotopy f₀ f₁`.
-/
def Homotopic (f₀ f₁ : C(X, Y)) : Prop :=
  Nonempty (Homotopy f₀ f₁)
#align continuous_map.homotopic ContinuousMap.Homotopic

def Simps.apply (F : HomotopyWith f₀ f₁ P) : I × X → Y := F
#align continuous_map.homotopy_with.simps.apply ContinuousMap.HomotopyWith.Simps.apply

def refl (f : C(X, Y)) (hf : P f) : HomotopyWith f f P where
  toHomotopy := Homotopy.refl f
  prop' := fun _ => hf
#align continuous_map.homotopy_with.refl ContinuousMap.HomotopyWith.refl

def symm {f₀ f₁ : C(X, Y)} (F : HomotopyWith f₀ f₁ P) : HomotopyWith f₁ f₀ P where
  toHomotopy := F.toHomotopy.symm
  prop' := fun t => F.prop (σ t)
#align continuous_map.homotopy_with.symm ContinuousMap.HomotopyWith.symm

def trans {f₀ f₁ f₂ : C(X, Y)} (F : HomotopyWith f₀ f₁ P) (G : HomotopyWith f₁ f₂ P) :
    HomotopyWith f₀ f₂ P :=
  { F.toHomotopy.trans G.toHomotopy with
    prop' := fun t => by
      simp only [Homotopy.trans]
      change P ⟨fun _ => ite ((t : ℝ) ≤ _) _ _, _⟩
      split_ifs
      · exact F.extendProp _
      · exact G.extendProp _ }
#align continuous_map.homotopy_with.trans ContinuousMap.HomotopyWith.trans

def cast {f₀ f₁ g₀ g₁ : C(X, Y)} (F : HomotopyWith f₀ f₁ P) (h₀ : f₀ = g₀) (h₁ : f₁ = g₁) :
    HomotopyWith g₀ g₁ P where
  toHomotopy := F.toHomotopy.cast h₀ h₁
  prop' := F.prop
#align continuous_map.homotopy_with.cast ContinuousMap.HomotopyWith.cast

def HomotopicWith (f₀ f₁ : C(X, Y)) (P : C(X, Y) → Prop) : Prop :=
  Nonempty (HomotopyWith f₀ f₁ P)
#align continuous_map.homotopic_with ContinuousMap.HomotopicWith

def refl (f : C(X, Y)) (S : Set X) : HomotopyRel f f S :=
  HomotopyWith.refl f fun _ _ ↦ rfl
#align continuous_map.homotopy_rel.refl ContinuousMap.HomotopyRel.refl

def symm (F : HomotopyRel f₀ f₁ S) : HomotopyRel f₁ f₀ S where
  toHomotopy := F.toHomotopy.symm
  prop' := fun _ _ hx ↦ F.eq_snd _ hx
#align continuous_map.homotopy_rel.symm ContinuousMap.HomotopyRel.symm

def trans (F : HomotopyRel f₀ f₁ S) (G : HomotopyRel f₁ f₂ S) : HomotopyRel f₀ f₂ S where
  toHomotopy := F.toHomotopy.trans G.toHomotopy
  prop' t x hx := by
    simp only [Homotopy.trans]
    split_ifs
    · simp [HomotopyWith.extendProp F (2 * t) x hx, F.fst_eq_snd hx, G.fst_eq_snd hx]
    · simp [HomotopyWith.extendProp G (2 * t - 1) x hx, F.fst_eq_snd hx, G.fst_eq_snd hx]
#align continuous_map.homotopy_rel.trans ContinuousMap.HomotopyRel.trans

def cast {f₀ f₁ g₀ g₁ : C(X, Y)} (F : HomotopyRel f₀ f₁ S) (h₀ : f₀ = g₀) (h₁ : f₁ = g₁) :
    HomotopyRel g₀ g₁ S where
  toHomotopy := Homotopy.cast F.toHomotopy h₀ h₁
  prop' t x hx := by simpa only [← h₀, ← h₁] using F.prop t x hx
#align continuous_map.homotopy_rel.cast ContinuousMap.HomotopyRel.cast

def compContinuousMap {f₀ f₁ : C(X, Y)} (F : f₀.HomotopyRel f₁ S) (g : C(Y, Z)) :
    (g.comp f₀).HomotopyRel (g.comp f₁) S where
  toHomotopy := F.hcomp (ContinuousMap.Homotopy.refl g)
  prop' t x hx := congr_arg g (F.prop t x hx)

end HomotopyRel

/-- Given continuous maps `f₀` and `f₁`, we say `f₀` and `f₁` are homotopic relative to a set `S` if
there exists a `HomotopyRel f₀ f₁ S`.
-/
def HomotopicRel (f₀ f₁ : C(X, Y)) (S : Set X) : Prop :=
  Nonempty (HomotopyRel f₀ f₁ S)
#align continuous_map.homotopic_rel ContinuousMap.HomotopicRel

structure Homotopy (f₀ f₁ : C(X, Y)) extends C(I × X, Y) where
  /-- value of the homotopy at 0 -/
  map_zero_left : ∀ x, toFun (0, x) = f₀ x
  /-- value of the homotopy at 1 -/
  map_one_left : ∀ x, toFun (1, x) = f₁ x
#align continuous_map.homotopy ContinuousMap.Homotopy

structure HomotopyWith (f₀ f₁ : C(X, Y)) (P : C(X, Y) → Prop) extends Homotopy f₀ f₁ where
  -- Porting note (#11215): TODO: use `toHomotopy.curry t`