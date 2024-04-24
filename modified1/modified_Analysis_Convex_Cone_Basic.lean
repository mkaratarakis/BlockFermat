def map (f : E →ₗ[𝕜] F) (S : ConvexCone 𝕜 E) : ConvexCone 𝕜 F where
  carrier := f '' S
  smul_mem' := fun c hc _ ⟨x, hx, hy⟩ => hy ▸ f.map_smul c x ▸ mem_image_of_mem f (S.smul_mem hc hx)
  add_mem' := fun _ ⟨x₁, hx₁, hy₁⟩ _ ⟨x₂, hx₂, hy₂⟩ =>
    hy₁ ▸ hy₂ ▸ f.map_add x₁ x₂ ▸ mem_image_of_mem f (S.add_mem hx₁ hx₂)
#align convex_cone.map ConvexCone.map

def comap (f : E →ₗ[𝕜] F) (S : ConvexCone 𝕜 F) : ConvexCone 𝕜 E where
  carrier := f ⁻¹' S
  smul_mem' c hc x hx := by
    rw [mem_preimage, f.map_smul c]
    exact S.smul_mem hc hx
  add_mem' x hx y hy := by
    rw [mem_preimage, f.map_add]
    exact S.add_mem hx hy
#align convex_cone.comap ConvexCone.comap

def Pointed (S : ConvexCone 𝕜 E) : Prop :=
  (0 : E) ∈ S
#align convex_cone.pointed ConvexCone.Pointed

def Blunt (S : ConvexCone 𝕜 E) : Prop :=
  (0 : E) ∉ S
#align convex_cone.blunt ConvexCone.Blunt

def Flat : Prop :=
  ∃ x ∈ S, x ≠ (0 : E) ∧ -x ∈ S
#align convex_cone.flat ConvexCone.Flat

def Salient : Prop :=
  ∀ x ∈ S, x ≠ (0 : E) → -x ∉ S
#align convex_cone.salient ConvexCone.Salient

def toPreorder (h₁ : S.Pointed) : Preorder E where
  le x y := y - x ∈ S
  le_refl x := by change x - x ∈ S; rw [sub_self x]; exact h₁
  le_trans x y z xy zy := by simpa using add_mem S zy xy
#align convex_cone.to_preorder ConvexCone.toPreorder

def toPartialOrder (h₁ : S.Pointed) (h₂ : S.Salient) : PartialOrder E :=
  { toPreorder S h₁ with
    le_antisymm := by
      intro a b ab ba
      by_contra h
      have h' : b - a ≠ 0 := fun h'' => h (eq_of_sub_eq_zero h'').symm
      have H := h₂ (b - a) ab h'
      rw [neg_sub b a] at H
      exact H ba }
#align convex_cone.to_partial_order ConvexCone.toPartialOrder

def toOrderedAddCommGroup (h₁ : S.Pointed) (h₂ : S.Salient) : OrderedAddCommGroup E :=
  { toPartialOrder S h₁ h₂, show AddCommGroup E by infer_instance with
    add_le_add_left := by
      intro a b hab c
      change c + b - (c + a) ∈ S
      rw [add_sub_add_left_eq_sub]
      exact hab }
#align convex_cone.to_ordered_add_comm_group ConvexCone.toOrderedAddCommGroup

def toConvexCone (S : Submodule 𝕜 E) : ConvexCone 𝕜 E where
  carrier := S
  smul_mem' c _ _ hx := S.smul_mem c hx
  add_mem' _ hx _ hy := S.add_mem hx hy
#align submodule.to_convex_cone Submodule.toConvexCone

def positive : ConvexCone 𝕜 E where
  carrier := Set.Ici 0
  smul_mem' _ hc _ (hx : _ ≤ _) := smul_nonneg hc.le hx
  add_mem' _ (hx : _ ≤ _) _ (hy : _ ≤ _) := add_nonneg hx hy
#align convex_cone.positive ConvexCone.positive

def strictlyPositive : ConvexCone 𝕜 E where
  carrier := Set.Ioi 0
  smul_mem' _ hc _ (hx : _ < _) := smul_pos hc hx
  add_mem' _ hx _ hy := add_pos hx hy
#align convex_cone.strictly_positive ConvexCone.strictlyPositive

def toCone (s : Set E) (hs : Convex 𝕜 s) : ConvexCone 𝕜 E := by
  apply ConvexCone.mk (⋃ (c : 𝕜) (_ : 0 < c), c • s) <;> simp only [mem_iUnion, mem_smul_set]
  · rintro c c_pos _ ⟨c', c'_pos, x, hx, rfl⟩
    exact ⟨c * c', mul_pos c_pos c'_pos, x, hx, (smul_smul _ _ _).symm⟩
  · rintro _ ⟨cx, cx_pos, x, hx, rfl⟩ _ ⟨cy, cy_pos, y, hy, rfl⟩
    have : 0 < cx + cy := add_pos cx_pos cy_pos
    refine' ⟨_, this, _, convex_iff_div.1 hs hx hy cx_pos.le cy_pos.le this, _⟩
    simp only [smul_add, smul_smul, mul_div_assoc', mul_div_cancel_left₀ _ this.ne']
#align convex.to_cone Convex.toCone

structure ConvexCone [AddCommMonoid E] [SMul 𝕜 E] where
  carrier : Set E
  smul_mem' : ∀ ⦃c : 𝕜⦄, 0 < c → ∀ ⦃x : E⦄, x ∈ carrier → c • x ∈ carrier
  add_mem' : ∀ ⦃x⦄ (_ : x ∈ carrier) ⦃y⦄ (_ : y ∈ carrier), x + y ∈ carrier
#align convex_cone ConvexCone