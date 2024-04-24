def reindex (e : ι ≃ ι') : AffineBasis ι' k P :=
  ⟨b ∘ e.symm, b.ind.comp_embedding e.symm.toEmbedding, by
    rw [e.symm.surjective.range_comp]
    exact b.3⟩
#align affine_basis.reindex AffineBasis.reindex

def basisOf (i : ι) : Basis { j : ι // j ≠ i } k V :=
  Basis.mk ((affineIndependent_iff_linearIndependent_vsub k b i).mp b.ind)
    (by
      suffices
        Submodule.span k (range fun j : { x // x ≠ i } => b ↑j -ᵥ b i) = vectorSpan k (range b) by
        rw [this, ← direction_affineSpan, b.tot, AffineSubspace.direction_top]
      conv_rhs => rw [← image_univ]
      rw [vectorSpan_image_eq_span_vsub_set_right_ne k b (mem_univ i)]
      congr
      ext v
      simp)
#align affine_basis.basis_of AffineBasis.basisOf

def coord (i : ι) : P →ᵃ[k] k where
  toFun q := 1 - (b.basisOf i).sumCoords (q -ᵥ b i)
  linear := -(b.basisOf i).sumCoords
  map_vadd' q v := by
    dsimp only
    rw [vadd_vsub_assoc, LinearMap.map_add, vadd_eq_add, LinearMap.neg_apply,
      sub_add_eq_sub_sub_swap, add_comm, sub_eq_add_neg]
#align affine_basis.coord AffineBasis.coord

def coords : P →ᵃ[k] ι → k where
  toFun q i := b.coord i q
  linear :=
    { toFun := fun v i => -(b.basisOf i).sumCoords v
      map_add' := fun v w => by ext; simp only [LinearMap.map_add, Pi.add_apply, neg_add]
      map_smul' := fun t v => by ext; simp }
  map_vadd' p v := by ext; simp
#align affine_basis.coords AffineBasis.coords

structure representing an affine basis of an affine space.
 * `AffineBasis.coord`: the map `P →ᵃ[k] k` corresponding to `i : ι`.
 * `AffineBasis.coord_apply_eq`: the behaviour of `AffineBasis.coord i` on `p i`.
 * `AffineBasis.coord_apply_ne`: the behaviour of `AffineBasis.coord i` on `p j` when `j ≠ i`.
 * `AffineBasis.coord_apply`: the behaviour of `AffineBasis.coord i` on `p j` for general `j`.
 * `AffineBasis.coord_apply_combination`: the characterisation of `AffineBasis.coord i` in terms
    of affine combinations, i.e., `AffineBasis.coord i (w₀ p₀ + w₁ p₁ + ⋯) = wᵢ`.

## TODO

structure AffineBasis (ι : Type u₁) (k : Type u₂) {V : Type u₃} (P : Type u₄) [AddCommGroup V]
  [AffineSpace V P] [Ring k] [Module k V] where
  protected toFun : ι → P
  protected ind' : AffineIndependent k toFun
  protected tot' : affineSpan k (range toFun) = ⊤
#align affine_basis AffineBasis