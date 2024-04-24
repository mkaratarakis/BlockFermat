def t0Space_iff_uniformity

theorem t0Space_iff_uniformity' :
    T0Space α ↔ Pairwise fun x y ↦ ∃ r ∈ 𝓤 α, (x, y) ∉ r := by
  simp [t0Space_iff_not_inseparable, inseparable_iff_ker_uniformity]
#align separated_def' t0Space_iff_uniformity'

def lift' [T0Space β] (f : α → β) : SeparationQuotient α → β :=
  if hc : UniformContinuous f then lift f fun _ _ h => (h.map hc.continuous).eq
  else fun x => f (Nonempty.some ⟨x.out'⟩)
#align uniform_space.separation_quotient.lift SeparationQuotient.lift'

def map (f : α → β) : SeparationQuotient α → SeparationQuotient β := lift' (mk ∘ f)
#align uniform_space.separation_quotient.map SeparationQuotient.map

structure
that agrees with the quotient topology.
We also prove that the quotient map induces uniformity on the original space.

Finally, we turn `SeparationQuotient` into a functor
(not in terms of `CategoryTheory.Functor` to avoid extra imports)
by defining `SeparationQuotient.lift'` and `SeparationQuotient.map` operations.

## Main definitions

structure on `SeparationQuotient α`,
  where `α` is a uniform space;

* `SeparationQuotient.lift'`: given a map `f : α → β`
  from a uniform space to a separated uniform space,
  lift it to a map `SeparationQuotient α → β`;
  if the original map is not uniformly continuous, then returns a constant map.

* `SeparationQuotient.map`: given a map `f : α → β` between uniform spaces,
  returns a map `SeparationQuotient α → SeparationQuotient β`.
  If the original map is not uniformly continuous, then returns a constant map.
  Otherwise, `SeparationQuotient.map f (SeparationQuotient.mk x) = SeparationQuotient.mk (f x)`.

## Main results

structure on the original space.
* `SeparationQuotient.uniformContinuous_lift'`: factoring a uniformly continuous map through the
  separation quotient gives a uniformly continuous map.
* `SeparationQuotient.uniformContinuous_map`: maps induced between separation quotients are
  uniformly continuous.

## Implementation notes