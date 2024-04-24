def equivProd : IntegrationParams ≃ Bool × Boolᵒᵈ × Boolᵒᵈ where
  toFun l := ⟨l.1, OrderDual.toDual l.2, OrderDual.toDual l.3⟩
  invFun l := ⟨l.1, OrderDual.ofDual l.2.1, OrderDual.ofDual l.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
#align box_integral.integration_params.equiv_prod BoxIntegral.IntegrationParams.equivProd

def isoProd : IntegrationParams ≃o Bool × Boolᵒᵈ × Boolᵒᵈ :=
  ⟨equivProd, Iff.rfl⟩
#align box_integral.integration_params.iso_prod BoxIntegral.IntegrationParams.isoProd

def Riemann : IntegrationParams where
  bRiemann := true
  bHenstock := true
  bDistortion := false
set_option linter.uppercaseLean3 false in
#align box_integral.integration_params.Riemann BoxIntegral.IntegrationParams.Riemann

def Henstock : IntegrationParams :=
  ⟨false, true, false⟩
set_option linter.uppercaseLean3 false in
#align box_integral.integration_params.Henstock BoxIntegral.IntegrationParams.Henstock

def McShane : IntegrationParams :=
  ⟨false, false, false⟩
set_option linter.uppercaseLean3 false in
#align box_integral.integration_params.McShane BoxIntegral.IntegrationParams.McShane

def GP : IntegrationParams := ⊥
set_option linter.uppercaseLean3 false in
#align box_integral.integration_params.GP BoxIntegral.IntegrationParams.GP

def RCond {ι : Type*} (l : IntegrationParams) (r : (ι → ℝ) → Ioi (0 : ℝ)) : Prop :=
  l.bRiemann → ∀ x, r x = r 0
#align box_integral.integration_params.r_cond BoxIntegral.IntegrationParams.RCond

def toFilterDistortion (l : IntegrationParams) (I : Box ι) (c : ℝ≥0) :
    Filter (TaggedPrepartition I) :=
  ⨅ (r : (ι → ℝ) → Ioi (0 : ℝ)) (_ : l.RCond r), 𝓟 { π | l.MemBaseSet I c r π }
#align box_integral.integration_params.to_filter_distortion BoxIntegral.IntegrationParams.toFilterDistortion

def toFilter (l : IntegrationParams) (I : Box ι) : Filter (TaggedPrepartition I) :=
  ⨆ c : ℝ≥0, l.toFilterDistortion I c
#align box_integral.integration_params.to_filter BoxIntegral.IntegrationParams.toFilter

def toFilterDistortioniUnion (l : IntegrationParams) (I : Box ι) (c : ℝ≥0) (π₀ : Prepartition I) :=
  l.toFilterDistortion I c ⊓ 𝓟 { π | π.iUnion = π₀.iUnion }
#align box_integral.integration_params.to_filter_distortion_Union BoxIntegral.IntegrationParams.toFilterDistortioniUnion

def toFilteriUnion (l : IntegrationParams) (I : Box ι) (π₀ : Prepartition I) :=
  ⨆ c : ℝ≥0, l.toFilterDistortioniUnion I c π₀
#align box_integral.integration_params.to_filter_Union BoxIntegral.IntegrationParams.toFilteriUnion

structure `BoxIntegral.IntegrationParams`. This structure will be used as an
argument in the definition of `BoxIntegral.integral` in order to use the same definition for a few
well-known definitions of integrals based on partitions of a rectangular box into subboxes (Riemann
integral, Henstock-Kurzweil integral, and McShane integral).

This structure holds three boolean values (see below), and encodes eight different sets of
parameters; only four of these values are used somewhere in `mathlib4`. Three of them correspond to
the integration theories listed above, and one is a generalization of the one-dimensional
Henstock-Kurzweil integral such that the divergence theorem works without additional integrability
assumptions.

Finally, for each set of parameters `l : BoxIntegral.IntegrationParams` and a rectangular box
`I : BoxIntegral.Box ι`, we define several `Filter`s that will be used either in the definition of
the corresponding integral, or in the proofs of its properties. We equip
`BoxIntegral.IntegrationParams` with a `BoundedOrder` structure such that larger
`IntegrationParams` produce larger filters.

## Main definitions

structure `BoxIntegral.IntegrationParams` has 3 boolean fields with the following meaning:

* `bRiemann`: the value `true` means that the filter corresponds to a Riemann-style integral, i.e.
  in the definition of integrability we require a constant upper estimate `r` on the size of boxes
  of a tagged partition; the value `false` means that the estimate may depend on the position of the
  tag.

* `bHenstock`: the value `true` means that we require that each tag belongs to its own closed box;
  the value `false` means that we only require that tags belong to the ambient box.

* `bDistortion`: the value `true` means that `r` can depend on the maximal ratio of sides of the
  same box of a partition. Presence of this case make quite a few proofs harder but we can prove the
  divergence theorem only for the filter `BoxIntegral.IntegrationParams.GP = ⊥ =
  {bRiemann := false, bHenstock := true, bDistortion := true}`.

### Well-known sets of parameters

structure BoxIntegral.IntegrationParams.MemBaseSet (l : BoxIntegral.IntegrationParams)
  (I : BoxIntegral.Box ι) (c : ℝ≥0) (r : (ι → ℝ) → Ioi (0 : ℝ))
  (π : BoxIntegral.TaggedPrepartition I) : Prop where
```

This predicate says that

* if `l.bHenstock`, then `π` is a Henstock prepartition, i.e. each tag belongs to the corresponding
  closed box;
* `π` is subordinate to `r`;
* if `l.bDistortion`, then the distortion of each box in `π` is less than or equal to `c`;
* if `l.bDistortion`, then there exists a prepartition `π'` with distortion `≤ c` that covers
  exactly `I \ π.iUnion`.

The last condition is always true for `c > 1`, see TODO section for more details.

Then we define a predicate `BoxIntegral.IntegrationParams.RCond` on functions
`r : (ι → ℝ) → {x : ℝ | 0 < x}`. If `l.bRiemann`, then this predicate requires `r` to be a constant
function, otherwise it imposes no restrictions on `r`. We introduce this definition to prove a few
dot-notation lemmas: e.g., `BoxIntegral.IntegrationParams.RCond.min` says that the pointwise
minimum of two functions that satisfy this condition satisfies this condition as well.

Then we define four filters on `BoxIntegral.TaggedPrepartition I`.

* `BoxIntegral.IntegrationParams.toFilterDistortion`: an auxiliary filter that takes parameters
  `(l : BoxIntegral.IntegrationParams) (I : BoxIntegral.Box ι) (c : ℝ≥0)` and returns the
  filter generated by all sets `{π | MemBaseSet l I c r π}`, where `r` is a function satisfying
  the predicate `BoxIntegral.IntegrationParams.RCond l`;

* `BoxIntegral.IntegrationParams.toFilter l I`: the supremum of `l.toFilterDistortion I c`
  over all `c : ℝ≥0`;

* `BoxIntegral.IntegrationParams.toFilterDistortioniUnion l I c π₀`, where `π₀` is a
  prepartition of `I`: the infimum of `l.toFilterDistortion I c` and the principal filter
  generated by `{π | π.iUnion = π₀.iUnion}`;

* `BoxIntegral.IntegrationParams.toFilteriUnion l I π₀`: the supremum of
  `l.toFilterDistortioniUnion l I c π₀` over all `c : ℝ≥0`. This is the filter (in the case
  `π₀ = ⊤` is the one-box partition of `I`) used in the definition of the integral of a function
  over a box.

## Implementation details

structure holding 3 boolean values used to define a filter to be
used in the definition of a box-integrable function.

* `bRiemann`: the value `true` means that the filter corresponds to a Riemann-style integral, i.e.
  in the definition of integrability we require a constant upper estimate `r` on the size of boxes
  of a tagged partition; the value `false` means that the estimate may depend on the position of the
  tag.

* `bHenstock`: the value `true` means that we require that each tag belongs to its own closed box;
  the value `false` means that we only require that tags belong to the ambient box.

* `bDistortion`: the value `true` means that `r` can depend on the maximal ratio of sides of the
  same box of a partition. Presence of this case makes quite a few proofs harder but we can prove
  the divergence theorem only for the filter `BoxIntegral.IntegrationParams.GP = ⊥ =
  {bRiemann := false, bHenstock := true, bDistortion := true}`.
-/
@[ext]
structure IntegrationParams : Type where
  (bRiemann bHenstock bDistortion : Bool)
#align box_integral.integration_params BoxIntegral.IntegrationParams

structure MemBaseSet (l : IntegrationParams) (I : Box ι) (c : ℝ≥0) (r : (ι → ℝ) → Ioi (0 : ℝ))
    (π : TaggedPrepartition I) : Prop where
  protected isSubordinate : π.IsSubordinate r
  protected isHenstock : l.bHenstock → π.IsHenstock
  protected distortion_le : l.bDistortion → π.distortion ≤ c
  protected exists_compl : l.bDistortion → ∃ π' : Prepartition I,
    π'.iUnion = ↑I \ π.iUnion ∧ π'.distortion ≤ c
#align box_integral.integration_params.mem_base_set BoxIntegral.IntegrationParams.MemBaseSet