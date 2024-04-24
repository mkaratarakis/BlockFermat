def smoothCoordChange (he : e ∈ a.pretrivializationAtlas)
    (he' : e' ∈ a.pretrivializationAtlas) (b : B) : F →L[𝕜] F :=
  Classical.choose (ha.exists_smoothCoordChange e he e' he') b
#align vector_prebundle.smooth_coord_change VectorPrebundle.smoothCoordChange

structure given by its trivializations -- these are charts to `B × F`.
Then, by "composition", if `B` is itself a charted space over `H` (e.g. a smooth manifold), then `E`
is also a charted space over `H × F`.

Now, we define `SmoothVectorBundle` as the `Prop` of having smooth transition functions.
Recall the structure groupoid `smoothFiberwiseLinear` on `B × F` consisting of smooth, fiberwise
linear partial homeomorphisms.  We show that our definition of "smooth vector bundle" implies
`HasGroupoid` for this groupoid, and show (by a "composition" of `HasGroupoid` instances) that
this means that a smooth vector bundle is a smooth manifold.

Since `SmoothVectorBundle` is a mixin, it should be easy to make variants and for many such
variants to coexist -- vector bundles can be smooth vector bundles over several different base
fields, they can also be C^k vector bundles, etc.

## Main definitions and constructions

structure groupoid `smoothFiberwiseLinear`.

* `Bundle.TotalSpace.smoothManifoldWithCorners`: A smooth vector bundle is naturally a smooth
  manifold.

* `VectorBundleCore.smoothVectorBundle`: If a (topological) `VectorBundleCore` is smooth,
  in the sense of having smooth transition functions (cf. `VectorBundleCore.IsSmooth`),
  then the vector bundle constructed from it is a smooth vector bundle.

* `VectorPrebundle.smoothVectorBundle`: If a `VectorPrebundle` is smooth,
  in the sense of having smooth transition functions (cf. `VectorPrebundle.IsSmooth`),
  then the vector bundle constructed from it is a smooth vector bundle.

* `Bundle.Prod.smoothVectorBundle`: The direct sum of two smooth vector bundles is a smooth vector
  bundle.
-/

assert_not_exists mfderiv

open Bundle Set PartialHomeomorph

open Function (id_def)

open Filter

open scoped Manifold Bundle Topology

variable {𝕜 B B' F M : Type*} {E : B → Type*}

/-! ### Charted space structure on a fiber bundle -/