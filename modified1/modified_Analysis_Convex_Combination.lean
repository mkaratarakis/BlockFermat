def Finset.centerMass (t : Finset ι) (w : ι → R) (z : ι → E) : E :=
  (∑ i in t, w i)⁻¹ • ∑ i in t, w i • z i
#align finset.center_mass Finset.centerMass

def convexHullAddMonoidHom : Set E →+ Set E where
  toFun := convexHull R
  map_add' := convexHull_add
  map_zero' := convexHull_zero
#align convex_hull_add_monoid_hom convexHullAddMonoidHom