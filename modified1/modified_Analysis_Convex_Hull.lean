def convexHull : ClosureOperator (Set E) := .ofCompletePred (Convex 𝕜) fun _ ↦ convex_sInter
#align convex_hull convexHull