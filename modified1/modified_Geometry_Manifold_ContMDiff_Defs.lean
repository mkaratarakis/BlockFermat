def ContDiffWithinAtProp (n : ℕ∞) (f : H → H') (s : Set H) (x : H) : Prop :=
  ContDiffWithinAt 𝕜 n (I' ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ range I) (I x)
#align cont_diff_within_at_prop ContDiffWithinAtProp

def ContMDiffWithinAt (n : ℕ∞) (f : M → M') (s : Set M) (x : M) :=
  LiftPropWithinAt (ContDiffWithinAtProp I I' n) f s x
#align cont_mdiff_within_at ContMDiffWithinAt

def SmoothWithinAt (f : M → M') (s : Set M) (x : M) :=
  ContMDiffWithinAt I I' ⊤ f s x
#align smooth_within_at SmoothWithinAt

def ContMDiffAt (n : ℕ∞) (f : M → M') (x : M) :=
  ContMDiffWithinAt I I' n f univ x
#align cont_mdiff_at ContMDiffAt

def SmoothAt (f : M → M') (x : M) :=
  ContMDiffAt I I' ⊤ f x
#align smooth_at SmoothAt

def ContMDiffOn (n : ℕ∞) (f : M → M') (s : Set M) :=
  ∀ x ∈ s, ContMDiffWithinAt I I' n f s x
#align cont_mdiff_on ContMDiffOn

def SmoothOn (f : M → M') (s : Set M) :=
  ContMDiffOn I I' ⊤ f s
#align smooth_on SmoothOn

def ContMDiff (n : ℕ∞) (f : M → M') :=
  ∀ x, ContMDiffAt I I' n f x
#align cont_mdiff ContMDiff

def Smooth (f : M → M') :=
  ContMDiff I I' ⊤ f
#align smooth Smooth