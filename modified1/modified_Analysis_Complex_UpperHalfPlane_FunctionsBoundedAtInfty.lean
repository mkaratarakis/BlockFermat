def atImInfty :=
  Filter.atTop.comap UpperHalfPlane.im
#align upper_half_plane.at_im_infty UpperHalfPlane.atImInfty

def IsBoundedAtImInfty {α : Type*} [Norm α] (f : ℍ → α) : Prop :=
  BoundedAtFilter atImInfty f
#align upper_half_plane.is_bounded_at_im_infty UpperHalfPlane.IsBoundedAtImInfty

def IsZeroAtImInfty {α : Type*} [Zero α] [TopologicalSpace α] (f : ℍ → α) : Prop :=
  ZeroAtFilter atImInfty f
#align upper_half_plane.is_zero_at_im_infty UpperHalfPlane.IsZeroAtImInfty

def zeroAtImInftySubmodule (α : Type*) [NormedField α] : Submodule α (ℍ → α) :=
  zeroAtFilterSubmodule _ atImInfty
#align upper_half_plane.zero_at_im_infty_submodule UpperHalfPlane.zeroAtImInftySubmodule

def boundedAtImInftySubalgebra (α : Type*) [NormedField α] : Subalgebra α (ℍ → α) :=
  boundedFilterSubalgebra _ atImInfty
#align upper_half_plane.bounded_at_im_infty_subalgebra UpperHalfPlane.boundedAtImInftySubalgebra