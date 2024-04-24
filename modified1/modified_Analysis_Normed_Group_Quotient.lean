def normedMk (S : AddSubgroup M) : NormedAddGroupHom M (M ⧸ S) :=
  { QuotientAddGroup.mk' S with
    bound' := ⟨1, fun m => by simpa [one_mul] using quotient_norm_mk_le _ m⟩ }
#align add_subgroup.normed_mk AddSubgroup.normedMk

def lift {N : Type*} [SeminormedAddCommGroup N] (S : AddSubgroup M)
    (f : NormedAddGroupHom M N) (hf : ∀ s ∈ S, f s = 0) : NormedAddGroupHom (M ⧸ S) N :=
  { QuotientAddGroup.lift S f.toAddMonoidHom hf with
    bound' := ⟨‖f‖, norm_lift_apply_le f hf⟩ }
#align normed_add_group_hom.lift NormedAddGroupHom.lift

structure on the quotient by
    an additive subgroup. This is an instance so there is no need to explicitly use it.

* `normedAddCommGroupQuotient` : The normed group structure on the quotient by
    a closed additive subgroup. This is an instance so there is no need to explicitly use it.

* `normedMk S` : the normed group hom from `M` to `M ⧸ S`.

* `lift S f hf`: implements the universal property of `M ⧸ S`. Here
    `(f : NormedAddGroupHom M N)`, `(hf : ∀ s ∈ S, f s = 0)` and
    `lift S f hf : NormedAddGroupHom (M ⧸ S) N`.

* `IsQuotient`: given `f : NormedAddGroupHom M N`, `IsQuotient f` means `N` is isomorphic
    to a quotient of `M` by a subgroup, with projection `f`. Technically it asserts `f` is
    surjective and the norm of `f x` is the infimum of the norms of `x + m` for `m` in `f.ker`.

## Main results

structure
includes a uniform space structure which includes a topological space structure, together
with propositional fields asserting compatibility conditions.
The usual way to define a `SeminormedAddCommGroup` is to let Lean build a uniform space structure
using the provided norm, and then trivially build a proof that the norm and uniform structure are
compatible. Here the uniform structure is provided using `TopologicalAddGroup.toUniformSpace`
which uses the topological structure and the group structure to build the uniform structure. This
uniform structure induces the correct topological structure by construction, but the fact that it
is compatible with the norm is not obvious; this is where the mathematical content explained in
the previous paragraph kicks in.

-/


noncomputable section

open QuotientAddGroup Metric Set Topology NNReal

variable {M N : Type*} [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]

/-- The definition of the norm on the quotient by an additive subgroup. -/
noncomputable instance normOnQuotient (S : AddSubgroup M) : Norm (M ⧸ S) where
  norm x := sInf (norm '' { m | mk' S m = x })
#align norm_on_quotient normOnQuotient

structure on the quotient by an additive subgroup. -/
noncomputable instance AddSubgroup.seminormedAddCommGroupQuotient (S : AddSubgroup M) :
    SeminormedAddCommGroup (M ⧸ S) where
  dist x y := ‖x - y‖
  dist_self x := by simp only [norm_mk_zero, sub_self]
  dist_comm := quotient_norm_sub_rev
  dist_triangle x y z := by
    refine le_trans ?_ (quotient_norm_add_le _ _ _)
    exact (congr_arg norm (sub_add_sub_cancel _ _ _).symm).le
  edist_dist x y := by exact ENNReal.coe_nnreal_eq _
  toUniformSpace := TopologicalAddGroup.toUniformSpace (M ⧸ S)
  uniformity_dist := by
    rw [uniformity_eq_comap_nhds_zero', ((quotient_nhd_basis S).comap _).eq_biInf]
    simp only [dist, quotient_norm_sub_rev (Prod.fst _), preimage_setOf_eq]
#align add_subgroup.seminormed_add_comm_group_quotient AddSubgroup.seminormedAddCommGroupQuotient

structure IsQuotient (f : NormedAddGroupHom M N) : Prop where
  protected surjective : Function.Surjective f
  protected norm : ∀ x, ‖f x‖ = sInf ((fun m => ‖x + m‖) '' f.ker)
#align normed_add_group_hom.is_quotient NormedAddGroupHom.IsQuotient