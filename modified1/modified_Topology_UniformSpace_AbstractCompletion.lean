def ofComplete [T0Space α] [CompleteSpace α] : AbstractCompletion α :=
  mk α id inferInstance inferInstance inferInstance uniformInducing_id denseRange_id
#align abstract_completion.of_complete AbstractCompletion.ofComplete

def extend (f : α → β) : hatα → β :=
  if UniformContinuous f then pkg.denseInducing.extend f else fun x => f (pkg.dense.some x)
#align abstract_completion.extend AbstractCompletion.extend

def (hf : UniformContinuous f) : pkg.extend f = pkg.denseInducing.extend f :=
  if_pos hf
#align abstract_completion.extend_def AbstractCompletion.extend_def

def hf]
  exact pkg.denseInducing.extend_eq hf.continuous a
#align abstract_completion.extend_coe AbstractCompletion.extend_coe

def hf]
    exact uniformContinuous_uniformly_extend pkg.uniformInducing pkg.dense hf
  · change UniformContinuous (ite _ _ _)
    rw [if_neg hf]
    exact uniformContinuous_of_const fun a b => by congr 1
#align abstract_completion.uniform_continuous_extend AbstractCompletion.uniformContinuous_extend

def map (f : α → β) : hatα → hatβ :=
  pkg.extend (ι' ∘ f)
#align abstract_completion.map AbstractCompletion.map

def compare : pkg.space → pkg'.space :=
  pkg.extend pkg'.coe
#align abstract_completion.compare AbstractCompletion.compare

def compareEquiv : pkg.space ≃ᵤ pkg'.space
    where
  toFun := pkg.compare pkg'
  invFun := pkg'.compare pkg
  left_inv := congr_fun (pkg'.inverse_compare pkg)
  right_inv := congr_fun (pkg.inverse_compare pkg')
  uniformContinuous_toFun := uniformContinuous_compare _ _
  uniformContinuous_invFun := uniformContinuous_compare _ _
#align abstract_completion.compare_equiv AbstractCompletion.compareEquiv

def prod : AbstractCompletion (α × β)
    where
  space := hatα × hatβ
  coe p := ⟨ι p.1, ι' p.2⟩
  uniformStruct := inferInstance
  complete := inferInstance
  separation := inferInstance
  uniformInducing := UniformInducing.prod pkg.uniformInducing pkg'.uniformInducing
  dense := DenseRange.prod_map pkg.dense pkg'.dense
#align abstract_completion.prod AbstractCompletion.prod

def extend₂ (f : α → β → γ) : hatα → hatβ → γ :=
  curry <| (pkg.prod pkg').extend (uncurry f)
#align abstract_completion.extend₂ AbstractCompletion.extend₂

def map₂ (f : α → β → γ) : hatα → hatβ → hatγ :=
  pkg.extend₂ pkg' (pkg''.coe ∘₂ f)
#align abstract_completion.map₂ AbstractCompletion.map₂

structure on α.
Assuming these properties we "extend" uniformly continuous maps from α to complete Hausdorff spaces
to the completions of α. This is the universal property expected from a completion.
It is then used to extend uniformly continuous maps from α to α' to maps between
completions of α and α'.

This file does not construct any such completion, it only study consequences of their existence.
The first advantage is that formal properties are clearly highlighted without interference from
construction details. The second advantage is that this framework can then be used to compare
different completion constructions. See `Topology/UniformSpace/CompareReals` for an example.
Of course the comparison comes from the universal property as usual.

A general explicit construction of completions is done in `UniformSpace/Completion`, leading
to a functor from uniform spaces to complete Hausdorff uniform spaces that is left adjoint to the
inclusion, see `UniformSpace/UniformSpaceCat` for the category packaging.

## Implementation notes

structure on `α`. -/
structure AbstractCompletion (α : Type u) [UniformSpace α] where
  /-- The underlying space of the completion. -/
  space : Type u
  /-- A map from a space to its completion. -/
  coe : α → space
  /-- The completion carries a uniform structure. -/
  uniformStruct : UniformSpace space
  /-- The completion is complete. -/
  complete : CompleteSpace space
  /-- The completion is a T₀ space. -/
  separation : T0Space space
  /-- The map into the completion is uniform-inducing. -/
  uniformInducing : UniformInducing coe
  /-- The map into the completion has dense range. -/
  dense : DenseRange coe
#align abstract_completion AbstractCompletion