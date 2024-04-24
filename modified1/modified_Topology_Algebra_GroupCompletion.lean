def toCompl : α →+ Completion α where
  toFun := (↑)
  map_add' := coe_add
  map_zero' := coe_zero
#align uniform_space.completion.to_compl UniformSpace.Completion.toCompl

def AddMonoidHom.extension [CompleteSpace β] [T0Space β] (f : α →+ β) (hf : Continuous f) :
    Completion α →+ β :=
  have hf : UniformContinuous f := uniformContinuous_addMonoidHom_of_continuous hf
  { toFun := Completion.extension f
    map_zero' := by rw [← coe_zero, extension_coe hf, f.map_zero]
    map_add' := fun a b ↦
      Completion.induction_on₂ a b
        (isClosed_eq (continuous_extension.comp continuous_add)
          ((continuous_extension.comp continuous_fst).add
            (continuous_extension.comp continuous_snd)))
        fun a b ↦
        show Completion.extension f _ = Completion.extension f _ + Completion.extension f _ by
        rw_mod_cast [extension_coe hf, extension_coe hf, extension_coe hf, f.map_add] }
#align add_monoid_hom.extension AddMonoidHom.extension

def AddMonoidHom.completion (f : α →+ β) (hf : Continuous f) : Completion α →+ Completion β :=
  (toCompl.comp f).extension (continuous_toCompl.comp hf)
#align add_monoid_hom.completion AddMonoidHom.completion

structure
on the completion of an abelian group endowed with a compatible uniform structure.
Then the instance `UniformSpace.Completion.uniformAddGroup` proves this group structure is
compatible with the completed uniform structure. The compatibility condition is `UniformAddGroup`.

## Main declarations: