def Function.leftLim (f : α → β) (a : α) : β := by
  classical
  haveI : Nonempty β := ⟨f a⟩
  letI : TopologicalSpace α := Preorder.topology α
  exact if 𝓝[<] a = ⊥ ∨ ¬∃ y, Tendsto f (𝓝[<] a) (𝓝 y) then f a else limUnder (𝓝[<] a) f
#align function.left_lim Function.leftLim

def Function.rightLim (f : α → β) (a : α) : β :=
  @Function.leftLim αᵒᵈ β _ _ f a
#align function.right_lim Function.rightLim