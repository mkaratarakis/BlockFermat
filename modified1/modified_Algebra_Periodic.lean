def Periodic [Add α] (f : α → β) (c : α) : Prop :=
  ∀ x : α, f (x + c) = f x
#align function.periodic Function.Periodic

def Periodic.lift [AddGroup α] (h : Periodic f c) (x : α ⧸ AddSubgroup.zmultiples c) : β :=
  Quotient.liftOn' x f fun a b h' => by
    rw [QuotientAddGroup.leftRel_apply] at h'
    obtain ⟨k, hk⟩ := h'
    exact (h.zsmul k _).symm.trans (congr_arg f (add_eq_of_eq_neg_add hk))
#align function.periodic.lift Function.Periodic.lift

def Antiperiodic [Add α] [Neg β] (f : α → β) (c : α) : Prop :=
  ∀ x : α, f (x + c) = -f x
#align function.antiperiodic Function.Antiperiodic