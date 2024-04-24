def toHomeomorph (e : α ≃o β) : α ≃ₜ β :=
  { e with
    continuous_toFun := e.continuous
    continuous_invFun := e.symm.continuous }
#align order_iso.to_homeomorph OrderIso.toHomeomorph