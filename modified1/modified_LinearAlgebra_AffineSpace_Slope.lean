def slope (f : k → PE) (a b : k) : E :=
  (b - a)⁻¹ • (f b -ᵥ f a)
#align slope slope

def (f : k → PE) : slope f = fun a b => (b - a)⁻¹ • (f b -ᵥ f a) :=
  rfl
#align slope_fun_def slope_fun_def