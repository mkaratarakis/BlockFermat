def atTop [Preorder α] : Filter α :=
  ⨅ a, 𝓟 (Ici a)
#align filter.at_top Filter.atTop

def atBot [Preorder α] : Filter α :=
  ⨅ a, 𝓟 (Iic a)
#align filter.at_bot Filter.atBot