def HasProd (f : β → α) (a : α) : Prop :=
  Tendsto (fun s : Finset β ↦ ∏ b in s, f b) atTop (𝓝 a)
#align has_sum HasSum

def Multipliable (f : β → α) : Prop :=
  ∃ a, HasProd f a
#align summable Summable

def tprod {β} (f : β → α) :=
  if h : Multipliable f then
  /- Note that the product might not be uniquely defined if the topology is not separated.
  When the multiplicative support of `f` is finite, we make the most reasonable choice to use the
  product over the multiplicative support. Otherwise, we choose arbitrarily an `a` satisfying
  `HasProd f a`. -/
    if (mulSupport f).Finite then finprod f
    else h.choose
  else 1
#align tsum tsum