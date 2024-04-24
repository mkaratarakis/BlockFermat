def min {r : α → α → Prop} (H : WellFounded r) (s : Set α) (h : s.Nonempty) : α :=
  Classical.choose (H.has_min s h)
#align well_founded.min WellFounded.min

def sup {r : α → α → Prop} (wf : WellFounded r) (s : Set α)
    (h : Bounded r s) : α :=
  wf.min { x | ∀ a ∈ s, r a x } h
#align well_founded.sup WellFounded.sup

def succ {r : α → α → Prop} (wf : WellFounded r) (x : α) : α :=
  if h : ∃ y, r x y then wf.min { y | r x y } h else x
#align well_founded.succ WellFounded.succ

def argmin [Nonempty α] : α :=
  WellFounded.min (InvImage.wf f h) Set.univ Set.univ_nonempty
#align function.argmin Function.argmin

def argminOn (s : Set α) (hs : s.Nonempty) : α :=
  WellFounded.min (InvImage.wf f h) s hs
#align function.argmin_on Function.argminOn