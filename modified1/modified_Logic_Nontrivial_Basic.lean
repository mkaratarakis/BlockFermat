def nontrivialPSumUnique (α : Type*) [Inhabited α] :
    PSum (Nontrivial α) (Unique α) :=
  if h : Nontrivial α then PSum.inl h
  else
    PSum.inr
      { default := default,
        uniq := fun x : α ↦ by
          by_contra H
          exact h ⟨_, _, H⟩ }
#align nontrivial_psum_unique nontrivialPSumUnique