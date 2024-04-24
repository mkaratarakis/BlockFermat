def {x : X} {s : CompositionSeries X} : x ∈ s ↔ x ∈ Set.range s :=
  Iff.rfl
#align composition_series.mem_def CompositionSeries.mem_def

def toList (s : CompositionSeries X) : List X :=
  List.ofFn s
#align composition_series.to_list CompositionSeries.toList

def ofList (l : List X) (hl : l ≠ []) (hc : List.Chain' IsMaximal l) : CompositionSeries X
    where
  length := l.length - 1
  series i :=
    l.nthLe i
      (by
        conv_rhs => rw [← tsub_add_cancel_of_le (Nat.succ_le_of_lt (List.length_pos_of_ne_nil hl))]
        exact i.2)
  step' := fun ⟨i, hi⟩ => List.chain'_iff_get.1 hc i hi
#align composition_series.of_list CompositionSeries.ofList

def top (s : CompositionSeries X) : X :=
  s (Fin.last _)
#align composition_series.top CompositionSeries.top

def bot (s : CompositionSeries X) : X :=
  s 0
#align composition_series.bot CompositionSeries.bot

def eraseTop (s : CompositionSeries X) : CompositionSeries X where
  length := s.length - 1
  series i := s ⟨i, lt_of_lt_of_le i.2 (Nat.succ_le_succ tsub_le_self)⟩
  step' i := by
    have := s.step ⟨i, lt_of_lt_of_le i.2 tsub_le_self⟩
    cases i
    exact this
#align composition_series.erase_top CompositionSeries.eraseTop

def append (s₁ s₂ : CompositionSeries X) (h : s₁.top = s₂.bot) : CompositionSeries X where
  length := s₁.length + s₂.length
  series := Matrix.vecAppend (Nat.add_succ s₁.length s₂.length).symm (s₁ ∘ Fin.castSucc) s₂
  step' i := by
    refine' Fin.addCases _ _ i
    · intro i
      rw [append_succ_castAdd_aux _ _ _ h, append_castAdd_aux]
      exact s₁.step i
    · intro i
      rw [append_natAdd_aux, append_succ_natAdd_aux]
      exact s₂.step i
#align composition_series.append CompositionSeries.append

def snoc (s : CompositionSeries X) (x : X) (hsat : IsMaximal s.top x) : CompositionSeries X where
  length := s.length + 1
  series := Fin.snoc s x
  step' i := by
    refine' Fin.lastCases _ _ i
    · rwa [Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last, ← top]
    · intro i
      rw [Fin.snoc_castSucc, ← Fin.castSucc_fin_succ, Fin.snoc_castSucc]
      exact s.step _
#align composition_series.snoc CompositionSeries.snoc

def Equivalent (s₁ s₂ : CompositionSeries X) : Prop :=
  ∃ f : Fin s₁.length ≃ Fin s₂.length,
    ∀ i : Fin s₁.length, Iso (s₁ (Fin.castSucc i), s₁ i.succ)
      (s₂ (Fin.castSucc (f i)), s₂ (Fin.succ (f i)))
#align composition_series.equivalent CompositionSeries.Equivalent

structure CompositionSeries (X : Type u) [Lattice X] [JordanHolderLattice X] : Type u where
  length : ℕ
  series : Fin (length + 1) → X
  step' : ∀ i : Fin length, IsMaximal (series (Fin.castSucc i)) (series (Fin.succ i))
#align composition_series CompositionSeries