def IsBounded (r : α → α → Prop) (f : Filter α) :=
  ∃ b, ∀ᶠ x in f, r x b
#align filter.is_bounded Filter.IsBounded

def IsBoundedUnder (r : α → α → Prop) (f : Filter β) (u : β → α) :=
  (map u f).IsBounded r
#align filter.is_bounded_under Filter.IsBoundedUnder

def IsCobounded (r : α → α → Prop) (f : Filter α) :=
  ∃ b, ∀ a, (∀ᶠ x in f, r x a) → r b a
#align filter.is_cobounded Filter.IsCobounded

def IsCoboundedUnder (r : α → α → Prop) (f : Filter β) (u : β → α) :=
  (map u f).IsCobounded r
#align filter.is_cobounded_under Filter.IsCoboundedUnder

def is_bounded_default : tactic Unit :=
--   tactic.applyc `` is_cobounded_le_of_bot <|>
--     tactic.applyc `` is_cobounded_ge_of_top <|>
--       tactic.applyc `` is_bounded_le_of_top <|> tactic.applyc `` is_bounded_ge_of_bot
-- #align filter.is_bounded_default filter.IsBounded_default

def limsSup (f : Filter α) : α :=
  sInf { a | ∀ᶠ n in f, n ≤ a }
set_option linter.uppercaseLean3 false in
#align filter.Limsup Filter.limsSup

def limsInf (f : Filter α) : α :=
  sSup { a | ∀ᶠ n in f, a ≤ n }
set_option linter.uppercaseLean3 false in
#align filter.Liminf Filter.limsInf

def limsup (u : β → α) (f : Filter β) : α :=
  limsSup (map u f)
#align filter.limsup Filter.limsup

def liminf (u : β → α) (f : Filter β) : α :=
  limsInf (map u f)
#align filter.liminf Filter.liminf

def blimsup (u : β → α) (f : Filter β) (p : β → Prop) :=
  sInf { a | ∀ᶠ x in f, p x → u x ≤ a }
#align filter.blimsup Filter.blimsup

def bliminf (u : β → α) (f : Filter β) (p : β → Prop) :=
  sSup { a | ∀ᶠ x in f, p x → a ≤ u x }
#align filter.bliminf Filter.bliminf

def liminf_reparam
    (f : ι → α) (s : ι' → Set ι) (p : ι' → Prop) [Countable (Subtype p)] [Nonempty (Subtype p)]
    (j : Subtype p) : Subtype p :=
  let m : Set (Subtype p) := {j | BddBelow (range (fun (i : s j) ↦ f i))}
  let g : ℕ → Subtype p := (exists_surjective_nat _).choose
  have Z : ∃ n, g n ∈ m ∨ ∀ j, j ∉ m := by
    by_cases H : ∃ j, j ∈ m
    · rcases H with ⟨j, hj⟩
      rcases (exists_surjective_nat (Subtype p)).choose_spec j with ⟨n, rfl⟩
      exact ⟨n, Or.inl hj⟩
    · push_neg at H
      exact ⟨0, Or.inr H⟩
  if j ∈ m then j else g (Nat.find Z)

/-- Writing a liminf as a supremum of infimum, in a (possibly non-complete) conditionally complete
linear order. A reparametrization trick is needed to avoid taking the infimum of sets which are
not bounded below. -/
theorem HasBasis.liminf_eq_ciSup_ciInf {v : Filter ι}
    {p : ι' → Prop} {s : ι' → Set ι} [Countable (Subtype p)] [Nonempty (Subtype p)]
    (hv : v.HasBasis p s) {f : ι → α} (hs : ∀ (j : Subtype p), (s j).Nonempty)
    (H : ∃ (j : Subtype p), BddBelow (range (fun (i : s j) ↦ f i))) :
    liminf f v = ⨆ (j : Subtype p), ⨅ (i : s (liminf_reparam f s p j)), f i := by
  rcases H with ⟨j0, hj0⟩
  let m : Set (Subtype p) := {j | BddBelow (range (fun (i : s j) ↦ f i))}
  have : ∀ (j : Subtype p), Nonempty (s j) := fun j ↦ Nonempty.coe_sort (hs j)
  have A : ⋃ (j : Subtype p), ⋂ (i : s j), Iic (f i) =
         ⋃ (j : Subtype p), ⋂ (i : s (liminf_reparam f s p j)), Iic (f i) := by
    apply Subset.antisymm
    · apply iUnion_subset (fun j ↦ ?_)
      by_cases hj : j ∈ m
      · have : j = liminf_reparam f s p j := by simp only [liminf_reparam, hj, ite_true]
        conv_lhs => rw [this]
        apply subset_iUnion _ j
      · simp only [m, mem_setOf_eq, ← nonempty_iInter_Iic_iff, not_nonempty_iff_eq_empty] at hj
        simp only [hj, empty_subset]
    · apply iUnion_subset (fun j ↦ ?_)
      exact subset_iUnion (fun (k : Subtype p) ↦ (⋂ (i : s k), Iic (f i))) (liminf_reparam f s p j)
  have B : ∀ (j : Subtype p), ⋂ (i : s (liminf_reparam f s p j)), Iic (f i) =
                                Iic (⨅ (i : s (liminf_reparam f s p j)), f i) := by
    intro j
    apply (Iic_ciInf _).symm
    change liminf_reparam f s p j ∈ m
    by_cases Hj : j ∈ m
    · simpa only [liminf_reparam, if_pos Hj] using Hj
    · simp only [liminf_reparam, if_neg Hj]
      have Z : ∃ n, (exists_surjective_nat (Subtype p)).choose n ∈ m ∨ ∀ j, j ∉ m := by
        rcases (exists_surjective_nat (Subtype p)).choose_spec j0 with ⟨n, rfl⟩
        exact ⟨n, Or.inl hj0⟩
      rcases Nat.find_spec Z with hZ|hZ
      · exact hZ
      · exact (hZ j0 hj0).elim
  simp_rw [hv.liminf_eq_sSup_iUnion_iInter, A, B, sSup_iUnion_Iic]

/-- Writing a liminf as a supremum of infimum, in a (possibly non-complete) conditionally complete
linear order. A reparametrization trick is needed to avoid taking the infimum of sets which are
not bounded below. -/
theorem HasBasis.liminf_eq_ite {v : Filter ι} {p : ι' → Prop} {s : ι' → Set ι}
    [Countable (Subtype p)] [Nonempty (Subtype p)] (hv : v.HasBasis p s) (f : ι → α):
    liminf f v = if ∃ (j : Subtype p), s j = ∅ then sSup univ else
      if ∀ (j : Subtype p), ¬BddBelow (range (fun (i : s j) ↦ f i)) then sSup ∅
      else ⨆ (j : Subtype p), ⨅ (i : s (liminf_reparam f s p j)), f i := by
  by_cases H : ∃ (j : Subtype p), s j = ∅
  · rw [if_pos H]
    rcases H with ⟨j, hj⟩
    simp [hv.liminf_eq_sSup_univ_of_empty j j.2 hj]
  rw [if_neg H]
  by_cases H' : ∀ (j : Subtype p), ¬BddBelow (range (fun (i : s j) ↦ f i))
  · have A : ∀ (j : Subtype p), ⋂ (i : s j), Iic (f i) = ∅ := by
      simp_rw [← not_nonempty_iff_eq_empty, nonempty_iInter_Iic_iff]
      exact H'
    simp_rw [if_pos H', hv.liminf_eq_sSup_iUnion_iInter, A, iUnion_empty]
  rw [if_neg H']
  apply hv.liminf_eq_ciSup_ciInf
  · push_neg at H
    simpa only [nonempty_iff_ne_empty] using H
  · push_neg at H'
    exact H'

/-- Given an indexed family of sets `s j` and a function `f`, then `limsup_reparam j` is equal
to `j` if `f` is bounded above on `s j`, and otherwise to some index `k` such that `f` is bounded
above on `s k` (if there exists one). To ensure good measurability behavior, this index `k` is
chosen as the minimal suitable index. This function is used to write down a limsup in a measurable
way, in `Filter.HasBasis.limsup_eq_ciInf_ciSup` and `Filter.HasBasis.limsup_eq_ite`. -/
noncomputable def limsup_reparam
    (f : ι → α) (s : ι' → Set ι) (p : ι' → Prop) [Countable (Subtype p)] [Nonempty (Subtype p)]
    (j : Subtype p) : Subtype p :=
  liminf_reparam (α := αᵒᵈ) f s p j

/-- Writing a limsup as an infimum of supremum, in a (possibly non-complete) conditionally complete
linear order. A reparametrization trick is needed to avoid taking the supremum of sets which are
not bounded above. -/
theorem HasBasis.limsup_eq_ciInf_ciSup {v : Filter ι}
    {p : ι' → Prop} {s : ι' → Set ι} [Countable (Subtype p)] [Nonempty (Subtype p)]
    (hv : v.HasBasis p s) {f : ι → α} (hs : ∀ (j : Subtype p), (s j).Nonempty)
    (H : ∃ (j : Subtype p), BddAbove (range (fun (i : s j) ↦ f i))) :
    limsup f v = ⨅ (j : Subtype p), ⨆ (i : s (limsup_reparam f s p j)), f i :=
  HasBasis.liminf_eq_ciSup_ciInf (α := αᵒᵈ) hv hs H

/-- Writing a limsup as an infimum of supremum, in a (possibly non-complete) conditionally complete
linear order. A reparametrization trick is needed to avoid taking the supremum of sets which are
not bounded below. -/
theorem HasBasis.limsup_eq_ite {v : Filter ι} {p : ι' → Prop} {s : ι' → Set ι}
    [Countable (Subtype p)] [Nonempty (Subtype p)] (hv : v.HasBasis p s) (f : ι → α) :
    limsup f v = if ∃ (j : Subtype p), s j = ∅ then sInf univ else
      if ∀ (j : Subtype p), ¬BddAbove (range (fun (i : s j) ↦ f i)) then sInf ∅
      else ⨅ (j : Subtype p), ⨆ (i : s (limsup_reparam f s p j)), f i :=
  HasBasis.liminf_eq_ite (α := αᵒᵈ) hv f

end Classical

end ConditionallyCompleteLinearOrder

end Filter

section Order

open Filter

theorem Monotone.isBoundedUnder_le_comp_iff [Nonempty β] [LinearOrder β] [Preorder γ] [NoMaxOrder γ]
    {g : β → γ} {f : α → β} {l : Filter α} (hg : Monotone g) (hg' : Tendsto g atTop atTop) :
    IsBoundedUnder (· ≤ ·) l (g ∘ f) ↔ IsBoundedUnder (· ≤ ·) l f := by
  refine' ⟨_, fun h => h.isBoundedUnder (α := β) hg⟩
  rintro ⟨c, hc⟩; rw [eventually_map] at hc
  obtain ⟨b, hb⟩ : ∃ b, ∀ a ≥ b, c < g a := eventually_atTop.1 (hg'.eventually_gt_atTop c)
  exact ⟨b, hc.mono fun x hx => not_lt.1 fun h => (hb _ h.le).not_le hx⟩
#align monotone.is_bounded_under_le_comp Monotone.isBoundedUnder_le_comp_iff