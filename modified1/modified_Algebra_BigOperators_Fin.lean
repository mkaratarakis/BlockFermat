def [CommMonoid β] {n : ℕ} (f : Fin n → β) :
    ∏ i, f i = ((List.finRange n).map f).prod := by simp [univ_def]
#align fin.prod_univ_def Fin.prod_univ_def

def Fin.sum_univ_def

@[to_additive]
theorem prod_ofFn [CommMonoid β] {n : ℕ} (f : Fin n → β) : (List.ofFn f).prod = ∏ i, f i := by
  rw [List.ofFn_eq_map, prod_univ_def]
#align fin.prod_of_fn Fin.prod_ofFn

def partialProd (f : Fin n → α) (i : Fin (n + 1)) : α :=
  ((List.ofFn f).take i).prod
#align fin.partial_prod Fin.partialProd

def finFunctionFinEquiv {m n : ℕ} : (Fin n → Fin m) ≃ Fin (m ^ n) :=
  Equiv.ofRightInverseOfCardLE (le_of_eq <| by simp_rw [Fintype.card_fun, Fintype.card_fin])
    (fun f => ⟨∑ i, f i * m ^ (i : ℕ), by
      induction' n with n ih
      · simp
      cases m
      · dsimp only [Nat.zero_eq] at f -- Porting note: added, wrong zero
        exact isEmptyElim (f <| Fin.last _)
      simp_rw [Fin.sum_univ_castSucc, Fin.coe_castSucc, Fin.val_last]
      refine' (add_lt_add_of_lt_of_le (ih _) <| mul_le_mul_right' (Fin.is_le _) _).trans_eq _
      rw [← one_add_mul (_ : ℕ), add_comm, pow_succ']
      -- Porting note: added, wrong `succ`
      rfl⟩)
    (fun a b => ⟨a / m ^ (b : ℕ) % m, by
      cases' n with n
      · exact b.elim0
      cases' m with m
      · dsimp only [Nat.zero_eq] at a -- Porting note: added, wrong zero
        rw [zero_pow n.succ_ne_zero] at a
        exact a.elim0
      · exact Nat.mod_lt _ m.succ_pos⟩)
    fun a => by
      dsimp
      induction' n with n ih
      · haveI : Subsingleton (Fin (m ^ 0)) := (Fin.castIso <| pow_zero _).toEquiv.subsingleton
        exact Subsingleton.elim _ _
      simp_rw [Fin.forall_iff, Fin.ext_iff] at ih
      ext
      simp_rw [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, pow_zero, Nat.div_one,
        mul_one, pow_succ', ← Nat.div_div_eq_div_mul, mul_left_comm _ m, ← mul_sum]
      rw [ih _ (Nat.div_lt_of_lt_mul ?_), Nat.mod_add_div]
      -- Porting note: replaces `a.is_lt` in the wildcard above. Caused by a refactor of the `npow`
      -- instance for `Fin`.
      exact a.is_lt.trans_eq (pow_succ' _ _)
#align fin_function_fin_equiv finFunctionFinEquiv

def finPiFinEquiv {m : ℕ} {n : Fin m → ℕ} : (∀ i : Fin m, Fin (n i)) ≃ Fin (∏ i : Fin m, n i) :=
  Equiv.ofRightInverseOfCardLE (le_of_eq <| by simp_rw [Fintype.card_pi, Fintype.card_fin])
    (fun f => ⟨∑ i, f i * ∏ j, n (Fin.castLE i.is_lt.le j), by
      induction' m with m ih
      · simp
      rw [Fin.prod_univ_castSucc, Fin.sum_univ_castSucc]
      suffices
        ∀ (n : Fin m → ℕ) (nn : ℕ) (f : ∀ i : Fin m, Fin (n i)) (fn : Fin nn),
          ((∑ i : Fin m, ↑(f i) * ∏ j : Fin i, n (Fin.castLE i.prop.le j)) + ↑fn * ∏ j, n j) <
            (∏ i : Fin m, n i) * nn by
        replace := this (Fin.init n) (n (Fin.last _)) (Fin.init f) (f (Fin.last _))
        rw [← Fin.snoc_init_self f]
        simp (config := { singlePass := true }) only [← Fin.snoc_init_self n]
        simp_rw [Fin.snoc_castSucc, Fin.snoc_last, Fin.snoc_init_self n]
        exact this
      intro n nn f fn
      cases nn
      · dsimp only [Nat.zero_eq] at fn -- Porting note: added, wrong zero
        exact isEmptyElim fn
      refine' (add_lt_add_of_lt_of_le (ih _) <| mul_le_mul_right' (Fin.is_le _) _).trans_eq _
      rw [← one_add_mul (_ : ℕ), mul_comm, add_comm]
      -- Porting note: added, wrong `succ`
      rfl⟩)
    (fun a b => ⟨(a / ∏ j : Fin b, n (Fin.castLE b.is_lt.le j)) % n b, by
      cases m
      · exact b.elim0
      cases' h : n b with nb
      · rw [prod_eq_zero (Finset.mem_univ _) h] at a
        exact isEmptyElim a
      exact Nat.mod_lt _ nb.succ_pos⟩)
    (by
      intro a; revert a; dsimp only [Fin.val_mk]
      refine' Fin.consInduction _ _ n
      · intro a
        haveI : Subsingleton (Fin (∏ i : Fin 0, i.elim0)) :=
          (Fin.castIso <| prod_empty).toEquiv.subsingleton
        exact Subsingleton.elim _ _
      · intro n x xs ih a
        simp_rw [Fin.forall_iff, Fin.ext_iff] at ih
        ext
        simp_rw [Fin.sum_univ_succ, Fin.cons_succ]
        have := fun i : Fin n =>
          Fintype.prod_equiv (Fin.castIso <| Fin.val_succ i).toEquiv
            (fun j => (Fin.cons x xs : _ → ℕ) (Fin.castLE (Fin.is_lt _).le j))
            (fun j => (Fin.cons x xs : _ → ℕ) (Fin.castLE (Nat.succ_le_succ (Fin.is_lt _).le) j))
            fun j => rfl
        simp_rw [this]
        clear this
        dsimp only [Fin.val_zero]
        simp_rw [Fintype.prod_empty, Nat.div_one, mul_one, Fin.cons_zero, Fin.prod_univ_succ]
        change (_ + ∑ y : _, _ / (x * _) % _ * (x * _)) = _
        simp_rw [← Nat.div_div_eq_div_mul, mul_left_comm (_ % _ : ℕ), ← mul_sum]
        convert Nat.mod_add_div _ _
        -- Porting note: new
        refine (ih (a / x) (Nat.div_lt_of_lt_mul <| a.is_lt.trans_eq ?_))
        exact Fin.prod_univ_succ _
        -- Porting note: was:
        /-
        refine' Eq.trans _ (ih (a / x) (Nat.div_lt_of_lt_mul <| a.is_lt.trans_eq _))
        swap
        · convert Fin.prod_univ_succ (Fin.cons x xs : _ → ℕ)
          simp_rw [Fin.cons_succ]
        congr with i
        congr with j
        · cases j
          rfl
        · cases j
          rfl-/)
#align fin_pi_fin_equiv finPiFinEquiv