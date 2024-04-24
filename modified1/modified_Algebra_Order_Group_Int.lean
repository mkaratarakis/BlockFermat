def inductionOn' {C : ℤ → Sort*}
    (z : ℤ) (b : ℤ) (H0 : C b) (Hs : ∀ k, b ≤ k → C k → C (k + 1))
    (Hp : ∀ k ≤ b, C k → C (k - 1)) : C z := by
  rw [← sub_add_cancel (G := ℤ) z b, add_comm]
  exact match z - b with
  | .ofNat n => pos n
  | .negSucc n => neg n
where
  /-- The positive case of `Int.inductionOn'`. -/
  pos : ∀ n : ℕ, C (b + n)
  | 0 => _root_.cast (by erw [add_zero]) H0
  | n+1 => _root_.cast (by rw [add_assoc]; rfl) <|
    Hs _ (Int.le_add_of_nonneg_right (ofNat_nonneg _)) (pos n)

  /-- The negative case of `Int.inductionOn'`. -/
  neg : ∀ n : ℕ, C (b + -[n+1])
  | 0 => Hp _ (Int.le_refl _) H0
  | n+1 => by
    refine _root_.cast (by rw [add_sub_assoc]; rfl) (Hp _ (Int.le_of_lt ?_) (neg n))
    conv => rhs; apply (add_zero b).symm
    rw [Int.add_lt_add_iff_left]; apply negSucc_lt_zero
#align int.induction_on' Int.inductionOn'