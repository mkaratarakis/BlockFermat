def IsNilpotent [Zero R] [Pow R ℕ] (x : R) : Prop :=
  ∃ n : ℕ, x ^ n = 0
#align is_nilpotent IsNilpotent

def nilpotencyClass : ℕ := sInf {k | x ^ k = 0}

@[simp] lemma nilpotencyClass_eq_zero_of_subsingleton [Subsingleton R] :
    nilpotencyClass x = 0 := by
  let s : Set ℕ := {k | x ^ k = 0}
  suffices s = univ by change sInf _ = 0; simp [s] at this; simp [this]
  exact eq_univ_iff_forall.mpr fun k ↦ Subsingleton.elim _ _

lemma isNilpotent_of_pos_nilpotencyClass (hx : 0 < nilpotencyClass x) :
    IsNilpotent x := by
  let s : Set ℕ := {k | x ^ k = 0}
  change s.Nonempty
  change 0 < sInf s at hx
  by_contra contra
  simp [not_nonempty_iff_eq_empty.mp contra] at hx

lemma pow_nilpotencyClass (hx : IsNilpotent x) : x ^ (nilpotencyClass x) = 0 :=
  Nat.sInf_mem hx

end ZeroPow

section MonoidWithZero

variable [MonoidWithZero R]

lemma nilpotencyClass_eq_succ_iff {k : ℕ} :
    nilpotencyClass x = k + 1 ↔ x ^ (k + 1) = 0 ∧ x ^ k ≠ 0 := by
  let s : Set ℕ := {k | x ^ k = 0}
  have : ∀ k₁ k₂ : ℕ, k₁ ≤ k₂ → k₁ ∈ s → k₂ ∈ s := fun k₁ k₂ h_le hk₁ ↦ pow_eq_zero_of_le h_le hk₁
  simp [s, nilpotencyClass, Nat.sInf_upward_closed_eq_succ_iff this]

@[simp] lemma nilpotencyClass_zero [Nontrivial R] :
    nilpotencyClass (0 : R) = 1 :=
  nilpotencyClass_eq_succ_iff.mpr <| by constructor <;> simp

@[simp] lemma pos_nilpotencyClass_iff [Nontrivial R] :
    0 < nilpotencyClass x ↔ IsNilpotent x := by
  refine ⟨isNilpotent_of_pos_nilpotencyClass, fun hx ↦ Nat.pos_of_ne_zero fun hx' ↦ ?_⟩
  replace hx := pow_nilpotencyClass hx
  rw [hx', pow_zero] at hx
  exact one_ne_zero hx

lemma pow_pred_nilpotencyClass [Nontrivial R] (hx : IsNilpotent x) :
    x ^ (nilpotencyClass x - 1) ≠ 0 :=
  (nilpotencyClass_eq_succ_iff.mp <| Nat.eq_add_of_sub_eq (pos_nilpotencyClass_iff.mpr hx) rfl).2

lemma eq_zero_of_nilpotencyClass_eq_one (hx : nilpotencyClass x = 1) :
    x = 0 := by
  have : IsNilpotent x := isNilpotent_of_pos_nilpotencyClass (hx ▸ one_pos)
  rw [← pow_nilpotencyClass this, hx, pow_one]

@[simp] lemma nilpotencyClass_eq_one [Nontrivial R] :
    nilpotencyClass x = 1 ↔ x = 0 :=
  ⟨eq_zero_of_nilpotencyClass_eq_one, fun hx ↦ hx ▸ nilpotencyClass_zero⟩

end MonoidWithZero

end NilpotencyClass

/-- A structure that has zero and pow is reduced if it has no nonzero nilpotent elements. -/
@[mk_iff]
class IsReduced (R : Type*) [Zero R] [Pow R ℕ] : Prop where
  /-- A reduced structure has no nonzero nilpotent elements. -/
  eq_zero : ∀ x : R, IsNilpotent x → x = 0
#align is_reduced IsReduced

def IsRadical [Dvd R] [Pow R ℕ] (y : R) : Prop :=
  ∀ (n : ℕ) (x), y ∣ x ^ n → y ∣ x
#align is_radical IsRadical

def nilradical (R : Type*) [CommSemiring R] : Ideal R :=
  (0 : Ideal R).radical
#align nilradical nilradical

structure that has zero and pow is reduced if it has no nonzero nilpotent elements. -/
@[mk_iff]
class IsReduced (R : Type*) [Zero R] [Pow R ℕ] : Prop where
  /-- A reduced structure has no nonzero nilpotent elements. -/
  eq_zero : ∀ x : R, IsNilpotent x → x = 0
#align is_reduced IsReduced