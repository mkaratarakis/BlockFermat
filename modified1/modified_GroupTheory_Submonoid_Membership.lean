def powers (n : M) : Submonoid M :=
  Submonoid.copy (mrange (powersHom M n)) (Set.range (n ^ · : ℕ → M)) <|
    Set.ext fun n => exists_congr fun i => by simp; rfl
#align submonoid.powers Submonoid.powers

def pow (n : M) (m : ℕ) : powers n :=
  (powersHom M n).mrangeRestrict (Multiplicative.ofAdd m)
#align submonoid.pow Submonoid.pow

def log [DecidableEq M] {n : M} (p : powers n) : ℕ :=
  Nat.find <| (mem_powers_iff p.val n).mp p.prop
#align submonoid.log Submonoid.log

def powLogEquiv [DecidableEq M] {n : M} (h : Function.Injective fun m : ℕ => n ^ m) :
    Multiplicative ℕ ≃* powers n where
  toFun m := pow n (Multiplicative.toAdd m)
  invFun m := Multiplicative.ofAdd (log m)
  left_inv := log_pow_eq_self h
  right_inv := pow_log_eq_self
  map_mul' _ _ := by simp only [pow, map_mul, ofAdd_add, toAdd_mul]
#align submonoid.pow_log_equiv Submonoid.powLogEquiv

def closureCommMonoidOfComm {s : Set M} (hcomm : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a) :
    CommMonoid (closure s) :=
  { (closure s).toMonoid with
    mul_comm := fun x y => by
      ext
      simp only [Submonoid.coe_mul]
      exact
        closure_induction₂ x.prop y.prop hcomm Commute.one_left Commute.one_right
          (fun x y z => Commute.mul_left) fun x y z => Commute.mul_right }
#align submonoid.closure_comm_monoid_of_comm Submonoid.closureCommMonoidOfComm

def multiples (x : A) : AddSubmonoid A :=
  AddSubmonoid.copy (AddMonoidHom.mrange (multiplesHom A x)) (Set.range (fun i => i • x : ℕ → A)) <|
    Set.ext fun n => exists_congr fun i => by simp
#align add_submonoid.multiples AddSubmonoid.multiples