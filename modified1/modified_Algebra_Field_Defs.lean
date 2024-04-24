def Rat.castRec [NatCast K] [IntCast K] [Div K] (q : ℚ) : K := q.num / q.den
#align rat.cast_rec Rat.castRec

def qsmulRec (coe : ℚ → K) [Mul K] (a : ℚ) (x : K) : K :=
  coe a * x
#align qsmul_rec qsmulRec

def (q : ℚ) : (Rat.cast q : α) = q.num / q.den := by intros; rfl
  /-- Scalar multiplication by a rational number.

  Set this to `qsmulRec _` unless there is a risk of a `Module ℚ _` instance diamond.

  Do not use directly. Instead use the `•` notation. -/
  protected qsmul : ℚ → α → α
  /-- However `qsmul` is defined, it must be propositionally equal to multiplication by `Rat.cast`.

  Do not use this lemma directly. Use `Rat.cast_def` instead. -/
  protected qsmul_def (a : ℚ) (x : α) : qsmul a x = Rat.cast a * x := by intros; rfl
#align division_ring DivisionRing

def

-- see Note [lower instance priority]
instance (priority := 100) DivisionRing.toDivisionSemiring [DivisionRing α] : DivisionSemiring α :=
  { ‹DivisionRing α› with }
#align division_ring.to_division_semiring DivisionRing.toDivisionSemiring

def (q : ℚ) : (q : K) = q.num / q.den := DivisionRing.ratCast_def _
#align rat.cast_def Rat.cast_def

def _
#align rat.cast_mk' Rat.cast_mk'

def (a : ℚ) (x : K) : a • x = ↑a * x := DivisionRing.qsmul_def a x
#align rat.smul_def Rat.smul_def