def PadicSeq (p : ℕ) :=
  CauSeq _ (padicNorm p)
#align padic_seq PadicSeq

def stationaryPoint {f : PadicSeq p} (hf : ¬f ≈ 0) : ℕ :=
  Classical.choose <| stationary hf
#align padic_seq.stationary_point PadicSeq.stationaryPoint

def norm (f : PadicSeq p) : ℚ :=
  if hf : f ≈ 0 then 0 else padicNorm p (f (stationaryPoint hf))
#align padic_seq.norm PadicSeq.norm

def valuation (f : PadicSeq p) : ℤ :=
  if hf : f ≈ 0 then 0 else padicValRat p (f (stationaryPoint hf))
#align padic_seq.valuation PadicSeq.valuation

def index_simp_core (hh hf hg : expr)
    (at_ : Interactive.Loc := Interactive.Loc.ns [none]) : tactic Unit := do
  let [v1, v2, v3] ← [hh, hf, hg].mapM fun n => tactic.mk_app `` stationary_point [n] <|> return n
  let e1 ← tactic.mk_app `` lift_index_left_left [hh, v2, v3] <|> return q(True)
  let e2 ← tactic.mk_app `` lift_index_left [hf, v1, v3] <|> return q(True)
  let e3 ← tactic.mk_app `` lift_index_right [hg, v1, v2] <|> return q(True)
  let sl ← [e1, e2, e3].foldlM (fun s e => simp_lemmas.add s e) simp_lemmas.mk
  when at_ (tactic.simp_target sl >> tactic.skip)
  let hs ← at_.get_locals
  hs (tactic.simp_hyp sl [])
#align index_simp_core index_simp_core

def tactic.interactive.padic_index_simp (l : interactive.parse interactive.types.pexpr_list)
    (at_ : interactive.parse interactive.types.location) : tactic Unit := do
  let [h, f, g] ← l.mapM tactic.i_to_expr
  index_simp_core h f g at_
#align tactic.interactive.padic_index_simp tactic.interactive.padic_index_simp

def Padic (p : ℕ) [Fact p.Prime] :=
  CauSeq.Completion.Cauchy (padicNorm p)
#align padic Padic

def mk : PadicSeq p → ℚ_[p] :=
  Quotient.mk'
#align padic.mk Padic.mk

def : (0 : ℚ_[p]) = ⟦0⟧ := rfl
#align padic.zero_def Padic.zero_def

def padicNormE {p : ℕ} [hp : Fact p.Prime] : AbsoluteValue ℚ_[p] ℚ where
  toFun := Quotient.lift PadicSeq.norm <| @PadicSeq.norm_equiv _ _
  map_mul' q r := Quotient.inductionOn₂ q r <| PadicSeq.norm_mul
  nonneg' q := Quotient.inductionOn q <| PadicSeq.norm_nonneg
  eq_zero' q := Quotient.inductionOn q fun r ↦ by
    rw [Padic.zero_def, Quotient.eq]
    exact PadicSeq.norm_zero_iff r
  add_le' q r := by
    trans
      max ((Quotient.lift PadicSeq.norm <| @PadicSeq.norm_equiv _ _) q)
        ((Quotient.lift PadicSeq.norm <| @PadicSeq.norm_equiv _ _) r)
    exact Quotient.inductionOn₂ q r <| PadicSeq.norm_nonarchimedean
    refine' max_le_add_of_nonneg (Quotient.inductionOn q <| PadicSeq.norm_nonneg) _
    exact Quotient.inductionOn r <| PadicSeq.norm_nonneg
#align padic_norm_e padicNormE

def limSeq : ℕ → ℚ :=
  fun n ↦ Classical.choose (rat_dense' (f n) (div_nat_pos n))
#align padic.lim_seq Padic.limSeq

def lim' : PadicSeq p :=
  ⟨_, exi_rat_seq_conv_cauchy f⟩

private def lim : ℚ_[p] :=
  ⟦lim' f⟧

theorem complete' : ∃ q : ℚ_[p], ∀ ε > 0, ∃ N, ∀ i ≥ N, padicNormE (q - f i : ℚ_[p]) < ε :=
  ⟨lim f, fun ε hε ↦ by
    obtain ⟨N, hN⟩ := exi_rat_seq_conv f (half_pos hε)
    obtain ⟨N2, hN2⟩ := padicNormE.defn (lim' f) (half_pos hε)
    refine' ⟨max N N2, fun i hi ↦ _⟩
    rw [← sub_add_sub_cancel _ (lim' f i : ℚ_[p]) _]
    refine' (padicNormE.add_le _ _).trans_lt _
    rw [← add_halves ε]
    apply _root_.add_lt_add
    · apply hN2 _ (le_of_max_le_right hi)
    · rw [padicNormE.map_sub]
      exact hN _ (le_of_max_le_left hi)⟩
#align padic.complete' Padic.complete'

def ratNorm (q : ℚ_[p]) : ℚ :=
  Classical.choose (padicNormE.is_rat q)
#align padic_norm_e.rat_norm padicNormE.ratNorm

def valuation : ℚ_[p] → ℤ :=
  Quotient.lift (@PadicSeq.valuation p _) fun f g h ↦ by
    by_cases hf : f ≈ 0
    · have hg : g ≈ 0 := Setoid.trans (Setoid.symm h) hf
      simp [hf, hg, PadicSeq.valuation]
    · have hg : ¬g ≈ 0 := fun hg ↦ hf (Setoid.trans h hg)
      rw [PadicSeq.val_eq_iff_norm_eq hf hg]
      exact PadicSeq.norm_equiv h
#align padic.valuation Padic.valuation

def addValuationDef : ℚ_[p] → WithTop ℤ :=
  fun x ↦ if x = 0 then ⊤ else x.valuation
#align padic.add_valuation_def Padic.addValuationDef

def addValuation : AddValuation ℚ_[p] (WithTop ℤ) :=
  AddValuation.of addValuationDef AddValuation.map_zero AddValuation.map_one AddValuation.map_add
    AddValuation.map_mul
#align padic.add_valuation Padic.addValuation

structure from this construction.
The extension of the norm on `ℚ` to `ℚ_[p]` is *not* analogous to extending the absolute value to
`ℝ` and hence the proof that `ℚ_[p]` is complete is different from the proof that ℝ is complete.

A small special-purpose simplification tactic, `padic_index_simp`, is used to manipulate sequence
indices in the proof that the norm extends.

`padicNormE` is the rational-valued `p`-adic norm on `ℚ_[p]`.
To instantiate `ℚ_[p]` as a normed field, we must cast this into an `ℝ`-valued norm.
The `ℝ`-valued norm, using notation `‖ ‖` from normed spaces,
is the canonical representation of this norm.

`simp` prefers `padicNorm` to `padicNormE` when possible.
Since `padicNormE` and `‖ ‖` have different types, `simp` does not rewrite one to the other.

Coercions from `ℚ` to `ℚ_[p]` are set up to work with the `norm_cast` tactic.

## References