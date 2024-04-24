def rpow (x y : ℝ) :=
  ((x : ℂ) ^ (y : ℂ)).re
#align real.rpow Real.rpow

def (x y : ℝ) : x ^ y = ((x : ℂ) ^ (y : ℂ)).re := rfl
#align real.rpow_def Real.rpow_def

def evalRpowZero : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q($a ^ (0 : ℝ)) =>
    assertInstancesCommute
    pure (.positive q(Real.rpow_zero_pos $a))
  | _, _, _ => throwError "not Real.rpow"

/-- Extension for the `positivity` tactic: exponentiation by a real number is nonnegative when
the base is nonnegative and positive when the base is positive. -/
@[positivity (_ : ℝ) ^ (_ : ℝ)]
def evalRpow : PositivityExt where eval {u α} _zα _pα e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q($a ^ ($b : ℝ)) =>
    let ra ← core q(inferInstance) q(inferInstance) a
    assertInstancesCommute
    match ra with
    | .positive pa =>
        pure (.positive q(Real.rpow_pos_of_pos $pa $b))
    | .nonnegative pa =>
        pure (.nonnegative q(Real.rpow_nonneg $pa $b))
    | _ => pure .none
  | _, _, _ => throwError "not Real.rpow"

end Mathlib.Meta.Positivity

/-!
## Further algebraic properties of `rpow`

def evalRPow : NormNumExt where eval {u α} e := do
  let .app (.app f (a : Q(ℝ))) (b : Q(ℝ)) ← Lean.Meta.whnfR e | failure
  guard <|← withNewMCtxDepth <| isDefEq f q(HPow.hPow (α := ℝ) (β := ℝ))
  haveI' : u =QL 0 := ⟨⟩
  haveI' : $α =Q ℝ := ⟨⟩
  haveI' h : $e =Q $a ^ $b := ⟨⟩
  h.check
  let (rb : Result b) ← derive (α := q(ℝ)) b
  match rb with
  | .isBool .. | .isRat _ .. => failure
  | .isNat sβ nb pb =>
    match ← derive q($a ^ $nb) with
    | .isBool .. => failure
    | .isNat sα' ne' pe' =>
      assumeInstancesCommute
      haveI' : $sα' =Q AddGroupWithOne.toAddMonoidWithOne := ⟨⟩
      return .isNat sα' ne' q(isNat_rpow_pos $pb $pe')
    | .isNegNat sα' ne' pe' =>
      assumeInstancesCommute
      return .isNegNat sα' ne' q(isInt_rpow_pos $pb $pe')
    | .isRat sα' qe' nume' dene' pe' =>
      assumeInstancesCommute
      return .isRat sα' qe' nume' dene' q(isRat_rpow_pos $pb $pe')
  | .isNegNat sβ nb pb =>
    match ← derive q($a ^ (-($nb : ℤ))) with
    | .isBool .. => failure
    | .isNat sα' ne' pe' =>
      assumeInstancesCommute
      return .isNat sα' ne' q(isNat_rpow_neg $pb $pe')
    | .isNegNat sα' ne' pe' =>
      let _ := q(instRingReal)
      assumeInstancesCommute
      return .isNegNat sα' ne' q(isInt_rpow_neg $pb $pe')
    | .isRat sα' qe' nume' dene' pe' =>
      assumeInstancesCommute
      return .isRat sα' qe' nume' dene' q(isRat_rpow_neg $pb $pe')

end Mathlib.Meta.NormNum

end Tactics

/-!
### Deprecated lemmas