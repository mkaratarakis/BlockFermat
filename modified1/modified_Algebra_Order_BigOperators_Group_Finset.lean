def evalFinsetSum : PositivityExt where eval {u α} zα pα e := do
  match e with
  | ~q(@Finset.sum $ι _ $instα $s $f) =>
    let i : Q($ι) ← mkFreshExprMVarQ q($ι) .syntheticOpaque
    have body : Q($α) := .betaRev f #[i]