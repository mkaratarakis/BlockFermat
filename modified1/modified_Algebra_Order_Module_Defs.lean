def OrderIso.smulRight [PosSMulMono α β] [PosSMulReflectLE α β] {a : α} (ha : 0 < a) : β ≃o β where
  toEquiv := Equiv.smulRight ha.ne'
  map_rel_iff' := smul_le_smul_iff_of_pos_left ha
#align order_iso.smul_left OrderIso.smulRight

def OrderIso.smulRightDual (ha : a < 0) : β ≃o βᵒᵈ where
  toEquiv := (Equiv.smulRight ha.ne).trans toDual
  map_rel_iff' := (@OrderDual.toDual_le_toDual β).trans <| smul_le_smul_iff_of_neg_left ha
#align order_iso.smul_left_dual OrderIso.smulRightDual

def evalHSMul : PositivityExt where eval {_u α} zα pα (e : Q($α)) := do
  let .app (.app (.app (.app (.app (.app
        (.const ``HSMul.hSMul [u1, _, _]) (β : Q(Type u1))) _) _) _)
          (a : Q($β))) (b : Q($α)) ← whnfR e | throwError "failed to match hSMul"
  let zM : Q(Zero $β) ← synthInstanceQ q(Zero $β)
  let pM : Q(PartialOrder $β) ← synthInstanceQ q(PartialOrder $β)
  -- Using `q()` here would be impractical, as we would have to manually `synthInstanceQ` all the
  -- required typeclasses. Ideally we could tell `q()` to do this automatically.
  match ← core zM pM a, ← core zα pα b with
  | .positive pa, .positive pb =>
      pure (.positive (← mkAppM ``smul_pos #[pa, pb]))