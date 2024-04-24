def IsVonNBounded (s : Set E) : Prop :=
  ∀ ⦃V⦄, V ∈ 𝓝 (0 : E) → Absorbs 𝕜 V s
#align bornology.is_vonN_bounded Bornology.IsVonNBounded

def vonNBornology : Bornology E :=
  Bornology.ofBounded (setOf (IsVonNBounded 𝕜)) (isVonNBounded_empty 𝕜 E)
    (fun _ hs _ ht => hs.subset ht) (fun _ hs _ => hs.union) isVonNBounded_singleton
#align bornology.vonN_bornology Bornology.vonNBornology