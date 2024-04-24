def Basis.ofRankEqZero {ι : Type*} [IsEmpty ι] (hV : Module.rank K V = 0) : Basis ι K V :=
  haveI : Subsingleton V := rank_zero_iff.1 hV
  Basis.empty _
#align basis.of_rank_eq_zero Basis.ofRankEqZero

def basisOfTopLeSpanOfCardEqFinrank {ι : Type*} [Fintype ι] (b : ι → V)
    (le_span : ⊤ ≤ span K (Set.range b)) (card_eq : Fintype.card ι = finrank K V) : Basis ι K V :=
  Basis.mk (linearIndependent_of_top_le_span_of_card_eq_finrank le_span card_eq) le_span
#align basis_of_top_le_span_of_card_eq_finrank basisOfTopLeSpanOfCardEqFinrank

def finsetBasisOfTopLeSpanOfCardEqFinrank {s : Finset V}
    (le_span : ⊤ ≤ span K (s : Set V)) (card_eq : s.card = finrank K V) : Basis {x // x ∈ s} K V :=
  basisOfTopLeSpanOfCardEqFinrank ((↑) : ↥(s : Set V) → V)
    ((@Subtype.range_coe_subtype _ fun x => x ∈ s).symm ▸ le_span)
    (_root_.trans (Fintype.card_coe _) card_eq)
#align finset_basis_of_top_le_span_of_card_eq_finrank finsetBasisOfTopLeSpanOfCardEqFinrank

def setBasisOfTopLeSpanOfCardEqFinrank {s : Set V} [Fintype s]
    (le_span : ⊤ ≤ span K s) (card_eq : s.toFinset.card = finrank K V) : Basis s K V :=
  basisOfTopLeSpanOfCardEqFinrank ((↑) : s → V) ((@Subtype.range_coe_subtype _ s).symm ▸ le_span)
    (_root_.trans s.toFinset_card.symm card_eq)
#align set_basis_of_top_le_span_of_card_eq_finrank setBasisOfTopLeSpanOfCardEqFinrank