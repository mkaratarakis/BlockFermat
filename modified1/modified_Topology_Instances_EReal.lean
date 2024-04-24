def neBotTopHomeomorphReal : ({⊥, ⊤}ᶜ : Set EReal) ≃ₜ ℝ where
  toEquiv := neTopBotEquivReal
  continuous_toFun := continuousOn_iff_continuous_restrict.1 continuousOn_toReal
  continuous_invFun := continuous_coe_real_ereal.subtype_mk _
#align ereal.ne_bot_top_homeomorph_real EReal.neBotTopHomeomorphReal

def negHomeo : EReal ≃ₜ EReal :=
  negOrderIso.toHomeomorph
#align ereal.neg_homeo EReal.negHomeo

structure on `EReal`

We endow `EReal` with the order topology, and prove basic properties of this topology.

## Main results