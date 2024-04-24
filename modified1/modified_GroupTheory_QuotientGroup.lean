def con : Con G where
  toSetoid := leftRel N
  mul' := @fun a b c d hab hcd => by
    rw [leftRel_eq] at hab hcd ⊢
    dsimp only
    calc
      (a * c)⁻¹ * (b * d) = c⁻¹ * (a⁻¹ * b) * c⁻¹⁻¹ * (c⁻¹ * d) :=
        by simp only [mul_inv_rev, mul_assoc, inv_mul_cancel_left]
      _ ∈ N := N.mul_mem (nN.conj_mem _ hab _) hcd
#align quotient_group.con QuotientGroup.con

def mk' : G →* G ⧸ N :=
  MonoidHom.mk' QuotientGroup.mk fun _ _ => rfl
#align quotient_group.mk' QuotientGroup.mk'

def lift (φ : G →* M) (HN : N ≤ φ.ker) : Q →* M :=
  (QuotientGroup.con N).lift φ fun x y h => by
    simp only [QuotientGroup.con, leftRel_apply, Con.rel_mk] at h
    rw [Con.ker_rel]
    calc
      φ x = φ (y * (x⁻¹ * y)⁻¹) := by rw [mul_inv_rev, inv_inv, mul_inv_cancel_left]
      _ = φ y := by rw [φ.map_mul, HN (N.inv_mem h), mul_one]
#align quotient_group.lift QuotientGroup.lift

def map (M : Subgroup H) [M.Normal] (f : G →* H) (h : N ≤ M.comap f) : G ⧸ N →* H ⧸ M := by
  refine' QuotientGroup.lift N ((mk' M).comp f) _
  intro x hx
  refine' QuotientGroup.eq.2 _
  rw [mul_one, Subgroup.inv_mem_iff]
  exact h hx
#align quotient_group.map QuotientGroup.map

def congr (e : G ≃* H) (he : G'.map e = H') : G ⧸ G' ≃* H ⧸ H' :=
  { map G' H' e (he ▸ G'.le_comap_map (e : G →* H)) with
    toFun := map G' H' e (he ▸ G'.le_comap_map (e : G →* H))
    invFun := map H' G' e.symm (he ▸ (G'.map_equiv_eq_comap_symm e).le)
    left_inv := fun x => by
      rw [map_map G' H' G' e e.symm (he ▸ G'.le_comap_map (e : G →* H))
        (he ▸ (G'.map_equiv_eq_comap_symm e).le)]
      simp only [map_map, ← MulEquiv.coe_monoidHom_trans, MulEquiv.self_trans_symm,
        MulEquiv.coe_monoidHom_refl, map_id_apply]
    right_inv := fun x => by
      rw [map_map H' G' H' e.symm e (he ▸ (G'.map_equiv_eq_comap_symm e).le)
        (he ▸ G'.le_comap_map (e : G →* H)) ]
      simp only [← MulEquiv.coe_monoidHom_trans, MulEquiv.symm_trans_self,
        MulEquiv.coe_monoidHom_refl, map_id_apply] }
#align quotient_group.congr QuotientGroup.congr

def kerLift : G ⧸ ker φ →* H :=
  lift _ φ fun _g => φ.mem_ker.mp
#align quotient_group.ker_lift QuotientGroup.kerLift

def rangeKerLift : G ⧸ ker φ →* φ.range :=
  lift _ φ.rangeRestrict fun g hg => (mem_ker _).mp <| by rwa [ker_rangeRestrict]
#align quotient_group.range_ker_lift QuotientGroup.rangeKerLift

def quotientKerEquivRange : G ⧸ ker φ ≃* range φ :=
  MulEquiv.ofBijective (rangeKerLift φ) ⟨rangeKerLift_injective φ, rangeKerLift_surjective φ⟩
#align quotient_group.quotient_ker_equiv_range QuotientGroup.quotientKerEquivRange

def quotientKerEquivOfRightInverse (ψ : H → G) (hφ : RightInverse ψ φ) : G ⧸ ker φ ≃* H :=
  { kerLift φ with
    toFun := kerLift φ
    invFun := mk ∘ ψ
    left_inv := fun x => kerLift_injective φ (by rw [Function.comp_apply, kerLift_mk', hφ])
    right_inv := hφ }
#align quotient_group.quotient_ker_equiv_of_right_inverse QuotientGroup.quotientKerEquivOfRightInverse

def quotientBot : G ⧸ (⊥ : Subgroup G) ≃* G :=
  quotientKerEquivOfRightInverse (MonoidHom.id G) id fun _x => rfl
#align quotient_group.quotient_bot QuotientGroup.quotientBot

def quotientKerEquivOfSurjective (hφ : Surjective φ) : G ⧸ ker φ ≃* H :=
  quotientKerEquivOfRightInverse φ _ hφ.hasRightInverse.choose_spec
#align quotient_group.quotient_ker_equiv_of_surjective QuotientGroup.quotientKerEquivOfSurjective

def quotientMulEquivOfEq {M N : Subgroup G} [M.Normal] [N.Normal] (h : M = N) : G ⧸ M ≃* G ⧸ N :=
  { Subgroup.quotientEquivOfEq h with
    map_mul' := fun q r => Quotient.inductionOn₂' q r fun _g _h => rfl }
#align quotient_group.quotient_mul_equiv_of_eq QuotientGroup.quotientMulEquivOfEq

def quotientMapSubgroupOfOfLe {A' A B' B : Subgroup G} [_hAN : (A'.subgroupOf A).Normal]
    [_hBN : (B'.subgroupOf B).Normal] (h' : A' ≤ B') (h : A ≤ B) :
    A ⧸ A'.subgroupOf A →* B ⧸ B'.subgroupOf B :=
  map _ _ (Subgroup.inclusion h) <| Subgroup.comap_mono h'
#align quotient_group.quotient_map_subgroup_of_of_le QuotientGroup.quotientMapSubgroupOfOfLe

def equivQuotientSubgroupOfOfEq {A' A B' B : Subgroup G} [hAN : (A'.subgroupOf A).Normal]
    [hBN : (B'.subgroupOf B).Normal] (h' : A' = B') (h : A = B) :
    A ⧸ A'.subgroupOf A ≃* B ⧸ B'.subgroupOf B :=
  MonoidHom.toMulEquiv (quotientMapSubgroupOfOfLe h'.le h.le) (quotientMapSubgroupOfOfLe h'.ge h.ge)
    (by ext ⟨x, hx⟩; rfl)
    (by ext ⟨x, hx⟩; rfl)
#align quotient_group.equiv_quotient_subgroup_of_of_eq QuotientGroup.equivQuotientSubgroupOfOfEq

def homQuotientZPowOfHom :
    A ⧸ (zpowGroupHom n : A →* A).range →* B ⧸ (zpowGroupHom n : B →* B).range :=
  lift _ ((mk' _).comp f) fun g ⟨h, (hg : h ^ n = g)⟩ =>
    (eq_one_iff _).mpr ⟨f h, by
      simp only [← hg, map_zpow, zpowGroupHom_apply]⟩
#align quotient_group.hom_quotient_zpow_of_hom QuotientGroup.homQuotientZPowOfHom

def equivQuotientZPowOfEquiv :
    A ⧸ (zpowGroupHom n : A →* A).range ≃* B ⧸ (zpowGroupHom n : B →* B).range :=
  MonoidHom.toMulEquiv _ _
    (homQuotientZPowOfHom_comp_of_rightInverse (e.symm : B →* A) (e : A →* B) n e.left_inv)
    (homQuotientZPowOfHom_comp_of_rightInverse (e : A →* B) (e.symm : B →* A) n e.right_inv)
    -- Porting note: had to explicitly coerce the `MulEquiv`s to `MonoidHom`s
#align quotient_group.equiv_quotient_zpow_of_equiv QuotientGroup.equivQuotientZPowOfEquiv

def quotientInfEquivProdNormalQuotient (H N : Subgroup G) [N.Normal] :
    H ⧸ N.subgroupOf H ≃* _ ⧸ N.subgroupOf (H ⊔ N) :=
  let
    φ :-- φ is the natural homomorphism H →* (HN)/N.
      H →*
      _ ⧸ N.subgroupOf (H ⊔ N) :=
    (mk' <| N.subgroupOf (H ⊔ N)).comp (inclusion le_sup_left)
  have φ_surjective : Surjective φ := fun x =>
    x.inductionOn' <| by
      rintro ⟨y, hy : y ∈ (H ⊔ N)⟩;
      rw [← SetLike.mem_coe] at hy
      rw [mul_normal H N] at hy
      rcases hy with ⟨h, hh, n, hn, rfl⟩
      use ⟨h, hh⟩
      let _ : Setoid ↑(H ⊔ N) :=
        (@leftRel ↑(H ⊔ N) (H ⊔ N : Subgroup G).toGroup (N.subgroupOf (H ⊔ N)))
      -- Porting note: Lean couldn't find this automatically
      refine Quotient.eq.mpr ?_
      change Setoid.r _ _
      rw [leftRel_apply]
      change h⁻¹ * (h * n) ∈ N
      rwa [← mul_assoc, inv_mul_self, one_mul]
  (quotientMulEquivOfEq (by simp [φ, ← comap_ker])).trans
    (quotientKerEquivOfSurjective φ φ_surjective)
#align quotient_group.quotient_inf_equiv_prod_normal_quotient QuotientGroup.quotientInfEquivProdNormalQuotient

def quotientQuotientEquivQuotientAux : (G ⧸ N) ⧸ M.map (mk' N) →* G ⧸ M :=
  lift (M.map (mk' N)) (map N M (MonoidHom.id G) h)
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [mem_ker, map_mk' N M _ _ x]
      exact (QuotientGroup.eq_one_iff _).mpr hx)
#align quotient_group.quotient_quotient_equiv_quotient_aux QuotientGroup.quotientQuotientEquivQuotientAux

def quotientQuotientEquivQuotient : (G ⧸ N) ⧸ M.map (QuotientGroup.mk' N) ≃* G ⧸ M :=
  MonoidHom.toMulEquiv (quotientQuotientEquivQuotientAux N M h)
    (QuotientGroup.map _ _ (QuotientGroup.mk' N) (Subgroup.le_comap_map _ _))
    (by ext; simp)
    (by ext; simp)
#align quotient_group.quotient_quotient_equiv_quotient QuotientGroup.quotientQuotientEquivQuotient

def fintypeOfKerLeRange (h : g.ker ≤ f.range) : Fintype G :=
  @Fintype.ofEquiv _ _
    (@instFintypeProd _ _ (Fintype.ofInjective _ <| kerLift_injective g) <|
      Fintype.ofInjective _ <| inclusion_injective h)
    groupEquivQuotientProdSubgroup.symm
#align group.fintype_of_ker_le_range Group.fintypeOfKerLeRange

def fintypeOfKerEqRange (h : g.ker = f.range) : Fintype G :=
  fintypeOfKerLeRange _ _ h.le
#align group.fintype_of_ker_eq_range Group.fintypeOfKerEqRange

def fintypeOfKerOfCodom [Fintype g.ker] : Fintype G :=
  fintypeOfKerLeRange ((topEquiv : _ ≃* G).toMonoidHom.comp <| inclusion le_top) g fun x hx =>
    ⟨⟨x, hx⟩, rfl⟩
#align group.fintype_of_ker_of_codom Group.fintypeOfKerOfCodom

def fintypeOfDomOfCoker [Normal f.range] [Fintype <| G ⧸ f.range] : Fintype G :=
  fintypeOfKerLeRange _ (mk' f.range) fun x => (eq_one_iff x).mp
#align group.fintype_of_dom_of_coker Group.fintypeOfDomOfCoker