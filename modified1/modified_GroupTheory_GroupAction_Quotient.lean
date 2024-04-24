def _root_.MulActionHom.toQuotient (H : Subgroup α) : α →[α] α ⧸ H where
  toFun := (↑); map_smul' := Quotient.smul_coe H
#align mul_action_hom.to_quotient MulActionHom.toQuotient

def ofQuotientStabilizer (g : α ⧸ MulAction.stabilizer α x) : β :=
  Quotient.liftOn' g (· • x) fun g1 g2 H =>
    calc
      g1 • x = g1 • (g1⁻¹ * g2) • x := congr_arg _ (leftRel_apply.mp H).symm
      _ = g2 • x := by rw [smul_smul, mul_inv_cancel_left]
#align mul_action.of_quotient_stabilizer MulAction.ofQuotientStabilizer

def orbitEquivQuotientStabilizer (b : β) : orbit α b ≃ α ⧸ stabilizer α b :=
  Equiv.symm <|
    Equiv.ofBijective (fun g => ⟨ofQuotientStabilizer α b g, ofQuotientStabilizer_mem_orbit α b g⟩)
      ⟨fun x y hxy => injective_ofQuotientStabilizer α b (by convert congr_arg Subtype.val hxy),
        fun ⟨b, ⟨g, hgb⟩⟩ => ⟨g, Subtype.eq hgb⟩⟩
#align mul_action.orbit_equiv_quotient_stabilizer MulAction.orbitEquivQuotientStabilizer

def orbitProdStabilizerEquivGroup (b : β) : orbit α b × stabilizer α b ≃ α :=
  (Equiv.prodCongr (orbitEquivQuotientStabilizer α _) (Equiv.refl _)).trans
    Subgroup.groupEquivQuotientProdSubgroup.symm
#align mul_action.orbit_prod_stabilizer_equiv_group MulAction.orbitProdStabilizerEquivGroup

def selfEquivSigmaOrbitsQuotientStabilizer' {φ : Ω → β}
    (hφ : LeftInverse Quotient.mk'' φ) : β ≃ Σω : Ω, α ⧸ stabilizer α (φ ω) :=
  calc
    β ≃ Σω : Ω, orbitRel.Quotient.orbit ω := selfEquivSigmaOrbits' α β
    _ ≃ Σω : Ω, α ⧸ stabilizer α (φ ω) :=
      Equiv.sigmaCongrRight fun ω =>
        (Equiv.Set.ofEq <| orbitRel.Quotient.orbit_eq_orbit_out _ hφ).trans <|
          orbitEquivQuotientStabilizer α (φ ω)
#align mul_action.self_equiv_sigma_orbits_quotient_stabilizer' MulAction.selfEquivSigmaOrbitsQuotientStabilizer'

def selfEquivSigmaOrbitsQuotientStabilizer : β ≃ Σω : Ω, α ⧸ stabilizer α ω.out' :=
  selfEquivSigmaOrbitsQuotientStabilizer' α β Quotient.out_eq'
#align mul_action.self_equiv_sigma_orbits_quotient_stabilizer MulAction.selfEquivSigmaOrbitsQuotientStabilizer

def sigmaFixedByEquivOrbitsProdGroup : (Σa : α, fixedBy β a) ≃ Ω × α :=
  calc
    (Σa : α, fixedBy β a) ≃ { ab : α × β // ab.1 • ab.2 = ab.2 } :=
      (Equiv.subtypeProdEquivSigmaSubtype _).symm
    _ ≃ { ba : β × α // ba.2 • ba.1 = ba.1 } := (Equiv.prodComm α β).subtypeEquiv fun _ => Iff.rfl
    _ ≃ Σb : β, stabilizer α b :=
      Equiv.subtypeProdEquivSigmaSubtype fun (b : β) a => a ∈ stabilizer α b
    _ ≃ Σωb : Σω : Ω, orbit α ω.out', stabilizer α (ωb.2 : β) :=
      (selfEquivSigmaOrbits α β).sigmaCongrLeft'
    _ ≃ Σω : Ω, Σb : orbit α ω.out', stabilizer α (b : β) :=
      Equiv.sigmaAssoc fun (ω : Ω) (b : orbit α ω.out') => stabilizer α (b : β)
    _ ≃ Σω : Ω, Σ _ : orbit α ω.out', stabilizer α ω.out' :=
      Equiv.sigmaCongrRight fun _ =>
        Equiv.sigmaCongrRight fun ⟨_, hb⟩ => (stabilizerEquivStabilizerOfOrbitRel hb).toEquiv
    _ ≃ Σω : Ω, orbit α ω.out' × stabilizer α ω.out' :=
      Equiv.sigmaCongrRight fun _ => Equiv.sigmaEquivProd _ _
    _ ≃ Σ _ : Ω, α := Equiv.sigmaCongrRight fun ω => orbitProdStabilizerEquivGroup α ω.out'
    _ ≃ Ω × α := Equiv.sigmaEquivProd Ω α
#align mul_action.sigma_fixed_by_equiv_orbits_prod_group MulAction.sigmaFixedByEquivOrbitsProdGroup

def quotientCentralizerEmbedding (g : G) :
    G ⧸ centralizer (zpowers (g : G)) ↪ commutatorSet G :=
  ((MulAction.orbitEquivQuotientStabilizer (ConjAct G) g).trans
            (quotientEquivOfEq (ConjAct.stabilizer_eq_centralizer g))).symm.toEmbedding.trans
    ⟨fun x =>
      ⟨x * g⁻¹,
        let ⟨_, x, rfl⟩ := x
        ⟨x, g, rfl⟩⟩,
      fun _ _ => Subtype.ext ∘ mul_right_cancel ∘ Subtype.ext_iff.mp⟩
#align subgroup.quotient_centralizer_embedding Subgroup.quotientCentralizerEmbedding

def quotientCenterEmbedding {S : Set G} (hS : closure S = ⊤) :
    G ⧸ center G ↪ S → commutatorSet G :=
  (quotientEquivOfEq (center_eq_infi' S hS)).toEmbedding.trans
    ((quotientiInfEmbedding _).trans
      (Function.Embedding.piCongrRight fun g => quotientCentralizerEmbedding (g : G)))
#align subgroup.quotient_center_embedding Subgroup.quotientCenterEmbedding