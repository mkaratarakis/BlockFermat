def quotientRel : Setoid M :=
  QuotientAddGroup.leftRel p.toAddSubgroup
#align submodule.quotient_rel Submodule.quotientRel

def {x y : M} : @Setoid.r _ p.quotientRel x y ↔ x - y ∈ p :=
  Iff.trans
    (by
      rw [leftRel_apply, sub_eq_add_neg, neg_add, neg_neg]
      rfl)
    neg_mem_iff
#align submodule.quotient_rel_r_def Submodule.quotientRel_r_def

def mk {p : Submodule R M} : M → M ⧸ p :=
  Quotient.mk''
#align submodule.quotient.mk Submodule.Quotient.mk

def restrictScalarsEquiv [Ring S] [SMul S R] [Module S M] [IsScalarTower S R M]
    (P : Submodule R M) : (M ⧸ P.restrictScalars S) ≃ₗ[S] M ⧸ P :=
  { Quotient.congrRight fun _ _ => Iff.rfl with
    map_add' := fun x y => Quotient.inductionOn₂' x y fun _x' _y' => rfl
    map_smul' := fun _c x => Quotient.inductionOn' x fun _x' => rfl }
#align submodule.quotient.restrict_scalars_equiv Submodule.Quotient.restrictScalarsEquiv

def mkQ : M →ₗ[R] M ⧸ p where
  toFun := Quotient.mk
  map_add' := by simp
  map_smul' := by simp
#align submodule.mkq Submodule.mkQ

def liftQ (f : M →ₛₗ[τ₁₂] M₂) (h : p ≤ ker f) : M ⧸ p →ₛₗ[τ₁₂] M₂ :=
  { QuotientAddGroup.lift p.toAddSubgroup f.toAddMonoidHom h with
    map_smul' := by rintro a ⟨x⟩; exact f.map_smulₛₗ a x }
#align submodule.liftq Submodule.liftQ

def liftQSpanSingleton (x : M) (f : M →ₛₗ[τ₁₂] M₂) (h : f x = 0) : (M ⧸ R ∙ x) →ₛₗ[τ₁₂] M₂ :=
  (R ∙ x).liftQ f <| by rw [span_singleton_le_iff_mem, LinearMap.mem_ker, h]
#align submodule.liftq_span_singleton Submodule.liftQSpanSingleton

def mapQ (f : M →ₛₗ[τ₁₂] M₂) (h : p ≤ comap f q) : M ⧸ p →ₛₗ[τ₁₂] M₂ ⧸ q :=
  p.liftQ (q.mkQ.comp f) <| by simpa [ker_comp] using h
#align submodule.mapq Submodule.mapQ

def comapMkQRelIso : Submodule R (M ⧸ p) ≃o { p' : Submodule R M // p ≤ p' } where
  toFun p' := ⟨comap p.mkQ p', le_comap_mkQ p _⟩
  invFun q := map p.mkQ q
  left_inv p' := map_comap_eq_self <| by simp
  right_inv := fun ⟨q, hq⟩ => Subtype.ext_val <| by simpa [comap_map_mkQ p]
  map_rel_iff' := comap_le_comap_iff <| range_mkQ _
#align submodule.comap_mkq.rel_iso Submodule.comapMkQRelIso

def comapMkQOrderEmbedding : Submodule R (M ⧸ p) ↪o Submodule R M :=
  (RelIso.toRelEmbedding <| comapMkQRelIso p).trans (Subtype.relEmbedding (· ≤ ·) _)
#align submodule.comap_mkq.order_embedding Submodule.comapMkQOrderEmbedding

def Quotient.equiv {N : Type*} [AddCommGroup N] [Module R N] (P : Submodule R M)
    (Q : Submodule R N) (f : M ≃ₗ[R] N) (hf : P.map f = Q) : (M ⧸ P) ≃ₗ[R] N ⧸ Q :=
  { P.mapQ Q (f : M →ₗ[R] N) fun x hx => hf ▸ Submodule.mem_map_of_mem hx with
    toFun := P.mapQ Q (f : M →ₗ[R] N) fun x hx => hf ▸ Submodule.mem_map_of_mem hx
    invFun :=
      Q.mapQ P (f.symm : N →ₗ[R] M) fun x hx => by
        rw [← hf, Submodule.mem_map] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        simpa
    left_inv := fun x => Quotient.inductionOn' x (by simp)
    right_inv := fun x => Quotient.inductionOn' x (by simp) }
#align submodule.quotient.equiv Submodule.Quotient.equiv

def quotEquivOfEqBot (hp : p = ⊥) : (M ⧸ p) ≃ₗ[R] M :=
  LinearEquiv.ofLinear (p.liftQ id <| hp.symm ▸ bot_le) p.mkQ (liftQ_mkQ _ _ _) <|
    p.quot_hom_ext _ LinearMap.id fun _ => rfl
#align submodule.quot_equiv_of_eq_bot Submodule.quotEquivOfEqBot

def quotEquivOfEq (h : p = p') : (M ⧸ p) ≃ₗ[R] M ⧸ p' :=
  { @Quotient.congr _ _ (quotientRel p) (quotientRel p') (Equiv.refl _) fun a b => by
      subst h
      rfl with
    map_add' := by
      rintro ⟨x⟩ ⟨y⟩
      rfl
    map_smul' := by
      rintro x ⟨y⟩
      rfl }
#align submodule.quot_equiv_of_eq Submodule.quotEquivOfEq

def mapQLinear : compatibleMaps p q →ₗ[R] M ⧸ p →ₗ[R] M₂ ⧸ q
    where
  toFun f := mapQ _ _ f.val f.property
  map_add' x y := by
    ext
    rfl
  map_smul' c f := by
    ext
    rfl
#align submodule.mapq_linear Submodule.mapQLinear