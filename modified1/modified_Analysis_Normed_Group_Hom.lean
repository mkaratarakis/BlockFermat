def mkNormedAddGroupHom (f : V →+ W) (C : ℝ) (h : ∀ v, ‖f v‖ ≤ C * ‖v‖) : NormedAddGroupHom V W :=
  { f with bound' := ⟨C, h⟩ }
#align add_monoid_hom.mk_normed_add_group_hom AddMonoidHom.mkNormedAddGroupHom

def mkNormedAddGroupHom' (f : V →+ W) (C : ℝ≥0) (hC : ∀ x, ‖f x‖₊ ≤ C * ‖x‖₊) :
    NormedAddGroupHom V W :=
  { f with bound' := ⟨C, hC⟩ }
#align add_monoid_hom.mk_normed_add_group_hom' AddMonoidHom.mkNormedAddGroupHom'

def ofLipschitz (f : V₁ →+ V₂) {K : ℝ≥0} (h : LipschitzWith K f) : NormedAddGroupHom V₁ V₂ :=
  f.mkNormedAddGroupHom K fun x ↦ by simpa only [map_zero, dist_zero_right] using h.dist_le_mul x 0

instance funLike : FunLike (NormedAddGroupHom V₁ V₂) V₁ V₂ where
  coe := toFun
  coe_injective' := fun f g h => by cases f; cases g; congr

-- Porting note: moved this declaration up so we could get a `FunLike` instance sooner.
instance toAddMonoidHomClass : AddMonoidHomClass (NormedAddGroupHom V₁ V₂) V₁ V₂ where
  map_add f := f.map_add'
  map_zero f := (AddMonoidHom.mk' f.toFun f.map_add').map_zero

initialize_simps_projections NormedAddGroupHom (toFun → apply)

theorem coe_inj (H : (f : V₁ → V₂) = g) : f = g := by
  cases f; cases g; congr
#align normed_add_group_hom.coe_inj NormedAddGroupHom.coe_inj

def toAddMonoidHom (f : NormedAddGroupHom V₁ V₂) : V₁ →+ V₂ :=
  AddMonoidHom.mk' f f.map_add'
#align normed_add_group_hom.to_add_monoid_hom NormedAddGroupHom.toAddMonoidHom

def SurjectiveOnWith (f : NormedAddGroupHom V₁ V₂) (K : AddSubgroup V₂) (C : ℝ) : Prop :=
  ∀ h ∈ K, ∃ g, f g = h ∧ ‖g‖ ≤ C * ‖h‖
#align normed_add_group_hom.surjective_on_with NormedAddGroupHom.SurjectiveOnWith

def opNorm (f : NormedAddGroupHom V₁ V₂) :=
  sInf { c | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * ‖x‖ }
#align normed_add_group_hom.op_norm NormedAddGroupHom.opNorm

def : ‖f‖ = sInf { c | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * ‖x‖ } :=
  rfl
#align normed_add_group_hom.norm_def NormedAddGroupHom.norm_def

def id : NormedAddGroupHom V V :=
  (AddMonoidHom.id V).mkNormedAddGroupHom 1 (by simp [le_refl])
#align normed_add_group_hom.id NormedAddGroupHom.id

def coeAddHom : NormedAddGroupHom V₁ V₂ →+ V₁ → V₂ where
  toFun := DFunLike.coe
  map_zero' := coe_zero
  map_add' := coe_add
#align normed_add_group_hom.coe_fn_add_hom NormedAddGroupHom.coeAddHom

def comp (g : NormedAddGroupHom V₂ V₃) (f : NormedAddGroupHom V₁ V₂) :
    NormedAddGroupHom V₁ V₃ :=
  (g.toAddMonoidHom.comp f.toAddMonoidHom).mkNormedAddGroupHom (‖g‖ * ‖f‖) fun v =>
    calc
      ‖g (f v)‖ ≤ ‖g‖ * ‖f v‖ := le_opNorm _ _
      _ ≤ ‖g‖ * (‖f‖ * ‖v‖) := by gcongr; apply le_opNorm
      _ = ‖g‖ * ‖f‖ * ‖v‖ := by rw [mul_assoc]
#align normed_add_group_hom.comp NormedAddGroupHom.comp

def compHom : NormedAddGroupHom V₂ V₃ →+ NormedAddGroupHom V₁ V₂ →+ NormedAddGroupHom V₁ V₃ :=
  AddMonoidHom.mk'
    (fun g =>
      AddMonoidHom.mk' (fun f => g.comp f)
        (by
          intros
          ext
          exact map_add g _ _))
    (by
      intros
      ext
      simp only [comp_apply, Pi.add_apply, Function.comp_apply, AddMonoidHom.add_apply,
        AddMonoidHom.mk'_apply, coe_add])
#align normed_add_group_hom.comp_hom NormedAddGroupHom.compHom

def incl (s : AddSubgroup V) : NormedAddGroupHom s V where
  toFun := (Subtype.val : s → V)
  map_add' v w := AddSubgroup.coe_add _ _ _
  bound' := ⟨1, fun v => by rw [one_mul, AddSubgroup.coe_norm]⟩
#align normed_add_group_hom.incl NormedAddGroupHom.incl

def ker : AddSubgroup V₁ :=
  f.toAddMonoidHom.ker
#align normed_add_group_hom.ker NormedAddGroupHom.ker

def ker.lift (h : g.comp f = 0) : NormedAddGroupHom V₁ g.ker where
  toFun v := ⟨f v, by rw [g.mem_ker, ← comp_apply g f, h, zero_apply]⟩
  map_add' v w := by simp only [map_add, AddSubmonoid.mk_add_mk]
  bound' := f.bound'
#align normed_add_group_hom.ker.lift NormedAddGroupHom.ker.lift

def range : AddSubgroup V₂ :=
  f.toAddMonoidHom.range
#align normed_add_group_hom.range NormedAddGroupHom.range

def NormNoninc (f : NormedAddGroupHom V W) : Prop :=
  ∀ v, ‖f v‖ ≤ ‖v‖
#align normed_add_group_hom.norm_noninc NormedAddGroupHom.NormNoninc

def equalizer :=
  (f - g).ker
#align normed_add_group_hom.equalizer NormedAddGroupHom.equalizer

def ι : NormedAddGroupHom (f.equalizer g) V :=
  incl _
#align normed_add_group_hom.equalizer.ι NormedAddGroupHom.Equalizer.ι

def lift (φ : NormedAddGroupHom V₁ V) (h : f.comp φ = g.comp φ) :
    NormedAddGroupHom V₁ (f.equalizer g)
    where
  toFun v :=
    ⟨φ v,
      show (f - g) (φ v) = 0 by
        rw [NormedAddGroupHom.sub_apply, sub_eq_zero, ← comp_apply, h, comp_apply]⟩
  map_add' v₁ v₂ := by
    ext
    simp only [map_add, AddSubgroup.coe_add, Subtype.coe_mk]
  bound' := by
    obtain ⟨C, _C_pos, hC⟩ := φ.bound
    exact ⟨C, hC⟩
#align normed_add_group_hom.equalizer.lift NormedAddGroupHom.Equalizer.lift

def liftEquiv :
    { φ : NormedAddGroupHom V₁ V // f.comp φ = g.comp φ } ≃ NormedAddGroupHom V₁ (f.equalizer g)
    where
  toFun φ := lift φ φ.prop
  invFun ψ := ⟨(ι f g).comp ψ, by rw [← comp_assoc, ← comp_assoc, comp_ι_eq]⟩
  left_inv φ := by simp
  right_inv ψ := by
    ext
    rfl
#align normed_add_group_hom.equalizer.lift_equiv NormedAddGroupHom.Equalizer.liftEquiv

def map (φ : NormedAddGroupHom V₁ V₂) (ψ : NormedAddGroupHom W₁ W₂) (hf : ψ.comp f₁ = f₂.comp φ)
    (hg : ψ.comp g₁ = g₂.comp φ) : NormedAddGroupHom (f₁.equalizer g₁) (f₂.equalizer g₂) :=
  lift (φ.comp <| ι _ _) <| by
    simp only [← comp_assoc, ← hf, ← hg]
    simp only [comp_assoc, comp_ι_eq f₁ g₁]
#align normed_add_group_hom.equalizer.map NormedAddGroupHom.Equalizer.map

structure and a norm, giving rise to a normed group structure. We provide several
simple constructions for normed group homs, like kernel, range and equalizer.

Some easy other constructions are related to subgroups of normed groups.

Since a lot of elementary properties don't require `‖x‖ = 0 → x = 0` we start setting up the
theory of `SeminormedAddGroupHom` and we specialize to `NormedAddGroupHom` when needed.
-/


noncomputable section

open NNReal BigOperators

-- TODO: migrate to the new morphism / morphism_class style
/-- A morphism of seminormed abelian groups is a bounded group homomorphism. -/
structure NormedAddGroupHom (V W : Type*) [SeminormedAddCommGroup V]
  [SeminormedAddCommGroup W] where
  /-- The function underlying a `NormedAddGroupHom` -/
  toFun : V → W
  /-- A `NormedAddGroupHom` is additive. -/
  map_add' : ∀ v₁ v₂, toFun (v₁ + v₂) = toFun v₁ + toFun v₂
  /-- A `NormedAddGroupHom` is bounded. -/
  bound' : ∃ C, ∀ v, ‖toFun v‖ ≤ C * ‖v‖
#align normed_add_group_hom NormedAddGroupHom

structure on normed group homs -/


/-- Homs between two given normed groups form a commutative additive group. -/
instance toAddCommGroup : AddCommGroup (NormedAddGroupHom V₁ V₂) :=
  coe_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    fun _ _ => rfl

/-- Normed group homomorphisms themselves form a seminormed group with respect to
    the operator norm. -/
instance toSeminormedAddCommGroup : SeminormedAddCommGroup (NormedAddGroupHom V₁ V₂) :=
  AddGroupSeminorm.toSeminormedAddCommGroup
    { toFun := opNorm
      map_zero' := opNorm_zero
      neg' := opNorm_neg
      add_le' := opNorm_add_le }
#align normed_add_group_hom.to_seminormed_add_comm_group NormedAddGroupHom.toSeminormedAddCommGroup

structure on normed group homs -/


instance distribMulAction {R : Type*} [MonoidWithZero R] [DistribMulAction R V₂]
    [PseudoMetricSpace R] [BoundedSMul R V₂] : DistribMulAction R (NormedAddGroupHom V₁ V₂) :=
  Function.Injective.distribMulAction coeAddHom coe_injective coe_smul

instance module {R : Type*} [Semiring R] [Module R V₂] [PseudoMetricSpace R] [BoundedSMul R V₂] :
    Module R (NormedAddGroupHom V₁ V₂) :=
  Function.Injective.module _ coeAddHom coe_injective coe_smul

/-! ### Composition of normed group homs -/