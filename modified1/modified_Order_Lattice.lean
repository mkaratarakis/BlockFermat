def exactSubsetOfSSubset : Mathlib.Tactic.GCongr.ForwardExt where
  eval h goal := do goal.assignIfDefeq (← Lean.Meta.mkAppM ``subset_of_ssubset #[h])

def SemilatticeSup.mk' {α : Type*} [Sup α] (sup_comm : ∀ a b : α, a ⊔ b = b ⊔ a)
    (sup_assoc : ∀ a b c : α, a ⊔ b ⊔ c = a ⊔ (b ⊔ c)) (sup_idem : ∀ a : α, a ⊔ a = a) :
    SemilatticeSup α where
  sup := (· ⊔ ·)
  le a b := a ⊔ b = b
  le_refl := sup_idem
  le_trans a b c hab hbc := by dsimp; rw [← hbc, ← sup_assoc, hab]
  le_antisymm a b hab hba := by rwa [← hba, sup_comm]
  le_sup_left a b := by dsimp; rw [← sup_assoc, sup_idem]
  le_sup_right a b := by dsimp; rw [sup_comm, sup_assoc, sup_idem]
  sup_le a b c hac hbc := by dsimp; rwa [sup_assoc, hbc]
#align semilattice_sup.mk' SemilatticeSup.mk'

def SemilatticeInf.mk' {α : Type*} [Inf α] (inf_comm : ∀ a b : α, a ⊓ b = b ⊓ a)
    (inf_assoc : ∀ a b c : α, a ⊓ b ⊓ c = a ⊓ (b ⊓ c)) (inf_idem : ∀ a : α, a ⊓ a = a) :
    SemilatticeInf α := by
  haveI : SemilatticeSup αᵒᵈ := SemilatticeSup.mk' inf_comm inf_assoc inf_idem
  haveI i := OrderDual.instSemilatticeInf αᵒᵈ
  exact i
#align semilattice_inf.mk' SemilatticeInf.mk'

def Lattice.mk' {α : Type*} [Sup α] [Inf α] (sup_comm : ∀ a b : α, a ⊔ b = b ⊔ a)
    (sup_assoc : ∀ a b c : α, a ⊔ b ⊔ c = a ⊔ (b ⊔ c)) (inf_comm : ∀ a b : α, a ⊓ b = b ⊓ a)
    (inf_assoc : ∀ a b c : α, a ⊓ b ⊓ c = a ⊓ (b ⊓ c)) (sup_inf_self : ∀ a b : α, a ⊔ a ⊓ b = a)
    (inf_sup_self : ∀ a b : α, a ⊓ (a ⊔ b) = a) : Lattice α :=
  have sup_idem : ∀ b : α, b ⊔ b = b := fun b =>
    calc
      b ⊔ b = b ⊔ b ⊓ (b ⊔ b) := by rw [inf_sup_self]
      _ = b := by rw [sup_inf_self]

  have inf_idem : ∀ b : α, b ⊓ b = b := fun b =>
    calc
      b ⊓ b = b ⊓ (b ⊔ b ⊓ b) := by rw [sup_inf_self]
      _ = b := by rw [inf_sup_self]

  let semilatt_inf_inst := SemilatticeInf.mk' inf_comm inf_assoc inf_idem
  let semilatt_sup_inst := SemilatticeSup.mk' sup_comm sup_assoc sup_idem
  have partial_order_eq : @SemilatticeSup.toPartialOrder _ semilatt_sup_inst =
                          @SemilatticeInf.toPartialOrder _ semilatt_inf_inst :=
    semilatticeSup_mk'_partialOrder_eq_semilatticeInf_mk'_partialOrder _ _ _ _ _ _
      sup_inf_self inf_sup_self
  { semilatt_sup_inst, semilatt_inf_inst with
    inf_le_left := fun a b => by
      rw [partial_order_eq]
      apply inf_le_left,
    inf_le_right := fun a b => by
      rw [partial_order_eq]
      apply inf_le_right,
    le_inf := fun a b c => by
      rw [partial_order_eq]
      apply le_inf }
#align lattice.mk' Lattice.mk'

def DistribLattice.ofInfSupLe [Lattice α] (inf_sup_le : ∀ a b c : α, a ⊓ (b ⊔ c) ≤ a ⊓ b ⊔ a ⊓ c) :
    DistribLattice α where
  le_sup_inf := (@OrderDual.instDistribLattice αᵒᵈ {inferInstanceAs (Lattice αᵒᵈ) with
      le_sup_inf := inf_sup_le}).le_sup_inf
#align distrib_lattice.of_inf_sup_le DistribLattice.ofInfSupLe

def Lattice.toLinearOrder (α : Type u) [Lattice α] [DecidableEq α]
    [DecidableRel ((· ≤ ·) : α → α → Prop)]
    [DecidableRel ((· < ·) : α → α → Prop)] [IsTotal α (· ≤ ·)] : LinearOrder α where
  __ := ‹Lattice α›
  decidableLE := ‹_›
  decidableEq := ‹_›
  decidableLT := ‹_›
  le_total := total_of (· ≤ ·)
  max := (· ⊔ ·)
  max_def := by exact congr_fun₂ sup_eq_maxDefault
  min := (· ⊓ ·)
  min_def := by exact congr_fun₂ inf_eq_minDefault
#align lattice.to_linear_order Lattice.toLinearOrder

def [∀ i, Sup (α' i)] (f g : ∀ i, α' i) : f ⊔ g = fun i => f i ⊔ g i :=
  rfl
#align pi.sup_def Pi.sup_def

def [∀ i, Inf (α' i)] (f g : ∀ i, α' i) : f ⊓ g = fun i => f i ⊓ g i :=
  rfl
#align pi.inf_def Pi.inf_def

def [Sup α] [Sup β] (p q : α × β) : p ⊔ q = (p.fst ⊔ q.fst, p.snd ⊔ q.snd) :=
  rfl
#align prod.sup_def Prod.sup_def

def [Inf α] [Inf β] (p q : α × β) : p ⊓ q = (p.fst ⊓ q.fst, p.snd ⊓ q.snd) :=
  rfl
#align prod.inf_def Prod.inf_def

def semilatticeSup [SemilatticeSup α] {P : α → Prop}
    (Psup : ∀ ⦃x y⦄, P x → P y → P (x ⊔ y)) :
    SemilatticeSup { x : α // P x } where
  sup x y := ⟨x.1 ⊔ y.1, Psup x.2 y.2⟩
  le_sup_left _ _ := le_sup_left
  le_sup_right _ _ := le_sup_right
  sup_le _ _ _ h1 h2 := sup_le h1 h2
#align subtype.semilattice_sup Subtype.semilatticeSup

def semilatticeInf [SemilatticeInf α] {P : α → Prop}
    (Pinf : ∀ ⦃x y⦄, P x → P y → P (x ⊓ y)) :
    SemilatticeInf { x : α // P x } where
  inf x y := ⟨x.1 ⊓ y.1, Pinf x.2 y.2⟩
  inf_le_left _ _ := inf_le_left
  inf_le_right _ _ := inf_le_right
  le_inf _ _ _ h1 h2 := le_inf h1 h2
#align subtype.semilattice_inf Subtype.semilatticeInf

def lattice [Lattice α] {P : α → Prop} (Psup : ∀ ⦃x y⦄, P x → P y → P (x ⊔ y))
    (Pinf : ∀ ⦃x y⦄, P x → P y → P (x ⊓ y)) : Lattice { x : α // P x } where
  __ := Subtype.semilatticeInf Pinf
  __ := Subtype.semilatticeSup Psup
#align subtype.lattice Subtype.lattice

def Function.Injective.semilatticeSup [Sup α] [SemilatticeSup β] (f : α → β)
    (hf_inj : Function.Injective f) (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) :
    SemilatticeSup α where
  __ := PartialOrder.lift f hf_inj
  sup := Sup.sup
  le_sup_left a b := by
    change f a ≤ f (a ⊔ b)
    rw [map_sup]
    exact le_sup_left
  le_sup_right a b := by
    change f b ≤ f (a ⊔ b)
    rw [map_sup]
    exact le_sup_right
  sup_le a b c ha hb := by
    change f (a ⊔ b) ≤ f c
    rw [map_sup]
    exact sup_le ha hb
#align function.injective.semilattice_sup Function.Injective.semilatticeSup

def Function.Injective.semilatticeInf [Inf α] [SemilatticeInf β] (f : α → β)
    (hf_inj : Function.Injective f) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b) :
    SemilatticeInf α where
  __ := PartialOrder.lift f hf_inj
  inf := Inf.inf
  inf_le_left a b := by
    change f (a ⊓ b) ≤ f a
    rw [map_inf]
    exact inf_le_left
  inf_le_right a b := by
    change f (a ⊓ b) ≤ f b
    rw [map_inf]
    exact inf_le_right
  le_inf a b c ha hb := by
    change f a ≤ f (b ⊓ c)
    rw [map_inf]
    exact le_inf ha hb
#align function.injective.semilattice_inf Function.Injective.semilatticeInf

def Function.Injective.lattice [Sup α] [Inf α] [Lattice β] (f : α → β)
    (hf_inj : Function.Injective f)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b) :
    Lattice α where
  __ := hf_inj.semilatticeSup f map_sup
  __ := hf_inj.semilatticeInf f map_inf
#align function.injective.lattice Function.Injective.lattice

def Function.Injective.distribLattice [Sup α] [Inf α] [DistribLattice β] (f : α → β)
    (hf_inj : Function.Injective f) (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b)
    (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b) :
    DistribLattice α where
  __ := hf_inj.lattice f map_sup map_inf
  le_sup_inf a b c := by
    change f ((a ⊔ b) ⊓ (a ⊔ c)) ≤ f (a ⊔ b ⊓ c)
    rw [map_inf, map_sup, map_sup, map_sup, map_inf]
    exact le_sup_inf
#align function.injective.distrib_lattice Function.Injective.distribLattice

structure of a
join-semilattice.

The partial order is defined so that `a ≤ b` unfolds to `a ⊔ b = b`; cf. `sup_eq_right`.
-/
def SemilatticeSup.mk' {α : Type*} [Sup α] (sup_comm : ∀ a b : α, a ⊔ b = b ⊔ a)
    (sup_assoc : ∀ a b c : α, a ⊔ b ⊔ c = a ⊔ (b ⊔ c)) (sup_idem : ∀ a : α, a ⊔ a = a) :
    SemilatticeSup α where
  sup := (· ⊔ ·)
  le a b := a ⊔ b = b
  le_refl := sup_idem
  le_trans a b c hab hbc := by dsimp; rw [← hbc, ← sup_assoc, hab]
  le_antisymm a b hab hba := by rwa [← hba, sup_comm]
  le_sup_left a b := by dsimp; rw [← sup_assoc, sup_idem]
  le_sup_right a b := by dsimp; rw [sup_comm, sup_assoc, sup_idem]
  sup_le a b c hac hbc := by dsimp; rwa [sup_assoc, hbc]
#align semilattice_sup.mk' SemilatticeSup.mk'

structure of a
meet-semilattice.

The partial order is defined so that `a ≤ b` unfolds to `b ⊓ a = a`; cf. `inf_eq_right`.
-/
def SemilatticeInf.mk' {α : Type*} [Inf α] (inf_comm : ∀ a b : α, a ⊓ b = b ⊓ a)
    (inf_assoc : ∀ a b c : α, a ⊓ b ⊓ c = a ⊓ (b ⊓ c)) (inf_idem : ∀ a : α, a ⊓ a = a) :
    SemilatticeInf α := by
  haveI : SemilatticeSup αᵒᵈ := SemilatticeSup.mk' inf_comm inf_assoc inf_idem
  haveI i := OrderDual.instSemilatticeInf αᵒᵈ
  exact i
#align semilattice_inf.mk' SemilatticeInf.mk'

structure of a lattice.

The partial order is defined so that `a ≤ b` unfolds to `a ⊔ b = b`; cf. `sup_eq_right`.
-/
def Lattice.mk' {α : Type*} [Sup α] [Inf α] (sup_comm : ∀ a b : α, a ⊔ b = b ⊔ a)
    (sup_assoc : ∀ a b c : α, a ⊔ b ⊔ c = a ⊔ (b ⊔ c)) (inf_comm : ∀ a b : α, a ⊓ b = b ⊓ a)
    (inf_assoc : ∀ a b c : α, a ⊓ b ⊓ c = a ⊓ (b ⊓ c)) (sup_inf_self : ∀ a b : α, a ⊔ a ⊓ b = a)
    (inf_sup_self : ∀ a b : α, a ⊓ (a ⊔ b) = a) : Lattice α :=
  have sup_idem : ∀ b : α, b ⊔ b = b := fun b =>
    calc
      b ⊔ b = b ⊔ b ⊓ (b ⊔ b) := by rw [inf_sup_self]
      _ = b := by rw [sup_inf_self]

  have inf_idem : ∀ b : α, b ⊓ b = b := fun b =>
    calc
      b ⊓ b = b ⊓ (b ⊔ b ⊓ b) := by rw [sup_inf_self]
      _ = b := by rw [inf_sup_self]

  let semilatt_inf_inst := SemilatticeInf.mk' inf_comm inf_assoc inf_idem
  let semilatt_sup_inst := SemilatticeSup.mk' sup_comm sup_assoc sup_idem
  have partial_order_eq : @SemilatticeSup.toPartialOrder _ semilatt_sup_inst =
                          @SemilatticeInf.toPartialOrder _ semilatt_inf_inst :=
    semilatticeSup_mk'_partialOrder_eq_semilatticeInf_mk'_partialOrder _ _ _ _ _ _
      sup_inf_self inf_sup_self
  { semilatt_sup_inst, semilatt_inf_inst with
    inf_le_left := fun a b => by
      rw [partial_order_eq]
      apply inf_le_left,
    inf_le_right := fun a b => by
      rw [partial_order_eq]
      apply inf_le_right,
    le_inf := fun a b c => by
      rw [partial_order_eq]
      apply le_inf }
#align lattice.mk' Lattice.mk'