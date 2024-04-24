def finZeroEquiv : Fin 0 ≃ Empty :=
  Equiv.equivEmpty _
#align fin_zero_equiv finZeroEquiv

def finZeroEquiv' : Fin 0 ≃ PEmpty.{u} :=
  Equiv.equivPEmpty _
#align fin_zero_equiv' finZeroEquiv'

def finOneEquiv : Fin 1 ≃ Unit :=
  Equiv.equivPUnit _
#align fin_one_equiv finOneEquiv

def finTwoEquiv : Fin 2 ≃ Bool where
  toFun := ![false, true]
  invFun b := b.casesOn 0 1
  left_inv := Fin.forall_fin_two.2 <| by simp
  right_inv := Bool.forall_bool.2 <| by simp
#align fin_two_equiv finTwoEquiv

def piFinTwoEquiv (α : Fin 2 → Type u) : (∀ i, α i) ≃ α 0 × α 1
    where
  toFun f := (f 0, f 1)
  invFun p := Fin.cons p.1 <| Fin.cons p.2 finZeroElim
  left_inv _ := funext <| Fin.forall_fin_two.2 ⟨rfl, rfl⟩
  right_inv := fun _ => rfl
#align pi_fin_two_equiv piFinTwoEquiv

def prodEquivPiFinTwo (α β : Type u) : α × β ≃ ∀ i : Fin 2, ![α, β] i :=
  (piFinTwoEquiv (Fin.cons α (Fin.cons β finZeroElim))).symm
#align prod_equiv_pi_fin_two prodEquivPiFinTwo

def finTwoArrowEquiv (α : Type*) : (Fin 2 → α) ≃ α × α :=
  { piFinTwoEquiv fun _ => α with invFun := fun x => ![x.1, x.2] }
#align fin_two_arrow_equiv finTwoArrowEquiv

def OrderIso.piFinTwoIso (α : Fin 2 → Type u) [∀ i, Preorder (α i)] : (∀ i, α i) ≃o α 0 × α 1
    where
  toEquiv := piFinTwoEquiv α
  map_rel_iff' := Iff.symm Fin.forall_fin_two
#align order_iso.pi_fin_two_iso OrderIso.piFinTwoIso

def OrderIso.finTwoArrowIso (α : Type*) [Preorder α] : (Fin 2 → α) ≃o α × α :=
  { OrderIso.piFinTwoIso fun _ => α with toEquiv := finTwoArrowEquiv α }
#align order_iso.fin_two_arrow_iso OrderIso.finTwoArrowIso

def finCongr (h : m = n) : Fin m ≃ Fin n :=
  (Fin.castIso h).toEquiv
#align fin_congr finCongr

def finSuccEquiv' (i : Fin (n + 1)) : Fin (n + 1) ≃ Option (Fin n)
    where
  toFun := i.insertNth none some
  invFun x := x.casesOn' i (Fin.succAbove i)
  left_inv x := Fin.succAboveCases i (by simp) (fun j => by simp) x
  right_inv x := by cases x <;> dsimp <;> simp
#align fin_succ_equiv' finSuccEquiv'

def finSuccEquiv (n : ℕ) : Fin (n + 1) ≃ Option (Fin n) :=
  finSuccEquiv' 0
#align fin_succ_equiv finSuccEquiv

def finSuccAboveEquiv (p : Fin (n + 1)) : Fin n ≃o { x : Fin (n + 1) // x ≠ p } :=
  { Equiv.optionSubtype p ⟨(finSuccEquiv' p).symm, rfl⟩ with
    map_rel_iff' := p.succAboveEmb.map_rel_iff' }
#align fin_succ_above_equiv finSuccAboveEquiv

def finSuccEquivLast : Fin (n + 1) ≃ Option (Fin n) :=
  finSuccEquiv' (Fin.last n)
#align fin_succ_equiv_last finSuccEquivLast

def Equiv.piFinSuccAbove (α : Fin (n + 1) → Type u) (i : Fin (n + 1)) :
    (∀ j, α j) ≃ α i × ∀ j, α (i.succAbove j) where
  toFun f := i.extractNth f
  invFun f := i.insertNth f.1 f.2
  left_inv f := by simp
  right_inv f := by simp
#align equiv.pi_fin_succ_above_equiv Equiv.piFinSuccAbove

def OrderIso.piFinSuccAboveIso (α : Fin (n + 1) → Type u) [∀ i, LE (α i)]
    (i : Fin (n + 1)) : (∀ j, α j) ≃o α i × ∀ j, α (i.succAbove j) where
  toEquiv := Equiv.piFinSuccAbove α i
  map_rel_iff' := Iff.symm i.forall_iff_succAbove
#align order_iso.pi_fin_succ_above_iso OrderIso.piFinSuccAboveIso

def Equiv.piFinSucc (n : ℕ) (β : Type u) : (Fin (n + 1) → β) ≃ β × (Fin n → β) :=
  Equiv.piFinSuccAbove (fun _ => β) 0
#align equiv.pi_fin_succ Equiv.piFinSucc

def Equiv.piFinCastSucc (n : ℕ) (β : Type u) : (Fin (n + 1) → β) ≃ β × (Fin n → β) :=
  Equiv.piFinSuccAbove (fun _ => β) (.last _)

/-- Equivalence between `Fin m ⊕ Fin n` and `Fin (m + n)` -/
def finSumFinEquiv : Sum (Fin m) (Fin n) ≃ Fin (m + n)
    where
  toFun := Sum.elim (Fin.castAdd n) (Fin.natAdd m)
  invFun i := @Fin.addCases m n (fun _ => Sum (Fin m) (Fin n)) Sum.inl Sum.inr i
  left_inv x := by cases' x with y y <;> dsimp <;> simp
  right_inv x := by refine' Fin.addCases (fun i => _) (fun i => _) x <;> simp
#align fin_sum_fin_equiv finSumFinEquiv

def finAddFlip : Fin (m + n) ≃ Fin (n + m) :=
  (finSumFinEquiv.symm.trans (Equiv.sumComm _ _)).trans finSumFinEquiv
#align fin_add_flip finAddFlip

def finRotate : ∀ n, Equiv.Perm (Fin n)
  | 0 => Equiv.refl _
  | n + 1 => finAddFlip.trans (finCongr (add_comm 1 n))
#align fin_rotate finRotate

def finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n)
    where
  toFun x :=
    ⟨x.2 + n * x.1,
      calc
        x.2.1 + n * x.1.1 + 1 = x.1.1 * n + x.2.1 + 1 := by ac_rfl
        _ ≤ x.1.1 * n + n := Nat.add_le_add_left x.2.2 _
        _ = (x.1.1 + 1) * n := Eq.symm <| Nat.succ_mul _ _
        _ ≤ m * n := Nat.mul_le_mul_right _ x.1.2
        ⟩
  invFun x := (x.divNat, x.modNat)
  left_inv := fun ⟨x, y⟩ =>
    have H : 0 < n := Nat.pos_of_ne_zero fun H => Nat.not_lt_zero y.1 <| H ▸ y.2
    Prod.ext
      (Fin.eq_of_val_eq <|
        calc
          (y.1 + n * x.1) / n = y.1 / n + x.1 := Nat.add_mul_div_left _ _ H
          _ = 0 + x.1 := by rw [Nat.div_eq_of_lt y.2]
          _ = x.1 := Nat.zero_add x.1
          )
      (Fin.eq_of_val_eq <|
        calc
          (y.1 + n * x.1) % n = y.1 % n := Nat.add_mul_mod_self_left _ _ _
          _ = y.1 := Nat.mod_eq_of_lt y.2
          )
  right_inv x := Fin.eq_of_val_eq <| Nat.mod_add_div _ _
#align fin_prod_fin_equiv finProdFinEquiv

def Nat.divModEquiv (n : ℕ) [NeZero n] : ℕ ≃ ℕ × Fin n where
  toFun a := (a / n, ↑a)
  invFun p := p.1 * n + ↑p.2
  -- TODO: is there a canonical order of `*` and `+` here?
  left_inv a := Nat.div_add_mod' _ _
  right_inv p := by
    refine' Prod.ext _ (Fin.ext <| Nat.mul_add_mod_of_lt p.2.is_lt)
    dsimp only
    rw [add_comm, Nat.add_mul_div_right _ _ (NeZero.pos n), Nat.div_eq_of_lt p.2.is_lt, zero_add]
#align nat.div_mod_equiv Nat.divModEquiv

def Int.divModEquiv (n : ℕ) [NeZero n] : ℤ ≃ ℤ × Fin n where
  -- TODO: could cast from int directly if we import `Data.ZMod.Defs`, though there are few lemmas
  -- about that coercion.
  toFun a := (a / n, ↑(a.natMod n))
  invFun p := p.1 * n + ↑p.2
  left_inv a := by
    simp_rw [Fin.coe_ofNat_eq_mod, Int.natCast_mod, Int.natMod,
      Int.toNat_of_nonneg (Int.emod_nonneg _ <| NeZero.ne ↑n), Int.emod_emod,
      Int.ediv_add_emod']
  right_inv := fun ⟨q, r, hrn⟩ => by
    simp only [Fin.val_mk, Prod.mk.inj_iff, Fin.ext_iff]
    obtain ⟨h1, h2⟩ := Int.natCast_nonneg r, Int.ofNat_lt.2 hrn
    rw [add_comm, Int.add_mul_ediv_right _ _ (NeZero.ne ↑n), Int.ediv_eq_zero_of_lt h1 h2,
      Int.natMod, Int.add_mul_emod_self, Int.emod_eq_of_lt h1 h2, Int.toNat_natCast]
    exact ⟨zero_add q, Fin.val_cast_of_lt hrn⟩
#align int.div_mod_equiv Int.divModEquiv

def Fin.castLEOrderIso {n m : ℕ} (h : n ≤ m) : Fin n ≃o { i : Fin m // (i : ℕ) < n }
    where
  toFun i := ⟨Fin.castLE h i, by simp⟩
  invFun i := ⟨i, i.prop⟩
  left_inv _ := by simp
  right_inv _ := by simp
  map_rel_iff' := by simp [(strictMono_castLE h).le_iff_le]
#align fin.cast_le_order_iso Fin.castLEOrderIso