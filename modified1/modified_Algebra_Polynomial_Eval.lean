def eval₂ (p : R[X]) : S :=
  p.sum fun e a => f a * x ^ e
#align polynomial.eval₂ Polynomial.eval₂

def eval₂AddMonoidHom : R[X] →+ S where
  toFun := eval₂ f x
  map_zero' := eval₂_zero _ _
  map_add' _ _ := eval₂_add _ _
#align polynomial.eval₂_add_monoid_hom Polynomial.eval₂AddMonoidHom

def eval₂RingHom' (f : R →+* S) (x : S) (hf : ∀ a, Commute (f a) x) : R[X] →+* S where
  toFun := eval₂ f x
  map_add' _ _ := eval₂_add _ _
  map_zero' := eval₂_zero _ _
  map_mul' _p q := eval₂_mul_noncomm f x fun k => hf <| coeff q k
  map_one' := eval₂_one _ _
#align polynomial.eval₂_ring_hom' Polynomial.eval₂RingHom'

def eval₂RingHom (f : R →+* S) (x : S) : R[X] →+* S :=
  { eval₂AddMonoidHom f x with
    map_one' := eval₂_one _ _
    map_mul' := fun _ _ => eval₂_mul _ _ }
#align polynomial.eval₂_ring_hom Polynomial.eval₂RingHom

def eval : R → R[X] → R :=
  eval₂ (RingHom.id _)
#align polynomial.eval Polynomial.eval

def leval {R : Type*} [Semiring R] (r : R) : R[X] →ₗ[R] R where
  toFun f := f.eval r
  map_add' _f _g := eval_add
  map_smul' c f := eval_smul c f r
#align polynomial.leval Polynomial.leval

def IsRoot (p : R[X]) (a : R) : Prop :=
  p.eval a = 0
#align polynomial.is_root Polynomial.IsRoot

def : IsRoot p a ↔ p.eval a = 0 :=
  Iff.rfl
#align polynomial.is_root.def Polynomial.IsRoot.def

def comp (p q : R[X]) : R[X] :=
  p.eval₂ C q
#align polynomial.comp Polynomial.comp

def map : R[X] → S[X] :=
  eval₂ (C.comp f) X
#align polynomial.map Polynomial.map

def mapRingHom (f : R →+* S) : R[X] →+* S[X] where
  toFun := Polynomial.map f
  map_add' _ _ := Polynomial.map_add f
  map_zero' := Polynomial.map_zero f
  map_mul' _ _ := Polynomial.map_mul f
  map_one' := Polynomial.map_one f
#align polynomial.map_ring_hom Polynomial.mapRingHom

def mapEquiv (e : R ≃+* S) : R[X] ≃+* S[X] :=
  RingEquiv.ofHomInv (mapRingHom (e : R →+* S)) (mapRingHom (e.symm : S →+* R)) (by ext <;> simp)
    (by ext <;> simp)
#align polynomial.map_equiv Polynomial.mapEquiv

def piEquiv {ι} [Finite ι] (R : ι → Type*) [∀ i, Semiring (R i)] :
    (∀ i, R i)[X] ≃+* ∀ i, (R i)[X] :=
  .ofBijective (Pi.ringHom fun i ↦ mapRingHom (Pi.evalRingHom R i))
    ⟨fun p q h ↦ by ext n i; simpa using congr_arg (fun p ↦ coeff (p i) n) h,
      fun p ↦ ⟨.ofFinsupp (.ofSupportFinite (fun n i ↦ coeff (p i) n) <|
        (Set.finite_iUnion fun i ↦ (p i).support.finite_toSet).subset fun n hn ↦ by
          simp only [Set.mem_iUnion, Finset.mem_coe, mem_support_iff, Function.mem_support] at hn ⊢
          contrapose! hn; exact funext hn), by ext i n; exact coeff_map _ _⟩⟩

theorem eval₂_eq_eval_map {x : S} : p.eval₂ f x = (p.map f).eval x := by
  induction p using Polynomial.induction_on' with
  | h_add p q hp hq =>
    simp [hp, hq]
  | h_monomial n r =>
    simp
#align polynomial.eval₂_eq_eval_map Polynomial.eval₂_eq_eval_map

def evalRingHom : R → R[X] →+* R :=
  eval₂RingHom (RingHom.id _)
#align polynomial.eval_ring_hom Polynomial.evalRingHom

def compRingHom : R[X] → R[X] →+* R[X] :=
  eval₂RingHom C
#align polynomial.comp_ring_hom Polynomial.compRingHom