def Equiv.star [InvolutiveStar R] : Equiv.Perm R :=
  star_involutive.toPerm _
#align equiv.star Equiv.star

def starMulEquiv [Mul R] [StarMul R] : R ≃* Rᵐᵒᵖ :=
  { (InvolutiveStar.star_involutive.toPerm star).trans opEquiv with
    toFun := fun x => MulOpposite.op (star x)
    map_mul' := fun x y => by simp only [star_mul, op_mul] }
#align star_mul_equiv starMulEquiv

def starMulAut [CommSemigroup R] [StarMul R] : MulAut R :=
  { InvolutiveStar.star_involutive.toPerm star with
    toFun := star
    map_mul' := star_mul' }
#align star_mul_aut starMulAut

def starMulOfComm {R : Type*} [CommMonoid R] : StarMul R where
  star := id
  star_involutive _ := rfl
  star_mul := mul_comm
#align star_semigroup_of_comm starMulOfComm

def starAddEquiv [AddMonoid R] [StarAddMonoid R] : R ≃+ R :=
  { InvolutiveStar.star_involutive.toPerm star with
    toFun := star
    map_add' := star_add }
#align star_add_equiv starAddEquiv

def starRingEquiv [NonUnitalNonAssocSemiring R] [StarRing R] : R ≃+* Rᵐᵒᵖ :=
  { starAddEquiv.trans (MulOpposite.opAddEquiv : R ≃+ Rᵐᵒᵖ), starMulEquiv with
    toFun := fun x => MulOpposite.op (star x) }
#align star_ring_equiv starRingEquiv

def starRingAut : RingAut R := { starAddEquiv, starMulAut (R := R) with toFun := star }
#align star_ring_aut starRingAut

def starRingEnd : R →+* R := @starRingAut R _ _
#align star_ring_end starRingEnd

def {S : Type*} [NonAssocSemiring S] (f : S →+* R) :
    Star.star f = RingHom.comp (starRingEnd R) f := rfl
#align ring_hom.star_def RingHom.star_def

def starRingOfComm {R : Type*} [CommSemiring R] : StarRing R :=
  { starMulOfComm with
    star_add := fun _ _ => rfl }
#align star_ring_of_comm starRingOfComm

structure with a star operation.
-/
class Star (R : Type u) where
  star : R → R
#align has_star Star

structure into a `*`-multiplication
(i.e. `star (r * s) = star s * star r`).  -/
class StarRing (R : Type u) [NonUnitalNonAssocSemiring R] extends StarMul R where
  /-- `star` commutes with addition -/
  star_add : ∀ r s : R, star (r + s) = star r + star s
#align star_ring StarRing