def FreeMonoid (α) := List α
#align free_monoid FreeMonoid

def toList : FreeMonoid α ≃ List α := Equiv.refl _
#align free_monoid.to_list FreeMonoid.toList

def ofList : List α ≃ FreeMonoid α := Equiv.refl _
#align free_monoid.of_list FreeMonoid.ofList

def of (x : α) : FreeMonoid α := ofList [x]
#align free_monoid.of FreeMonoid.of

def recOn {C : FreeMonoid α → Sort*} (xs : FreeMonoid α) (h0 : C 1)
    (ih : ∀ x xs, C xs → C (of x * xs)) : C xs := List.rec h0 ih xs
#align free_monoid.rec_on FreeMonoid.recOn

def casesOn {C : FreeMonoid α → Sort*} (xs : FreeMonoid α) (h0 : C 1)
    (ih : ∀ x xs, C (of x * xs)) : C xs := List.casesOn xs h0 ih
#align free_monoid.cases_on FreeMonoid.casesOn

def prodAux {M} [Monoid M] : List M → M
  | [] => 1
  | (x :: xs) => List.foldl (· * ·) x xs
#align free_monoid.prod_aux FreeMonoid.prodAux

def lift : (α → M) ≃ (FreeMonoid α →* M) where
  toFun f :=
  { toFun := fun l ↦ prodAux ((toList l).map f)
    map_one' := rfl
    map_mul' := fun _ _ ↦ by simp only [prodAux_eq, toList_mul, List.map_append, List.prod_append] }
  invFun f x := f (of x)
  left_inv f := rfl
  right_inv f := hom_eq fun x ↦ rfl
#align free_monoid.lift FreeMonoid.lift

def mkMulAction (f : α → β → β) : MulAction (FreeMonoid α) β where
  smul l b := l.toList.foldr f b
  one_smul _ := rfl
  mul_smul _ _ _ := List.foldr_append _ _ _ _
#align free_monoid.mk_mul_action FreeMonoid.mkMulAction

def (f : α → β → β) (l : FreeMonoid α) (b : β) :
    haveI := mkMulAction f
    l • b = l.toList.foldr f b := rfl
#align free_monoid.smul_def FreeMonoid.smul_def

def FreeAddMonoid.vadd_def

@[to_additive]
theorem ofList_smul (f : α → β → β) (l : List α) (b : β) :
    haveI := mkMulAction f
    ofList l • b = l.foldr f b := rfl
#align free_monoid.of_list_smul FreeMonoid.ofList_smul

def map (f : α → β) : FreeMonoid α →* FreeMonoid β
    where
  toFun l := ofList <| l.toList.map f
  map_one' := rfl
  map_mul' _ _ := List.map_append _ _ _
#align free_monoid.map FreeMonoid.map