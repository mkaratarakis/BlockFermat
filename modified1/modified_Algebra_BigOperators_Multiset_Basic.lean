def prod : Multiset α → α :=
  foldr (· * ·) (fun x y z => by simp [mul_left_comm]) 1
#align multiset.prod Multiset.prod

def sumAddMonoidHom : Multiset α →+ α where
  toFun := sum
  map_zero' := sum_zero
  map_add' := sum_add
#align multiset.sum_add_monoid_hom Multiset.sumAddMonoidHom

structure on `α`.
  `prod {a, b, c} = a * b * c` -/
@[to_additive
      "Sum of a multiset given a commutative additive monoid structure on `α`.
      `sum {a, b, c} = a + b + c`"]
def prod : Multiset α → α :=
  foldr (· * ·) (fun x y z => by simp [mul_left_comm]) 1
#align multiset.prod Multiset.prod