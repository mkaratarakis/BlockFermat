def [Star R] [Star S] (x : R × S) : star x = (star x.1, star x.2) :=
  rfl
#align prod.star_def Prod.star_def

structure on product types that operates elementwise.
-/


universe u v w

variable {R : Type u} {S : Type v}

namespace Prod

instance [Star R] [Star S] : Star (R × S) where star x := (star x.1, star x.2)

@[simp]
theorem fst_star [Star R] [Star S] (x : R × S) : (star x).1 = star x.1 :=
  rfl
#align prod.fst_star Prod.fst_star