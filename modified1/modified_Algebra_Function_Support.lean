def support [Zero A] (f : α → A) : Set α :=
  { x | f x ≠ 0 }
#align function.support Function.support

def mulSupport (f : α → M) : Set α :=
  { x | f x ≠ 1 }
#align function.mul_support Function.mulSupport