def mulLeft₀ (a : G) (ha : a ≠ 0) : Perm G :=
  (Units.mk0 a ha).mulLeft
#align equiv.mul_left₀ Equiv.mulLeft₀

def mulRight₀ (a : G) (ha : a ≠ 0) : Perm G :=
  (Units.mk0 a ha).mulRight
#align equiv.mul_right₀ Equiv.mulRight₀