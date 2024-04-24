def LipschitzAdd.C [AddMonoid β] [_i : LipschitzAdd β] : ℝ≥0 := Classical.choose _i.lipschitz_add
set_option linter.uppercaseLean3 false in
#align has_lipschitz_add.C LipschitzAdd.C

def LipschitzMul.C [_i : LipschitzMul β] : ℝ≥0 := Classical.choose _i.lipschitz_mul
set_option linter.uppercaseLean3 false in
#align has_lipschitz_mul.C LipschitzMul.C