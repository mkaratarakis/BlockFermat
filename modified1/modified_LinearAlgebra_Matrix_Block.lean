def BlockTriangular (M : Matrix m m R) (b : m → α) : Prop :=
  ∀ ⦃i j⦄, b j < b i → M i j = 0
#align matrix.block_triangular Matrix.BlockTriangular

def BlockTriangular.invertibleToBlock [LinearOrder α] [Invertible M] (hM : BlockTriangular M b)
    (k : α) : Invertible (M.toBlock (fun i => b i < k) fun i => b i < k) :=
  invertibleOfLeftInverse _ ((⅟ M).toBlock (fun i => b i < k) fun i => b i < k) <| by
    simpa only [invOf_eq_nonsing_inv] using hM.toBlock_inverse_mul_toBlock_eq_one k
#align matrix.block_triangular.invertible_to_block Matrix.BlockTriangular.invertibleToBlock