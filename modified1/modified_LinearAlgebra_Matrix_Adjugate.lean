def cramerMap (i : n) : α :=
  (A.updateColumn i b).det
#align matrix.cramer_map Matrix.cramerMap

def cramer (A : Matrix n n α) : (n → α) →ₗ[α] (n → α) :=
  IsLinearMap.mk' (cramerMap A) (cramer_is_linear A)
#align matrix.cramer Matrix.cramer

def adjugate (A : Matrix n n α) : Matrix n n α :=
  of fun i => cramer Aᵀ (Pi.single i 1)
#align matrix.adjugate Matrix.adjugate

def (A : Matrix n n α) : adjugate A = of fun i => cramer Aᵀ (Pi.single i 1) :=
  rfl
#align matrix.adjugate_def Matrix.adjugate_def