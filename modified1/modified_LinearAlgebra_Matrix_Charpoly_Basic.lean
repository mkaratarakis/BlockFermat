def charmatrix (M : Matrix n n R) : Matrix n n R[X] :=
  Matrix.scalar n (X : R[X]) - (C : R →+* R[X]).mapMatrix M
#align charmatrix Matrix.charmatrix

def charpoly (M : Matrix n n R) : R[X] :=
  (charmatrix M).det
#align matrix.charpoly Matrix.charpoly