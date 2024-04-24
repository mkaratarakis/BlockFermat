def prod {α} [Mul α] [One α] : List α → α :=
  foldl (· * ·) 1
#align list.prod List.prod

def alternatingSum {G : Type*} [Zero G] [Add G] [Neg G] : List G → G
  | [] => 0
  | g :: [] => g
  | g :: h :: t => g + -h + alternatingSum t
#align list.alternating_sum List.alternatingSum

def alternatingProd {G : Type*} [One G] [Mul G] [Inv G] : List G → G
  | [] => 1
  | g :: [] => g
  | g :: h :: t => g * h⁻¹ * alternatingProd t
#align list.alternating_prod List.alternatingProd