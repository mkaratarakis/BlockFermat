def affineSegment (x y : P) :=
  lineMap x y '' Set.Icc (0 : R) 1
#align affine_segment affineSegment

def Wbtw (x y z : P) : Prop :=
  y ∈ affineSegment R x z
#align wbtw Wbtw

def Sbtw (x y z : P) : Prop :=
  Wbtw R x y z ∧ y ≠ x ∧ y ≠ z
#align sbtw Sbtw