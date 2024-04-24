def Ideal.closure (I : Ideal R) : Ideal R :=
  {
    AddSubmonoid.topologicalClosure
      I.toAddSubmonoid with
    carrier := closure I
    smul_mem' := fun c _ hx => map_mem_closure (mulLeft_continuous _) hx fun _ => I.mul_mem_left c }
#align ideal.closure Ideal.closure

structure on the quotient of a topological ring by an
ideal and prove that the quotient is a topological ring.
-/


section Ring

variable {R : Type*} [TopologicalSpace R] [Ring R] [TopologicalRing R]

/-- The closure of an ideal in a topological ring as an ideal. -/
protected def Ideal.closure (I : Ideal R) : Ideal R :=
  {
    AddSubmonoid.topologicalClosure
      I.toAddSubmonoid with
    carrier := closure I
    smul_mem' := fun c _ hx => map_mem_closure (mulLeft_continuous _) hx fun _ => I.mul_mem_left c }
#align ideal.closure Ideal.closure