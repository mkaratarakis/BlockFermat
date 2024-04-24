def WithOne (α) :=
  Option α
#align with_one WithOne

def coe : α → WithOne α :=
  Option.some

@[to_additive]
instance coeTC : CoeTC α (WithOne α) :=
  ⟨coe⟩

/-- Recursor for `WithOne` using the preferred forms `1` and `↑a`. -/
@[to_additive (attr := elab_as_elim)
  "Recursor for `WithZero` using the preferred forms `0` and `↑a`."]
def recOneCoe {C : WithOne α → Sort*} (h₁ : C 1) (h₂ : ∀ a : α, C a) : ∀ n : WithOne α, C n
  | Option.none => h₁
  | Option.some x => h₂ x
#align with_one.rec_one_coe WithOne.recOneCoe

def unone : ∀ {x : WithOne α}, x ≠ 1 → α | (x : α), _ => x
#align with_one.unone WithOne.unone

structure which then
behaves like a zero or a one. An example is adjoining a one to a semigroup to obtain a monoid. That
this provides an example of an adjunction is proved in `Algebra.Category.MonCat.Adjunctions`.

Another result says that adjoining to a group an element `zero` gives a `GroupWithZero`. For more
information about these structures (which are not that standard in informal mathematics, see
`Algebra.GroupWithZero.Basic`)

## Porting notes