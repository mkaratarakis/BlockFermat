def Nat.iterate {α : Sort u} (op : α → α) : ℕ → α → α
  | 0, a => a
  | succ k, a => iterate op k (op a)
#align nat.iterate Nat.iterate

def Iterate.rec (p : α → Sort*) {f : α → α} (h : ∀ a, p a → p (f a)) {a : α} (ha : p a) (n : ℕ) :
    p (f^[n] a) :=
  match n with
  | 0 => ha
  | m+1 => Iterate.rec p h (h _ ha) m
#align function.iterate.rec Function.Iterate.rec