def isEmptyElim [IsEmpty α] {p : α → Sort*} (a : α) : p a :=
  (IsEmpty.false a).elim
#align is_empty_elim isEmptyElim

def elim {α : Sort u} (_ : IsEmpty α) {p : α → Sort*} (a : α) : p a :=
  isEmptyElim a
#align is_empty.elim IsEmpty.elim

def elim' {β : Sort*} (h : IsEmpty α) (a : α) : β :=
  (h.false a).elim
#align is_empty.elim' IsEmpty.elim'