def Classical.inhabited_of_nonempty' {α} [h : Nonempty α] : Inhabited α :=
  ⟨Classical.choice h⟩
#align classical.inhabited_of_nonempty' Classical.inhabited_of_nonempty'

def Nonempty.some {α} (h : Nonempty α) : α :=
  Classical.choice h
#align nonempty.some Nonempty.some

def Classical.arbitrary (α) [h : Nonempty α] : α :=
  Classical.choice h
#align classical.arbitrary Classical.arbitrary