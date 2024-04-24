def nfpFamily (f : ι → Ordinal → Ordinal) (a : Ordinal) : Ordinal :=
  sup (List.foldr f a)
#align ordinal.nfp_family Ordinal.nfpFamily

def derivFamily (f : ι → Ordinal → Ordinal) (o : Ordinal) : Ordinal :=
  limitRecOn o (nfpFamily.{u, v} f 0) (fun _ IH => nfpFamily.{u, v} f (succ IH))
    fun a _ => bsup.{max u v, u} a
#align ordinal.deriv_family Ordinal.derivFamily

def nfpBFamily (o : Ordinal) (f : ∀ b < o, Ordinal → Ordinal) : Ordinal → Ordinal :=
  nfpFamily (familyOfBFamily o f)
#align ordinal.nfp_bfamily Ordinal.nfpBFamily

def derivBFamily (o : Ordinal) (f : ∀ b < o, Ordinal → Ordinal) : Ordinal → Ordinal :=
  derivFamily (familyOfBFamily o f)
#align ordinal.deriv_bfamily Ordinal.derivBFamily

def nfp (f : Ordinal → Ordinal) : Ordinal → Ordinal :=
  nfpFamily fun _ : Unit => f
#align ordinal.nfp Ordinal.nfp

def deriv (f : Ordinal → Ordinal) : Ordinal → Ordinal :=
  derivFamily fun _ : Unit => f
#align ordinal.deriv Ordinal.deriv