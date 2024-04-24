def lcm (s : Finset β) (f : β → α) : α :=
  s.fold GCDMonoid.lcm 1 f
#align finset.lcm Finset.lcm

def : s.lcm f = (s.1.map f).lcm :=
  rfl
#align finset.lcm_def Finset.lcm_def

def gcd (s : Finset β) (f : β → α) : α :=
  s.fold GCDMonoid.gcd 0 f
#align finset.gcd Finset.gcd

def : s.gcd f = (s.1.map f).gcd :=
  rfl
#align finset.gcd_def Finset.gcd_def