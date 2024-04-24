def iSup [SupSet α] (s : ι → α) : α :=
  sSup (range s)
#align supr iSup

def iInf [InfSet α] (s : ι → α) : α :=
  sInf (range s)
#align infi iInf

def iSup_delab : Delab := whenPPOption Lean.getPPNotation <| withOverApp 4 do
  let #[_, ι, _, f] := (← SubExpr.getExpr).getAppArgs | failure

def iInf_delab : Delab := whenPPOption Lean.getPPNotation <| withOverApp 4 do
  let #[_, ι, _, f] := (← SubExpr.getExpr).getAppArgs | failure

def sInter (S : Set (Set α)) : Set α :=
  sInf S
#align set.sInter Set.sInter

def sUnion (S : Set (Set α)) : Set α :=
  sSup S
#align set.sUnion Set.sUnion

def iUnion (s : ι → Set α) : Set α :=
  iSup s
#align set.Union Set.iUnion

def iInter (s : ι → Set α) : Set α :=
  iInf s
#align set.Inter Set.iInter

def iUnion_delab : Delab := whenPPOption Lean.getPPNotation do
  let #[_, ι, f] := (← SubExpr.getExpr).getAppArgs | failure

def sInter_delab : Delab := whenPPOption Lean.getPPNotation do
  let #[_, ι, f] := (← SubExpr.getExpr).getAppArgs | failure