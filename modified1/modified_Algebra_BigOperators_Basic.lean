def prod [CommMonoid β] (s : Finset α) (f : α → β) : β :=
  (s.1.map f).prod
#align finset.prod Finset.prod

def delabFinsetProd : Delab :=
  whenPPOption getPPNotation <| withOverApp 5 <| do
  let #[_, _, _, s, f] := (← getExpr).getAppArgs | failure

def delabFinsetSum : Delab :=
  whenPPOption getPPNotation <| withOverApp 5 <| do
  let #[_, _, _, s, f] := (← getExpr).getAppArgs | failure