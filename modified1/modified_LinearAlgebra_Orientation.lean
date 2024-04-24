def Orientation.map (e : M ≃ₗ[R] N) : Orientation R M ι ≃ Orientation R N ι :=
  Module.Ray.map <| AlternatingMap.domLCongr R R ι R e
#align orientation.map Orientation.map

def Orientation.reindex (e : ι ≃ ι') : Orientation R M ι ≃ Orientation R M ι' :=
  Module.Ray.map <| AlternatingMap.domDomCongrₗ R e
#align orientation.reindex Orientation.reindex

def orientation (e : Basis ι R M) : Orientation R M ι :=
  rayOfNeZero R _ e.det_ne_zero
#align basis.orientation Basis.orientation

def adjustToOrientation [Nonempty ι] (e : Basis ι R M) (x : Orientation R M ι) :
    Basis ι R M :=
  haveI := Classical.decEq (Orientation R M ι)
  if e.orientation = x then e else e.unitsSMul (Function.update 1 (Classical.arbitrary ι) (-1))
#align basis.adjust_to_orientation Basis.adjustToOrientation

def someBasis [Nonempty ι] [DecidableEq ι] (x : Orientation R M ι)
    (h : Fintype.card ι = finrank R M) : Basis ι R M :=
  ((finBasis R M).reindex (Fintype.equivFinOfCardEq h).symm).adjustToOrientation x
#align orientation.some_basis Orientation.someBasis