def charpoly : R[X] :=
  (toMatrix (chooseBasis R M) (chooseBasis R M) f).charpoly
#align linear_map.charpoly LinearMap.charpoly

def : f.charpoly = (toMatrix (chooseBasis R M) (chooseBasis R M) f).charpoly :=
  rfl
#align linear_map.charpoly_def LinearMap.charpoly_def