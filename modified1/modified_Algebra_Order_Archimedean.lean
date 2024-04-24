def Archimedean.floorRing (α) [LinearOrderedRing α] [Archimedean α] : FloorRing α :=
  FloorRing.ofFloor α (fun a => Classical.choose (exists_floor a)) fun z a =>
    (Classical.choose_spec (exists_floor a) z).symm
#align archimedean.floor_ring Archimedean.floorRing