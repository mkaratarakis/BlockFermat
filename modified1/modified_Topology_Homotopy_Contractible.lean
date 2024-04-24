def Nullhomotopic (f : C(X, Y)) : Prop :=
  ∃ y : Y, Homotopic f (ContinuousMap.const _ y)
#align continuous_map.nullhomotopic ContinuousMap.Nullhomotopic