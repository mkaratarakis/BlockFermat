def uncurryBilinear (f : E →L[𝕜] F →L[𝕜] G) : E × F[×2]→L[𝕜] G :=
  @ContinuousLinearMap.uncurryLeft 𝕜 1 (fun _ => E × F) G _ _ _ _ _ <|
    (↑(continuousMultilinearCurryFin1 𝕜 (E × F) G).symm : (E × F →L[𝕜] G) →L[𝕜] _).comp <|
      f.bilinearComp (fst _ _ _) (snd _ _ _)
#align continuous_linear_map.uncurry_bilinear ContinuousLinearMap.uncurryBilinear

def fpowerSeriesBilinear (f : E →L[𝕜] F →L[𝕜] G) (x : E × F) : FormalMultilinearSeries 𝕜 (E × F) G
  | 0 => ContinuousMultilinearMap.curry0 𝕜 _ (f x.1 x.2)
  | 1 => (continuousMultilinearCurryFin1 𝕜 (E × F) G).symm (f.deriv₂ x)
  | 2 => f.uncurryBilinear
  | _ => 0
#align continuous_linear_map.fpower_series_bilinear ContinuousLinearMap.fpowerSeriesBilinear