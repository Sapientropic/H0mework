import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.TruncatedFourier.Radius.Scaling.Variation.FiniteRank.OriginalSource
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.WindowEffect
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKNativeSourceReturn.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace FixedWindowFourierReaction
open Complex MeasureTheory Set
open scoped InnerProductSpace

def gapTail (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  burnolAmbientEvenPart (burnolAmbientCompletedMellinKernelFormula coordinate)
def originalShell (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  burnolAmbientEvenPart (burnolRieszSourceRawShell coordinate)

theorem original_kernel_source (coordinate : BurnolCompletedMellinCoordinate) :
    (burnolCompletedMellinRieszVector coordinate : BurnolL2) = gapTail coordinate-originalShell coordinate := by
  rw [burnolCompletedMellinRieszVector_eq_singleFourierSource]
  unfold gapTail originalShell burnolRieszSourceRawShell burnolAmbientEvenPart
  simp only [map_sub]
  module

-- Every original contact crossing is retained, with the actual outside gap/tail and increment.
theorem original_actual_price (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) (increment : BurnolL2) :
    inner ℂ (burnolCompletedMellinRieszVector coordinate : BurnolL2)
      (burnolMultiplicativeDilation h ((burnolCompletedMellinRieszVector coordinate : BurnolL2)+increment)) =
      inner ℂ (burnolCompletedMellinRieszVector coordinate : BurnolL2)
        (burnolMultiplicativeDilation h (gapTail coordinate)) -
      inner ℂ (gapTail coordinate) (burnolMultiplicativeDilation h (originalShell coordinate)) +
      inner ℂ (originalShell coordinate) (burnolMultiplicativeDilation h (originalShell coordinate)) +
      inner ℂ (burnolCompletedMellinRieszVector coordinate : BurnolL2) (burnolMultiplicativeDilation h increment) := by
  rw [map_add,inner_add_right]
  have initial := original_kernel_source coordinate
  have decomposition : inner ℂ (burnolCompletedMellinRieszVector coordinate : BurnolL2)
      (burnolMultiplicativeDilation h (burnolCompletedMellinRieszVector coordinate : BurnolL2)) =
    inner ℂ (burnolCompletedMellinRieszVector coordinate : BurnolL2) (burnolMultiplicativeDilation h (gapTail coordinate)) -
      inner ℂ (gapTail coordinate) (burnolMultiplicativeDilation h (originalShell coordinate)) +
      inner ℂ (originalShell coordinate) (burnolMultiplicativeDilation h (originalShell coordinate)) := by
    nth_rw 2 [initial]
    rw [map_sub,inner_sub_right]
    nth_rw 2 [initial]
    rw [inner_sub_left]
    ring
  rw [decomposition]

-- The two actual window rows read the same complete original shell at their separate radii.
theorem original_shell_pair_window (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) :
    inner ℂ (burnolRieszSourceRawShell coordinate)
      (burnolMultiplicativeDilation h (burnolRieszSourceRawShell coordinate)) =
      inner ℂ (originalB coordinate)
        (quarterChart (burnolQuarterRestriction (fourierL2
          (burnolMultiplicativeDilation h (burnolRieszSourceRawShell coordinate))))) -
      inner ℂ (quarterChart (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate) : BurnolQuarterIntervalL2))
        (quarterChart (burnolQuarterRestriction (burnolMultiplicativeDilation h (burnolRieszSourceRawShell coordinate)))) := by
  let b := burnolRieszSingleFourierSource coordinate
  let w := burnolMeanZeroTruncatedFourier b
  have reflected : reflectL2 (burnolMultiplicativeDilation h (burnolRieszSourceRawShell coordinate)) =
      burnolMultiplicativeDilation h (burnolRieszSourceRawShell coordinate) := by
    unfold burnolRieszSourceRawShell burnolQuarterZeroExtension
    rw [reflectL2_burnolMultiplicativeDilation,map_sub,← fourierL2_reflectL2_commute,
      burnolRadiusZeroExtension_reflect,burnolRadiusZeroExtension_reflect,
      burnolRieszSingleFourierSource_reflection_fixed,burnolRieszSingleFourierReturn_reflection_fixed]
  have unitary := fourierL2.inner_map_map (burnolQuarterZeroExtension (b : BurnolQuarterIntervalL2))
    (fourierL2 (burnolMultiplicativeDilation h (burnolRieszSourceRawShell coordinate)))
  rw [fourierL2_fourierL2,reflected] at unitary
  change inner ℂ (fourierL2 (burnolQuarterZeroExtension (b : BurnolQuarterIntervalL2))-
    burnolQuarterZeroExtension (w : BurnolQuarterIntervalL2))
    (burnolMultiplicativeDilation h (burnolRieszSourceRawShell coordinate)) = _
  rw [inner_sub_left,unitary]
  have extension : burnolQuarterZeroExtension = ContinuousLinearMap.adjoint burnolQuarterRestriction := rfl
  rw [extension,ContinuousLinearMap.adjoint_inner_left burnolQuarterRestriction,
    ContinuousLinearMap.adjoint_inner_left burnolQuarterRestriction]
  change inner ℂ (b : BurnolQuarterIntervalL2) _ - inner ℂ (w : BurnolQuarterIntervalL2) _ = _
  unfold originalB
  rw [quarterChart.inner_map_map,quarterChart.inner_map_map]

-- Mixed square polarization keeps its difference-square cost instead of replacing a cross with S_r².
theorem mixed_square_price (left right : H →L[ℂ] H) (source : H) :
    inner ℂ (left source) (right source)+inner ℂ (right source) (left source) =
      inner ℂ (left source) (left source)+inner ℂ (right source) (right source)-
        inner ℂ (right source-left source) (right source-left source) := by
  rw [inner_sub_sub_self]
  ring

end FixedWindowFourierReaction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
