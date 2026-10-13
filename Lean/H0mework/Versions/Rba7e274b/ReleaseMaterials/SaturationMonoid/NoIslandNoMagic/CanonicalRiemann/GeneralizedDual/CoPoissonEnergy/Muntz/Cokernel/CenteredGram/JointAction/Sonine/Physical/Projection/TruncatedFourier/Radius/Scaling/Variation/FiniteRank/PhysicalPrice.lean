import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.TruncatedFourier.Radius.Scaling.Variation.FiniteRank.EvenSource
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.TruncatedFourier.Radius.Scaling.Variation.FiniteRank.MixedPrice
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace FixedWindowFourierReaction
open Complex MeasureTheory Set
open scoped InnerProductSpace

def originalW (coordinate : BurnolCompletedMellinCoordinate) : H := centeredOperator (1/4 : ℝ) (originalB coordinate)
def actualRadius (h : ℝ) : ℝ := (1/4 : ℝ)*Real.exp (h/2)
def actualOverlap (h : ℝ) : H →L[ℂ] H := burnolFixedWindowDilationOverlap
  (by norm_num : (0:ℝ)<1/4) (by norm_num : (0:ℝ)<1/4) h

def mixedReactionPrice (coordinate : BurnolCompletedMellinCoordinate) (r : ℝ) : ℂ :=
  2*inner ℂ (originalW coordinate) (originalW coordinate)+
    inner ℂ (originalB coordinate) (finiteReaction (1/4 : ℝ) r (originalB coordinate))-
    inner ℂ (centeredOperator r (originalB coordinate)-originalW coordinate)
      (centeredOperator r (originalB coordinate)-originalW coordinate)

theorem original_mixed_finite_price (coordinate : BurnolCompletedMellinCoordinate) (r : ℝ) (positive : 0<r) :
    inner ℂ (originalW coordinate) (centeredOperator r (originalB coordinate))+
      inner ℂ (centeredOperator r (originalB coordinate)) (originalW coordinate) = mixedReactionPrice coordinate r := by
  have polarization := mixed_square_price (centeredOperator (1/4 : ℝ)) (centeredOperator r) (originalB coordinate)
  have rightSquare : inner ℂ (centeredOperator r (originalB coordinate)) (centeredOperator r (originalB coordinate)) =
      inner ℂ (originalB coordinate) (centeredSquare r (originalB coordinate)) :=
    centered_even_pair r positive _ _ (centered_source_even coordinate r positive)
  have leftSquare : inner ℂ (originalW coordinate) (originalW coordinate) =
      inner ℂ (originalB coordinate) (centeredSquare (1/4 : ℝ) (originalB coordinate)) :=
    centered_even_pair (1/4 : ℝ) (by norm_num) _ _ (centered_source_even coordinate (1/4 : ℝ) (by norm_num))
  have reaction := congrArg (inner ℂ (originalB coordinate))
    (centered_square_finite (1/4 : ℝ) r (by norm_num) positive (originalB coordinate))
  simp only [squareDifference,sub_apply,inner_sub_right] at reaction
  change _+_ = _ at polarization
  unfold mixedReactionPrice originalW
  rw [rightSquare] at polarization
  rw [← reaction]
  change _ = _
  rw [← leftSquare]
  simp only [originalW] at *
  linear_combination polarization

theorem original_shell_even (coordinate : BurnolCompletedMellinCoordinate) :
    originalShell coordinate = burnolRieszSourceRawShell coordinate := by
  have fixed : reflectL2 (burnolRieszSourceRawShell coordinate) = burnolRieszSourceRawShell coordinate := by
    unfold burnolRieszSourceRawShell burnolQuarterZeroExtension
    rw [map_sub,← fourierL2_reflectL2_commute,burnolRadiusZeroExtension_reflect,burnolRadiusZeroExtension_reflect,
      burnolRieszSingleFourierSource_reflection_fixed,burnolRieszSingleFourierReturn_reflection_fixed]
  unfold originalShell burnolAmbientEvenPart
  rw [fixed]
  module

theorem original_shell_window_price (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) :
    inner ℂ (originalShell coordinate) (burnolMultiplicativeDilation h (originalShell coordinate)) =
      inner ℂ (originalB coordinate) (actualOverlap (-h) (originalB coordinate))+
      inner ℂ (originalW coordinate) (actualOverlap h (originalW coordinate))-
      inner ℂ (originalB coordinate) (burnolRechartedTruncatedFourierOperator (actualRadius (-h)) (originalW coordinate))-
      inner ℂ (originalW coordinate) (burnolRechartedTruncatedFourierOperator (actualRadius h) (originalB coordinate)) := by
  rw [original_shell_even,original_shell_pair_window]
  rw [show quarterChart (burnolQuarterRestriction (fourierL2 (burnolMultiplicativeDilation h
      (burnolRieszSourceRawShell coordinate)))) =
      actualOverlap (-h) (originalB coordinate)-
        burnolRechartedTruncatedFourierOperator (actualRadius (-h)) (originalW coordinate) by
    simp only [actualOverlap,originalW,originalB,actualRadius]
    rw [quarter_centered_chart,burnolRechartedTruncatedFourierOperator_of_pos (mul_pos (by norm_num) (Real.exp_pos _))]
    have source := burnolRieszSource_fourierWindowAction coordinate h
    rw [burnolRieszSingleFourierSource_reflection_fixed] at source
    exact source]
  rw [show quarterChart (burnolQuarterRestriction (burnolMultiplicativeDilation h
      (burnolRieszSourceRawShell coordinate))) =
      burnolRechartedTruncatedFourierOperator (actualRadius h) (originalB coordinate)-actualOverlap h (originalW coordinate) by
    simp only [actualOverlap,originalW,originalB,actualRadius]
    rw [quarter_centered_chart,burnolRechartedTruncatedFourierOperator_of_pos (mul_pos (by norm_num) (Real.exp_pos _))]
    exact burnolRieszSource_positionWindowAction coordinate h]
  rw [← quarter_centered_chart]
  simp only [inner_sub_right]
  simp only [originalW,originalB]
  ring

end FixedWindowFourierReaction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
