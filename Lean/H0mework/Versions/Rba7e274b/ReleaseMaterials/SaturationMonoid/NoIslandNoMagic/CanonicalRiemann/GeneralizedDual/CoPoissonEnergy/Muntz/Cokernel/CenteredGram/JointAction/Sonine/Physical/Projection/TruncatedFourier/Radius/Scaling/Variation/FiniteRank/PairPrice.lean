import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.TruncatedFourier.Radius.Scaling.Variation.FiniteRank.PhysicalPrice
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace FixedWindowFourierReaction
open Complex MeasureTheory Set
open scoped InnerProductSpace

theorem originalW_chart (coordinate : BurnolCompletedMellinCoordinate) : originalW coordinate =
    quarterChart (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate) : BurnolQuarterIntervalL2) :=
  quarter_centered_chart _
theorem originalW_Q (coordinate : BurnolCompletedMellinCoordinate) : Q (originalW coordinate) = originalW coordinate := by
  rw [originalW_chart,← quarter_projection_chart]
  exact congrArg quarterChart (Submodule.starProjection_eq_self_iff.mpr
    (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate)).property)
theorem originalW_even (coordinate : BurnolCompletedMellinCoordinate) :
    reflectRestricted 1 (originalW coordinate) = originalW coordinate :=
  centered_source_even coordinate (1/4 : ℝ) (by norm_num)

theorem original_cross_centered (coordinate : BurnolCompletedMellinCoordinate) (r : ℝ) :
    inner ℂ (originalW coordinate) (burnolRechartedTruncatedFourierOperator r (originalB coordinate)) =
      inner ℂ (originalW coordinate) (centeredOperator r (originalB coordinate)) := by
  unfold centeredOperator
  simp only [ContinuousLinearMap.comp_apply]
  rw [original_source_Q]
  have pair : inner ℂ (Q (originalW coordinate)) (burnolRechartedTruncatedFourierOperator r (originalB coordinate)) =
      inner ℂ (originalW coordinate) (Q (burnolRechartedTruncatedFourierOperator r (originalB coordinate))) :=
    Q_symmetric _ _
  rw [originalW_Q] at pair
  exact pair

theorem original_other_cross_centered (coordinate : BurnolCompletedMellinCoordinate) (r : ℝ) (positive : 0<r) :
    inner ℂ (originalB coordinate) (burnolRechartedTruncatedFourierOperator r (originalW coordinate)) =
      inner ℂ (centeredOperator r (originalB coordinate)) (originalW coordinate) := by
  have pair := recharted_even_pair r positive (originalB coordinate) (originalW coordinate) (originalW_even coordinate)
  have project : inner ℂ (Q (burnolRechartedTruncatedFourierOperator r (originalB coordinate))) (originalW coordinate) =
      inner ℂ (burnolRechartedTruncatedFourierOperator r (originalB coordinate)) (Q (originalW coordinate)) :=
    Q_symmetric _ _
  rw [originalW_Q] at project
  unfold centeredOperator
  simp only [ContinuousLinearMap.comp_apply]
  rw [original_source_Q,project]
  exact pair.symm

def pairedShellPrice (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
  inner ℂ (originalB coordinate) (actualOverlap (-h) (originalB coordinate))+
  inner ℂ (originalW coordinate) (actualOverlap h (originalW coordinate))+
  inner ℂ (originalB coordinate) (actualOverlap h (originalB coordinate))+
  inner ℂ (originalW coordinate) (actualOverlap (-h) (originalW coordinate))-
  mixedReactionPrice coordinate (actualRadius h)-mixedReactionPrice coordinate (actualRadius (-h))

theorem original_paired_shell_finite_price (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) :
    inner ℂ (originalShell coordinate) (burnolMultiplicativeDilation h (originalShell coordinate))+
      inner ℂ (originalShell coordinate) (burnolMultiplicativeDilation (-h) (originalShell coordinate)) =
      pairedShellPrice coordinate h := by
  rw [original_shell_window_price,original_shell_window_price]
  simp only [neg_neg]
  rw [original_cross_centered,original_cross_centered,
    original_other_cross_centered coordinate (actualRadius h) (mul_pos (by norm_num) (Real.exp_pos _)),
    original_other_cross_centered coordinate (actualRadius (-h)) (mul_pos (by norm_num) (Real.exp_pos _))]
  unfold pairedShellPrice
  rw [← original_mixed_finite_price coordinate (actualRadius h) (mul_pos (by norm_num) (Real.exp_pos _)),
    ← original_mixed_finite_price coordinate (actualRadius (-h)) (mul_pos (by norm_num) (Real.exp_pos _))]
  ring

def originalPairedPrice (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) (increment : BurnolL2) : ℂ :=
  inner ℂ (burnolCompletedMellinRieszVector coordinate : BurnolL2) (burnolMultiplicativeDilation h (gapTail coordinate))+
  inner ℂ (burnolCompletedMellinRieszVector coordinate : BurnolL2) (burnolMultiplicativeDilation (-h) (gapTail coordinate))-
  inner ℂ (gapTail coordinate) (burnolMultiplicativeDilation h (originalShell coordinate))-
  inner ℂ (gapTail coordinate) (burnolMultiplicativeDilation (-h) (originalShell coordinate))+
  pairedShellPrice coordinate h+
  inner ℂ (burnolCompletedMellinRieszVector coordinate : BurnolL2) (burnolMultiplicativeDilation h increment)+
  inner ℂ (burnolCompletedMellinRieszVector coordinate : BurnolL2) (burnolMultiplicativeDilation (-h) increment)

-- Two finite reactions alter the physical paired price; the outside source and actual increment stay visible.
theorem original_paired_finite_price (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) (increment : BurnolL2) :
    inner ℂ (burnolCompletedMellinRieszVector coordinate : BurnolL2)
      (burnolMultiplicativeDilation h ((burnolCompletedMellinRieszVector coordinate : BurnolL2)+increment))+
    inner ℂ (burnolCompletedMellinRieszVector coordinate : BurnolL2)
      (burnolMultiplicativeDilation (-h) ((burnolCompletedMellinRieszVector coordinate : BurnolL2)+increment)) =
      originalPairedPrice coordinate h increment := by
  rw [original_actual_price,original_actual_price]
  have shell := original_paired_shell_finite_price coordinate h
  unfold originalPairedPrice
  linear_combination shell

end FixedWindowFourierReaction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
