import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.CanonicalRaw.BoundaryTrace.Projection

/-! The original whole paired boundary identifies its unclamped gap with its actual constant mode. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace Topology
noncomputable section

def burnolProjectionGapRaw (value : BurnolL2) : ℂ :=
  burnolQuarterMeanCoefficient (burnolQuarterRestriction (burnolAmbientEvenPart value)) -
    burnolQuarterMeanCoefficient (burnolTruncatedFourier
      (burnolAmbientMeanZeroSecondCorrection value : BurnolQuarterIntervalL2))

theorem burnolEvenProjectionRaw_gap_read
    (value : BurnolL2) (raw : ℝ → ℂ) {x : ℝ}
    (inside : x ∈ symmetricInterval (1 / 4 : ℝ)) :
    burnolEvenProjectionRaw value raw x = burnolProjectionGapRaw value := by
  have negative : -x ∈ symmetricInterval (1 / 4 : ℝ) := by
    exact ⟨by linarith [inside.2], by linarith [inside.1]⟩
  unfold burnolEvenProjectionRaw burnolRawCorrectionRaw burnolEvenRaw
  simp only [indicator_of_mem inside, indicator_of_mem negative]
  unfold burnolFirstCorrectionRaw burnolPositionMeanZeroRaw burnolMeanZeroRaw
    burnolEvenRaw burnolMeanZeroFourierRaw burnolProjectionGapRaw
  simp only [neg_neg]
  ring

theorem burnolPairedBoundaryUnclampedRaw_gap_read
    (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) {x : ℝ}
    (inside : x ∈ symmetricInterval (1 / 4 : ℝ)) :
    burnolPairedBoundaryUnclampedRaw coordinate shift x =
      pairedMellinTranslationCharacter coordinate.value shift *
          burnolRieszStateQuarterInnerRaw coordinate -
        burnolProjectionGapRaw (pairedBurnolMultiplicativeDilation shift
          (burnolCompletedMellinRieszVector coordinate : BurnolL2)) := by
  unfold burnolPairedBoundaryUnclampedRaw
  rw [burnolRieszStateRaw_eq_quarterInner_of_mem coordinate inside,
    burnolEvenProjectionRaw_gap_read _ _ inside]

theorem burnolPairedBoundaryUnclampedRaw_quarter_eq_actual_zero
    (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (shift : ℝ) :
    burnolPairedBoundaryUnclampedRaw coordinate shift (1 / 4 : ℝ) =
      burnolPairedBoundaryRaw coordinate zero shift 0 := by
  let μq := (volume : Measure ℝ).restrict (symmetricInterval (1 / 4 : ℝ))
  have : NeBot (ae μq) := ae_neBot.mpr (by
    dsimp only [μq]
    intro empty
    have mass := Measure.restrict_eq_zero.mp empty
    norm_num [symmetricInterval, Real.volume_Icc] at mass)
  have same := ae_restrict_of_ae (s := symmetricInterval (1 / 4 : ℝ))
    ((burnolPairedBoundary_ae_unclampedRaw coordinate zero shift).symm.trans
      (burnolPairedBoundary_ae_raw coordinate zero shift))
  have fixed : ∀ᵐ x : ℝ ∂μq,
      burnolPairedBoundaryUnclampedRaw coordinate shift (1 / 4 : ℝ) =
        burnolPairedBoundaryRaw coordinate zero shift 0 := by
    filter_upwards [same, ae_restrict_mem (measurableSet_symmetricInterval (1 / 4 : ℝ))]
      with x read inside
    rw [burnolPairedBoundaryUnclampedRaw_gap_read coordinate shift inside,
      burnolPairedBoundaryRaw_quarterGap coordinate zero shift x
        (by simpa only [symmetricInterval, mem_Icc, abs_le] using inside)] at read
    rw [burnolPairedBoundaryUnclampedRaw_gap_read coordinate shift
      (by norm_num [symmetricInterval])]
    exact read
  obtain ⟨_, result⟩ := fixed.exists
  exact result

theorem burnolPairedBoundaryQuarterOuterRaw_sub_unclamped
    (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) :
    burnolPairedBoundaryQuarterOuterRaw coordinate shift -
        burnolPairedBoundaryUnclampedRaw coordinate shift (1 / 4 : ℝ) =
      pairedMellinTranslationCharacter coordinate.value shift *
        ((1 / 2 : ℂ) * ((1 / 4 : ℝ) : ℂ) ^ (-star coordinate.value) -
          star (burnolRadiusMellinGapMoment (1 / 4 : ℝ) coordinate.value) *
            star ((‖intervalConstant (1 / 4 : ℝ)‖ ^ 2 : ℂ)⁻¹) -
          (1 / 2 : ℂ) *
            (burnolMeanZeroFourierRaw (burnolRieszSingleFourierSource coordinate)
                (1 / 4 : ℝ) +
              burnolMeanZeroFourierRaw (burnolRieszSingleFourierSource coordinate)
                (-(1 / 4 : ℝ)))) -
        burnolEvenFirstCorrectionQuarterTrace
          (pairedBurnolMultiplicativeDilation shift
            (burnolCompletedMellinRieszVector coordinate : BurnolL2))
          (burnolRieszPairedDilationRaw coordinate shift) := by
  let value := pairedBurnolMultiplicativeDilation shift
    (burnolCompletedMellinRieszVector coordinate : BurnolL2)
  let raw := burnolRieszPairedDilationRaw coordinate shift
  let jump := (1 / 2 : ℂ) * ((1 / 4 : ℝ) : ℂ) ^ (-star coordinate.value) -
    star (burnolRadiusMellinGapMoment (1 / 4 : ℝ) coordinate.value) *
      star ((‖intervalConstant (1 / 4 : ℝ)‖ ^ 2 : ℂ)⁻¹) -
    (1 / 2 : ℂ) *
      (burnolMeanZeroFourierRaw (burnolRieszSingleFourierSource coordinate)
          (1 / 4 : ℝ) +
        burnolMeanZeroFourierRaw (burnolRieszSingleFourierSource coordinate)
          (-(1 / 4 : ℝ)))
  unfold burnolPairedBoundaryQuarterOuterRaw
    burnolPairedBoundaryUnclampedRaw
  change pairedMellinTranslationCharacter coordinate.value shift *
        burnolRieszStatePositiveOuterRaw coordinate (1 / 4 : ℝ) -
      burnolEvenProjectionQuarterOuterRaw value raw -
        (pairedMellinTranslationCharacter coordinate.value shift *
            burnolRieszStateRaw coordinate (1 / 4 : ℝ) -
          burnolEvenProjectionRaw value raw (1 / 4 : ℝ)) = _
  rw [burnolRieszStateRaw_eq_quarterInner coordinate]
  calc
    _ = pairedMellinTranslationCharacter coordinate.value shift *
          (burnolRieszStatePositiveOuterRaw coordinate (1 / 4 : ℝ) -
            burnolRieszStateQuarterInnerRaw coordinate) -
        (burnolEvenProjectionQuarterOuterRaw value raw -
          burnolEvenProjectionRaw value raw (1 / 4 : ℝ)) := by ring
    _ = pairedMellinTranslationCharacter coordinate.value shift * jump -
        burnolEvenFirstCorrectionQuarterTrace value raw := by
      rw [burnolRieszState_quarter_outer_sub_inner,
        burnolEvenProjectionQuarterOuterRaw_sub_projectionRaw]
    _ = _ := rfl

theorem burnolPairedBoundary_actual_joint_jump
    (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (shift : ℝ) :
    burnolPairedBoundaryQuarterOuterRaw coordinate shift -
        burnolPairedBoundaryRaw coordinate zero shift 0 =
      pairedMellinTranslationCharacter coordinate.value shift *
        (burnolRieszStatePositiveOuterRaw coordinate (1 / 4 : ℝ) -
          burnolRieszStateQuarterInnerRaw coordinate) -
      burnolEvenFirstCorrectionQuarterTrace
        (pairedBurnolMultiplicativeDilation shift
          (burnolCompletedMellinRieszVector coordinate : BurnolL2))
        (burnolRieszPairedDilationRaw coordinate shift) := by
  rw [← burnolPairedBoundaryUnclampedRaw_quarter_eq_actual_zero coordinate zero shift,
    burnolPairedBoundaryQuarterOuterRaw_sub_unclamped,
    burnolRieszState_quarter_outer_sub_inner]

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
