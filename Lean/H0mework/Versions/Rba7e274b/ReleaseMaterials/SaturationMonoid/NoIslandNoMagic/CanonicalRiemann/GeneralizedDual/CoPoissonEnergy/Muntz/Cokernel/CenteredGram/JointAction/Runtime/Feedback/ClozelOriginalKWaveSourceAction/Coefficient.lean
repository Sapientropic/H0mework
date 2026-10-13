import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKWaveSourceAction.Recovery
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWaveSourceAction
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalRieszFinitePairing OriginalRieszFiniteColumns OriginalPaPhysicalGreen

def actualUpperWaveWindowSource (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) : BurnolL2 :=
  OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h •
    (originalPhysicalCutoff 4 (CoPoisson.positionSeed coordinate h) +
      burnolTateReciprocalL2 (originalPhysicalCutoff 4 (CoPoisson.fourierSeed coordinate h)))

theorem actual_original_upper_wave_complete_source (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    burnolMobiusSourceL2 (OriginalCommonInverseForcing.SourceJoint.upperSourceWaveAmbient
      coordinate h nonnegative bounded) = actualUpperWaveWindowSource coordinate h := by
  have windows := actual_original_wave_source_windows coordinate h nonnegative bounded
  have position : burnolMobiusSourceL2 (actualPositionWaveAmbient coordinate h nonnegative bounded) =
      originalPhysicalCutoff 4 (CoPoisson.positionSeed coordinate h) := by
    unfold burnolMobiusSourceL2
    change burnolRadiusZeroExtension 4 (burnolMobiusWindowSourceRead _) = _
    rw [windows.1]
    rfl
  have fourier : burnolMobiusSourceL2 (actualFourierWaveAmbient coordinate h nonnegative bounded) =
      originalPhysicalCutoff 4 (CoPoisson.fourierSeed coordinate h) := by
    unfold burnolMobiusSourceL2
    change burnolRadiusZeroExtension 4 (burnolMobiusWindowSourceRead _) = _
    rw [windows.2]
    rfl
  have inPa : actualFourierWaveAmbient coordinate h nonnegative bounded ∈ burnolCompactCoPoissonClosedRange := by
    obtain ⟨physical, member, actual⟩ := Submodule.mem_map.mp
      (CoPoisson.fourierWave_inPa coordinate h nonnegative bounded)
    have same : physical = actualFourierWaveAmbient coordinate h nonnegative bounded := Subtype.ext actual
    rwa [← same]
  have combined : OriginalCommonInverseForcing.SourceJoint.upperSourceWaveAmbient coordinate h nonnegative bounded =
      OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h •
        (actualPositionWaveAmbient coordinate h nonnegative bounded +
          evenFaceFourierEquiv burnolUnscaledCommonGapRadius
            (actualFourierWaveAmbient coordinate h nonnegative bounded)) := by
    apply Subtype.ext
    rfl
  rw [combined, map_smul, map_add, burnolMobiusSource_fourier _ inPa, position, fourier]
  rfl

/-- The coefficient consumes the original weighted source action before taking its dependent Mellin face. -/
theorem actual_original_upper_wave_coefficient_action (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    burnolPaResolventSourceCoefficient coordinate
      (OriginalCommonInverseForcing.SourceJoint.upperSourceWaveAmbient coordinate h nonnegative bounded) =
      (2 : ℂ) * OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h *
        burnolMellinTailEvaluator coordinate.value coordinate.rightHalf
          (burnolTateReciprocalL2 (originalPhysicalCutoff 4 (CoPoisson.positionSeed coordinate h)) +
            originalPhysicalCutoff 4 (CoPoisson.fourierSeed coordinate h)) := by
  change (2 : ℂ) * burnolMellinTailEvaluator coordinate.value coordinate.rightHalf
    (burnolTateReciprocalL2 (burnolMobiusSourceL2 _)) = _
  rw [actual_original_upper_wave_complete_source]
  unfold actualUpperWaveWindowSource
  rw [map_smul, map_add, burnolTateReciprocalL2_involutive, map_smul]
  ring

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWaveSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
