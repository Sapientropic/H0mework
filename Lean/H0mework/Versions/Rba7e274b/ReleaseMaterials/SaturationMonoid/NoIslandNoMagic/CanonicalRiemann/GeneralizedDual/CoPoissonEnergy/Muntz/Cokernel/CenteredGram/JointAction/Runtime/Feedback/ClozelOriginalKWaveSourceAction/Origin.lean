import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKWaveSourceAction.Effect
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
open BurnolPhysicalState OriginalRieszFinitePairing OriginalPaPhysicalGreen
local notation "q" => (1 / 4 : ℝ)

/-- The actual primitive source pays the original position contact; the Fourier contact is the same original beta endpoint. -/
theorem actual_original_wave_source_contacts (coordinate : BurnolCompletedMellinCoordinate) :
    positionSource coordinate q = -OriginalRieszSource.Kernel.A coordinate ∧
    burnolRieszSingleFourierSourceRaw coordinate q = OriginalRieszSource.Kernel.beta coordinate := by
  have source := OriginalRieszSource.GapEuler.gapMean_primitive q (by norm_num) coordinate
  constructor
  · unfold positionSource OriginalRieszSource.Kernel.A
    linear_combination -source
  · rfl

theorem actual_original_wave_source_origin_inventory (coordinate : BurnolCompletedMellinCoordinate) :
    (q : ℂ) * actualPositionBandDensity coordinate q =
      -(q : ℂ) ^ coordinate.value * OriginalRieszSource.Kernel.A coordinate ∧
    (q : ℂ) * actualFourierBandDensity coordinate q =
      (q : ℂ) ^ (1 - coordinate.value) * OriginalRieszSource.Kernel.beta coordinate := by
  have source := actual_original_wave_source_contacts coordinate
  have positionPower : (q : ℂ) * (q : ℂ) ^ (coordinate.value - 1) = (q : ℂ) ^ coordinate.value := by
    conv_rhs => rw [show coordinate.value = (coordinate.value - 1) + 1 by ring,
      Complex.cpow_add _ _ (by norm_num : (q : ℂ) ≠ 0), Complex.cpow_one]
    ring
  have fourierPower : (q : ℂ) * (q : ℂ) ^ (-coordinate.value) = (q : ℂ) ^ (1 - coordinate.value) := by
    conv_rhs => rw [show 1 - coordinate.value = -coordinate.value + 1 by ring,
      Complex.cpow_add _ _ (by norm_num : (q : ℂ) ≠ 0), Complex.cpow_one]
    ring
  unfold actualPositionBandDensity actualFourierBandDensity
  rw [source.1, source.2]
  constructor
  · calc
      _ = -((q : ℂ) * (q : ℂ) ^ (coordinate.value - 1)) * OriginalRieszSource.Kernel.A coordinate := by ring
      _ = _ := by rw [positionPower]
  · rw [← mul_assoc, fourierPower]

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half

/-- Both source actions cannot disappear together: the same evaluator-generated kernel paid its determinant before these endpoint readouts. No sign of their sum is supplied. -/
theorem actual_original_wave_joint_origin_action_not_erased :
    ¬((q : ℂ) * actualPositionBandDensity c q = 0 ∧
      (q : ℂ) * actualFourierBandDensity c q = 0) := by
  intro erased
  have source := actual_original_wave_source_origin_inventory c
  rw [source.1, source.2] at erased
  have positionUnit : (q : ℂ) ^ (c).value ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have fourierUnit : (q : ℂ) ^ (1 - (c).value) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have positionZero : OriginalRieszSource.Kernel.A c = 0 :=
    (mul_eq_zero.mp erased.1).resolve_left (neg_ne_zero.mpr positionUnit)
  have fourierZero : OriginalRieszSource.Kernel.beta c = 0 :=
    (mul_eq_zero.mp erased.2).resolve_left fourierUnit
  have oldUnit := OriginalKCharacterActionSource.actual_original_common_determinant_ne_zero observation nontrivial half
  apply oldUnit
  unfold OriginalKCommonGapKernelSource.actualCommonDeterminant
  rw [positionZero, fourierZero]
  ring

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWaveSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
