import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.PairedSharp

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2800000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKPairedBEulerJunctionSource OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.CompactPaired
open scoped Topology InnerProductSpace
open private poisson_scale from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.CompactPaired
open private poisson_dilation from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.KPaired
open private drive_weight_regular from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.PairedDrive
open private step family_integrable from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.WeightedProgram
open private forward_reflect from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountingJointEnergy
local notation "q" => (1 / 4 : ℝ)
local notation "h" => junctionShift
local notation "r" => junctionPoint
local notation "E" => burnolQuarterZeroExtension
local notation "Hq" => BurnolQuarterIntervalL2
local notation "H" => burnolUnitCountingPrimitiveL2
local notation "T" => burnolTateReciprocalL2
local notation "F" => fourierL2
local notation "K" => burnolCompletedMellinRieszVector
local notation "P" => burnolEvenAmbientProjection
local notation "Q" => pairedBurnolMultiplicativeDilation h

private theorem finite_program_paired (upper : ℝ) (f f' : ℝ → ℂ)
    (regular : ContinuousOn f' (Icc 4 upper)) :
    poissonPair (WeightedProgram.program 4 upper f f' H) =
      WeightedProgram.program 4 upper f f' (poissonPair H) := by
  simp only [WeightedProgram.program, map_sub, map_smul]
  rw [← poissonPair.integral_comp_comm (family_integrable 4 upper f' (by norm_num) regular H)]
  simp only [step, map_smul, map_sub, poisson_scale]

/-- The finite collar and its nonzero constant programme have the same actual Poisson-paired value. -/
theorem actual_paired_drive_value (c : BurnolCompletedMellinCoordinate) (i : Fin 2) :
    pairedDriveReverse c i = poissonPair (pairedDriveForward c i) := by
  have constant : poissonPair ConstantForward.value = ConstantDual.value := by
    change T (F ConstantForward.value) = ConstantDual.value
    rw [ConstantFourier.original_square, burnolTateReciprocalL2_involutive]
  rw [pairedDriveForward, map_add, map_smul, constant,
    finite_program_paired r⁻¹ _ _ (drive_weight_regular c i)]
  rfl

theorem actual_paired_correction_value (c : BurnolCompletedMellinCoordinate) (i : Fin 2) :
    pairedCorrectionReverse c i = poissonPair (pairedCorrectionForward c i) := by
  rw [pairedCorrectionForward, map_sub, ← actual_paired_drive_value]
  rfl

private theorem correction_forward_even (c : BurnolCompletedMellinCoordinate) (i : Fin 2) :
    reflectL2 (pairedCorrectionForward c i) = pairedCorrectionForward c i := by
  have even : reflectL2 (E (sourceCorrection c i : Hq)) = E (sourceCorrection c i : Hq) := by
    change reflectL2 (burnolRadiusZeroExtension q (sourceCorrection c i : Hq)) = _
    rw [burnolRadiusZeroExtension_reflect, source_correction_even]
    rfl
  have graph := actual_paired_correction_forward c i
  have reflected := (reflectL2.continuous.tendsto _).comp graph
  exact tendsto_nhds_unique (reflected.congr' (Eventually.of_forall (fun N => by
    dsimp only [Function.comp_apply]
    rw [forward_reflect, even]))) graph

private theorem poisson_fourier_poisson (value : BurnolL2) (even : reflectL2 value = value) :
    poissonPair (F (poissonPair value)) = F value := by
  change T (F (F (T (F value)))) = F value
  rw [fourierL2_fourierL2, burnolTateReciprocal_reflect, burnolTateReciprocalL2_involutive,
    ← fourierL2_reflectL2_commute, even]

private theorem poisson_paired (value : BurnolL2) : poissonPair (Q value) = Q (poissonPair value) := by
  change poissonPair ((1 / 2 : ℂ) •
    (burnolMultiplicativeDilation h value + burnolMultiplicativeDilation (-h) value)) = _
  rw [map_smul, map_add, poisson_dilation, poisson_dilation]
  rfl

theorem actual_paired_whole_correction_value (c : BurnolCompletedMellinCoordinate) :
    pairedWholeCorrectionReverse c = poissonPair (pairedWholeCorrectionForward c) := by
  rw [pairedWholeCorrectionForward, map_add, ← actual_paired_correction_value,
    actual_paired_correction_value c 1, poisson_fourier_poisson _ (correction_forward_even c 1)]
  rfl

/-- Both independently generated cotest values belong to the same source programme. -/
theorem actual_paired_cotest_value (c : BurnolCompletedMellinCoordinate) :
    pairedCotestReverse c = poissonPair (pairedCotestForward c) := by
  rw [pairedCotestForward, map_add, map_sub, map_smul, poisson_paired,
    ← actual_paired_whole_correction_value]
  rfl

private theorem cotest_forward_even (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) :
    reflectL2 (pairedCotestForward c) = pairedCotestForward c := by
  let theta : BurnolPaAmbientCarrier := star (pairedMellinTranslationCharacter c.value h) • K c - P (sourceAction c)
  have even : reflectL2 (theta : BurnolL2) = (theta : BurnolL2) :=
    mem_evenL2ClosedFace_iff.mp theta.property.2
  have graph := actual_paired_cotest_forward c zero
  change Tendsto (fun N : ℕ => FiniteForcing.source N (theta : BurnolL2)) atTop
    (𝓝 (pairedCotestForward c)) at graph
  have reflected := (reflectL2.continuous.tendsto _).comp graph
  exact tendsto_nhds_unique (reflected.congr' (Eventually.of_forall (fun N => by
    dsimp only [Function.comp_apply]
    rw [forward_reflect, even]))) graph

/-- The two actual sharp cotests have one complete common value, before either source price is read. -/
theorem actual_paired_cotest_common_value (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) :
    T (pairedCotestReverse c) = fourierL2.symm (pairedCotestForward c) := by
  rw [actual_paired_cotest_value]
  change T (T (F (pairedCotestForward c))) = _
  rw [burnolTateReciprocalL2_involutive]
  have source := congrArg fourierL2.symm (fourierL2_fourierL2 (pairedCotestForward c))
  rw [fourierL2.symm_apply_apply, cotest_forward_even c zero] at source
  exact source

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
