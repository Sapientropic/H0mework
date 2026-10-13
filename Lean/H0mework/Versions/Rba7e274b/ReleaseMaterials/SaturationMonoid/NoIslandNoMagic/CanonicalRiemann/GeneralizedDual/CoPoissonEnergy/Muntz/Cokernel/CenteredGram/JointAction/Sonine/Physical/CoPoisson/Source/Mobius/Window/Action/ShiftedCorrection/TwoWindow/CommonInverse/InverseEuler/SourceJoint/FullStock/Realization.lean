import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.TwoWindow.CommonInverse.InverseEuler.SourceJoint.FullStock.Consumer

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalCommonInverseForcing.SourceJoint.FullStock
open Complex
open scoped InnerProductSpace
local notation "P" => burnolEvenAmbientProjection
local notation "OP" => burnolCompactCoPoissonClosedRange.toSubmodule.orthogonal.starProjection
local instance realizationAmbientComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

theorem source_normalization_nonzero (h : ℝ) : 2*upperSeedFactor h≠0 := by
  unfold upperSeedFactor
  exact mul_ne_zero (by norm_num) (div_ne_zero (neg_ne_zero.mpr
    (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))) (by norm_num))

/-- The source owns every term of the complete original boundary. The wave is
actual Pa material; neither the full correction nor the two debts is erased. -/
def generatedBoundary (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) : BurnolPaAmbientCarrier :=
  (2*upperSeedFactor h)⁻¹ •
    ((2*upperSeedFactor h*(pairedMellinTranslationCharacter coordinate.value h-
      pairedMellinTranslationCharacter (star coordinate.value) h)) • burnolCompletedMellinRieszVector coordinate-
      upperSourceWaveAmbient coordinate h nonnegative bounded+P (upperSourceCorrection coordinate h)+
      upperSeedFactor h • meanDebt coordinate h)

def generatedOrthogonalBoundary (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) : BurnolPaAmbientCarrier :=
  (2*upperSeedFactor h)⁻¹ •
    ((2*upperSeedFactor h*(pairedMellinTranslationCharacter coordinate.value h-
      pairedMellinTranslationCharacter (star coordinate.value) h)) • burnolCompletedMellinRieszVector coordinate+
      OP (P (upperSourceCorrection coordinate h))+
      upperSeedFactor h • OP (meanDebt coordinate h))

theorem generated_boundary_realizes_original (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value=0) (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
    generatedBoundary coordinate h nonnegative bounded=burnolZeroPairedFixedAnnulusBoundary coordinate zero h := by
  unfold generatedBoundary
  rw [← actual_whole_boundary_source coordinate zero h nonnegative bounded,smul_smul,
    inv_mul_cancel₀ (source_normalization_nonzero h),one_smul]

theorem generated_orthogonal_boundary_realizes_original (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value=0) (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
    generatedOrthogonalBoundary coordinate h=
      OP (burnolZeroPairedFixedAnnulusBoundary coordinate zero h) := by
  unfold generatedOrthogonalBoundary
  rw [← actual_orthogonal_boundary_source coordinate zero h nonnegative bounded,smul_smul,
    inv_mul_cancel₀ (source_normalization_nonzero h),one_smul]

theorem generated_boundary_complete_projection (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value=0) (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
    OP (generatedBoundary coordinate h nonnegative bounded)=generatedOrthogonalBoundary coordinate h := by
  rw [generated_boundary_realizes_original coordinate zero h nonnegative bounded,
    generated_orthogonal_boundary_realizes_original coordinate zero h nonnegative bounded]

end OriginalCommonInverseForcing.SourceJoint.FullStock
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
