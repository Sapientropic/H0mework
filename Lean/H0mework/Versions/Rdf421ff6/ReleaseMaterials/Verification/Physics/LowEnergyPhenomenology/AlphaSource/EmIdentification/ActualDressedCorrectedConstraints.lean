import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedCorrectedGreen
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMDressedSchur

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedCorrectedGreen
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumPhysicalCharacteristic PreparationVacuumOriginalGreenFeedback
open PreparationVacuumCurrentSignalOperator
open ActualDressedFullCoulomb ActualDressedPhysicalRayNumerator ActualEMAction
open ActualEMDressedConstraint ActualEMDressedSchur
open scoped Matrix
attribute [local irreducible] physicalRayDenominator physicalRayNumerator physicalRayClearedPencil
  correctedResponse correctedDet sourceNull sourceNullLift sourceNullCoordinates sourceCokernel

/-- The original null initial directions retain their complete quantum action in the new pencil. -/
theorem actual_corrected_null_lift (event : DressedEvent) (e s sigma : ℝ) (n : PhysicalMomentum)
    (initial : Fin 9→ℂ) :
    physicalRayClearedPencil event e s sigma n*ᵥsourceNullLift (frequencyRay e s n) initial=
      -((sigma:ℂ) • (physicalRayNumerator event e s sigma n*ᵥ
        sourceNullLift (frequencyRay e s n) initial)) := by
  have original : originalJacobi (frequencyRay e s n)*ᵥsourceNullLift (frequencyRay e s n) initial=0 := by
    rw [←source_null_lift_fixed,Matrix.mulVec_mulVec,source_null_euler,Matrix.zero_mulVec]
  unfold physicalRayClearedPencil
  rw [Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.smul_mulVec,em_jacobi_source,original,smul_zero,zero_sub]

/-- All nine original cokernel rows return their actual quantum residual, for arbitrary full input. -/
theorem actual_corrected_constraint_rows (event : DressedEvent) (e s sigma : ℝ) (n : PhysicalMomentum)
    (a : SignalAmplitude) :
    sourceCokernel (frequencyRay e s n) (physicalRayClearedPencil event e s sigma n*ᵥa)=
      -((sigma:ℂ) • sourceCokernel (frequencyRay e s n) (physicalRayNumerator event e s sigma n*ᵥa)) := by
  have original : sourceCokernel (frequencyRay e s n) (emOriginalJacobi (frequencyRay e s n)*ᵥa)=0 := by
    rw [em_jacobi_source]
    exact (source_compatibility_nine _ _).mp (source_compatibility_euler _ a)
  unfold physicalRayClearedPencil
  rw [Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.smul_mulVec,map_sub,map_smul,map_smul,
    original,smul_zero,zero_sub]

theorem actual_corrected_kernel_nine (event : DressedEvent) (e s sigma : ℝ) (n : PhysicalMomentum)
    (positive : 0<sigma) (a : SignalAmplitude) (homogeneous : physicalRayClearedPencil event e s sigma n*ᵥa=0) :
    sourceCokernel (frequencyRay e s n) (physicalRayNumerator event e s sigma n*ᵥa)=0 := by
  have paid:=actual_corrected_constraint_rows event e s sigma n a
  rw [homogeneous,map_zero] at paid
  have zero : (sigma:ℂ) • sourceCokernel (frequencyRay e s n)
      (physicalRayNumerator event e s sigma n*ᵥa)=0 := neg_eq_zero.mp paid.symm
  exact (smul_eq_zero.mp zero).resolve_left (Complex.ofReal_ne_zero.mpr positive.ne')

/-- The generated response itself supplies the original initial coordinates; no null datum is erased. -/
theorem actual_corrected_response_initial (event : DressedEvent) (e s sigma : ℝ) (n : PhysicalMomentum)
    (forcing : SignalAmplitude) :
    sourceNullLift (frequencyRay e s n)
      (sourceNullCoordinates (frequencyRay e s n) (correctedResponse event e s sigma n forcing))=
      sourceNull (frequencyRay e s n)*ᵥcorrectedResponse event e s sigma n forcing :=
  source_null_coordinates_generated _ _

/-- Complete forcing and complete quantum correction jointly pay the same nine source rows. -/
theorem actual_corrected_response_nine (event : DressedEvent) (e s sigma : ℝ) (n : PhysicalMomentum)
    (positive : 0<sigma) (regular : correctedDet event e s sigma n≠0) (forcing : SignalAmplitude) :
    (sigma:ℂ) • sourceCokernel (frequencyRay e s n)
        (physicalRayNumerator event e s sigma n*ᵥcorrectedResponse event e s sigma n forcing)=
      -(physicalRayDenominator event e s sigma n • sourceCokernel (frequencyRay e s n) forcing) := by
  calc
    _=-(sourceCokernel (frequencyRay e s n)
        (physicalRayClearedPencil event e s sigma n*ᵥcorrectedResponse event e s sigma n forcing)) := by
      rw [actual_corrected_constraint_rows,neg_neg]
    _=_ := by rw [actual_corrected_response_cleared event e s sigma n positive regular forcing,map_smul]

end LowEnergy.GaussComposite.ActualDressedCorrectedGreen
