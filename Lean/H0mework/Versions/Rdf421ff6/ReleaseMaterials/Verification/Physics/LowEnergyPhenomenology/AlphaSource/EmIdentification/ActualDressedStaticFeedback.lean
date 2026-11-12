import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNoetherCoulombCoefficient
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualWholeStaticUniform

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedStaticFeedback
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationVacuumOriginalGreenFeedback PreparationPhysicalVoltageCompleteReturn
open PreparationPhysicalStaticSpatialCouplingReturn PreparationVacuumStaticPoleResponse
open ActualDressedFullCoulomb ActualDressedFrequencyHalf ActualDressedCorrectedGreen
open ActualEMDressedConstraint ActualEMDressedSchur ActualEMAction ActualCompositeFieldCurrent
open ActualDressedCorrectedElectronRead ActualDressedOrderedStatic ActualWholeStatic Filter Set
open scoped Matrix BigOperators Topology
attribute [local irreducible] sourceGreen sourceNull sourceNullLift sourceNullCoordinates
  frequencyResponsePencil correctedResponse

/-- The physical spatial ray is the original source Fourier momentum at kappa=epsilon squared. -/
theorem actual_static_ray (eps : ℝ) (n : PhysicalMomentum) :
    frequencyRay eps 0 n=sourceStaticSpatialMomentum n (eps^2) := by
  ext i
  fin_cases i <;> simp [frequencyRay,physicalFrequencyMomentum,sourceStaticSpatialMomentum] <;> rfl

private theorem original_feedback_return (p : regularSource) (Q : Matrix (Fin 289) (Fin 289) ℂ)
    (forcing a : Fin 289→ℂ) (equation : (originalJacobi p.val-Q)*ᵥa=forcing) :
    a=sourceGreen p*ᵥforcing+sourceGreen p*ᵥ(Q*ᵥa)+
      sourceNullLift p.val (sourceNullCoordinates p.val a) := by
  have original : sourceGreen p*originalJacobi p.val=1-sourceNull p.val := by
    simpa only [sourceNull] using sourceGreen_original_left p
  have paid:=congrArg (fun v=>sourceGreen p*ᵥv) equation
  rw [Matrix.sub_mulVec,Matrix.mulVec_sub,Matrix.mulVec_mulVec,original,
    Matrix.sub_mulVec,Matrix.one_mulVec] at paid
  rw [source_null_coordinates_generated]
  linear_combination paid

/-- The full corrected field generates its original feedback and all nine null coordinates without a feedback inverse premise. -/
theorem actual_corrected_static_feedback (event : DressedEvent) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (kappa : staticDomain) (sigma : ℝ) (positive : 0<sigma)
    (regular : correctedDet event (Real.sqrt kappa.val) 0 sigma n≠0) (forcing : Fin 289→ℂ) :
    correctedResponse event (Real.sqrt kappa.val) 0 sigma n forcing=
      sourceGreen (sourceSpatialStaticRegularPoint n unit kappa)*ᵥforcing+
      sourceGreen (sourceSpatialStaticRegularPoint n unit kappa)*ᵥ
        (frequencyQuantumCorrection event (kappa.val • n) (sourceStaticSpatialMomentum n kappa.val)
          (dampedFourierClock 0 sigma)*ᵥcorrectedResponse event (Real.sqrt kappa.val) 0 sigma n forcing)+
      sourceNullLift (sourceStaticSpatialMomentum n kappa.val)
        (sourceNullCoordinates (sourceStaticSpatialMomentum n kappa.val)
          (correctedResponse event (Real.sqrt kappa.val) 0 sigma n forcing)) := by
  have equation:=actual_corrected_response_equation event (Real.sqrt kappa.val) 0 sigma n positive regular forcing
  rw [frequencyResponsePencil,em_jacobi_source,actual_static_ray,Real.sq_sqrt kappa.property.1.le] at equation
  simp only [sourceFrequency,mul_zero] at equation
  exact original_feedback_return (sourceSpatialStaticRegularPoint n unit kappa) _ _ _ equation

/-- Complete forcing and feedback obey the original nine rows; contact/deviation contributions stay in the source cokernel. -/
theorem actual_corrected_static_nine (event : DressedEvent) (n : PhysicalMomentum)
    (kappa : staticDomain) (sigma : ℝ) (positive : 0<sigma)
    (regular : correctedDet event (Real.sqrt kappa.val) 0 sigma n≠0) (forcing : Fin 289→ℂ) :
    sourceCokernel (sourceStaticSpatialMomentum n kappa.val)
      (forcing+frequencyQuantumCorrection event (kappa.val • n) (sourceStaticSpatialMomentum n kappa.val)
        (dampedFourierClock 0 sigma)*ᵥcorrectedResponse event (Real.sqrt kappa.val) 0 sigma n forcing)=0 := by
  have equation:=actual_corrected_response_equation event (Real.sqrt kappa.val) 0 sigma n positive regular forcing
  rw [frequencyResponsePencil,em_jacobi_source,actual_static_ray,Real.sq_sqrt kappa.property.1.le] at equation
  simp only [sourceFrequency,mul_zero] at equation
  have returned : forcing+frequencyQuantumCorrection event (kappa.val • n) (sourceStaticSpatialMomentum n kappa.val)
      (dampedFourierClock 0 sigma)*ᵥcorrectedResponse event (Real.sqrt kappa.val) 0 sigma n forcing=
      originalJacobi (sourceStaticSpatialMomentum n kappa.val)*ᵥcorrectedResponse event (Real.sqrt kappa.val) 0 sigma n forcing := by
    rw [Matrix.sub_mulVec] at equation
    linear_combination -equation
  rw [returned]
  exact (source_compatibility_nine _ _).mp (source_compatibility_euler _ _)

end LowEnergy.GaussComposite.ActualDressedStaticFeedback
