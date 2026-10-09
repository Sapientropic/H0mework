import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMCurrentSplit
import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceRestFieldPoleTensor

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMResponseSplit
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open Stage10 CanonicalGradedSpatialSource
open ProofFreeRicherAnholonomicSource
open ActualEMCarrierOwn ActualEMCurrentSplit
open PreparationVacuumElectromagneticIdentity PreparationVacuumPhysicalFeedback
open PreparationPhysicalActualGaussChargeCurrent PreparationPhysicalCommonCurrentStaticRead
open PreparationPhysicalNativePhotonFluxReturn
open scoped Matrix BigOperators Topology

/-- The physical EM tensor is a restriction of the same complete source field response. -/
def emResponseTensor (G : Matrix (Fin 289) (Fin 289) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  emInsertion.transpose*G*emInsertion

def emCurrentObservation (G : Matrix (Fin 289) (Fin 289) ℂ) (fd fs : Fin 289→ℂ) : ℂ :=
  dotProduct fd (G*ᵥfs)

def emPureObservation (G : Matrix (Fin 289) (Fin 289) ℂ) (fd fs : Fin 289→ℂ) : ℂ :=
  dotProduct (emCoordinateCurrent fd) (emResponseTensor G*ᵥemCoordinateCurrent fs)

/-- Dual coordinates exactly compensate the literal three-slot Gram; no kinetic normalization is inserted. -/
theorem em_pure_response_tensor (G : Matrix (Fin 289) (Fin 289) ℂ) (fd fs : Fin 289→ℂ) :
    emCurrentObservation G (emCurrentForce fd) (emCurrentForce fs)=emPureObservation G fd fs := by
  unfold emCurrentObservation emPureObservation emResponseTensor
  rw [em_current_force_insertion,em_current_force_insertion]
  rw [dotProduct_comm (emInsertion*ᵥemCoordinateCurrent fd),←Matrix.dotProduct_transpose_mulVec]
  simp only [Matrix.mulVec_mulVec,Matrix.mul_assoc]

/-- The two actual currents retain all four source-generated response terms. -/
theorem em_response_four_parts (G : Matrix (Fin 289) (Fin 289) ℂ) (fd fs : Fin 289→ℂ) :
    emCurrentObservation G fd fs=
      emPureObservation G fd fs+
      emCurrentObservation G (emCurrentForce fd) (emCurrentResidual fs)+
      emCurrentObservation G (emCurrentResidual fd) (emCurrentForce fs)+
      emCurrentObservation G (emCurrentResidual fd) (emCurrentResidual fs) := by
  unfold emCurrentObservation
  conv_lhs=>rw [em_current_complete fd,em_current_complete fs,Matrix.mulVec_add,
    add_dotProduct,dotProduct_add,dotProduct_add]
  rw [show dotProduct (emCurrentForce fd) (G*ᵥemCurrentForce fs)=emPureObservation G fd fs from
    em_pure_response_tensor G fd fs]
  ring

/-- The original full289 rest-density reader consumes the literal EM tensor and all remaining terms. -/
theorem em_rest_density_four_parts (G : Matrix (Fin 289) (Fin 289) ℂ)
    (pointD pointS : BasePoint) (reader driver : RestPairIndex) :
    sourceRestFieldDensityRead pointD reader
      (G*ᵥactualRestNativeComplexForcingCovector pointS driver.1 driver.2)=
      emPureObservation G
        (actualRestNativeComplexForcingCovector pointD reader.1 reader.2)
        (actualRestNativeComplexForcingCovector pointS driver.1 driver.2)+
      emCurrentObservation G
        (emCurrentForce (actualRestNativeComplexForcingCovector pointD reader.1 reader.2))
        (emCurrentResidual (actualRestNativeComplexForcingCovector pointS driver.1 driver.2))+
      emCurrentObservation G
        (emCurrentResidual (actualRestNativeComplexForcingCovector pointD reader.1 reader.2))
        (emCurrentForce (actualRestNativeComplexForcingCovector pointS driver.1 driver.2))+
      emCurrentObservation G
        (emCurrentResidual (actualRestNativeComplexForcingCovector pointD reader.1 reader.2))
        (emCurrentResidual (actualRestNativeComplexForcingCovector pointS driver.1 driver.2)) := by
  rw [sourceRestFieldDensityRead_generated]
  exact em_response_four_parts G _ _

/-- Both independently prepared original currents use the same four-piece carrier. -/
theorem em_prepared_response_four_parts (G : Matrix (Fin 289) (Fin 289) ℂ)
    (qd : PhysicalResponsePoint) (pDL pDR : PhysicalMomentum) (dSL dEL dSR dER : Fin 2)
    (lambda : ℂ) (T : ℝ) (qs : PhysicalResponsePoint) (pSL pSR : PhysicalMomentum)
    (sSL sEL sSR sER : Fin 2) (mu : ℂ) (S : ℝ) :
    sourceActualPreparedDetector qd pDL pDR dSL dEL dSR dER lambda T
      (G*ᵥsourceActualPreparedCurrent qs pSL pSR sSL sEL sSR sER mu S)=
      emPureObservation G
        (sourceActualPreparedCurrent qd pDL pDR dSL dEL dSR dER lambda T)
        (sourceActualPreparedCurrent qs pSL pSR sSL sEL sSR sER mu S)+
      emCurrentObservation G
        (emCurrentForce (sourceActualPreparedCurrent qd pDL pDR dSL dEL dSR dER lambda T))
        (emCurrentResidual (sourceActualPreparedCurrent qs pSL pSR sSL sEL sSR sER mu S))+
      emCurrentObservation G
        (emCurrentResidual (sourceActualPreparedCurrent qd pDL pDR dSL dEL dSR dER lambda T))
        (emCurrentForce (sourceActualPreparedCurrent qs pSL pSR sSL sEL sSR sER mu S))+
      emCurrentObservation G
        (emCurrentResidual (sourceActualPreparedCurrent qd pDL pDR dSL dEL dSR dER lambda T))
        (emCurrentResidual (sourceActualPreparedCurrent qs pSL pSR sSL sEL sSR sER mu S)) := by
  rw [sourceActualPreparedDetector_current]
  exact em_response_four_parts G _ _

/-- The EM piece of the original full Green is the original four-current propagator. -/
theorem em_fullGreen_tensor (epsilon s : ℝ) (n : PhysicalMomentum) :
    emResponseTensor (sourceWholePhotonGreen epsilon s n)=emPropagator epsilon s n := rfl

/-- The EM piece of the original sheet residue is the original physical insertion tensor. -/
theorem em_residue_tensor (epsilon s : ℝ) (n : PhysicalMomentum) :
    emResponseTensor (sourceWholePhotonResidue epsilon s n)=emPoleTensor epsilon s n := rfl

end LowEnergy.GaussComposite.ActualEMResponseSplit
