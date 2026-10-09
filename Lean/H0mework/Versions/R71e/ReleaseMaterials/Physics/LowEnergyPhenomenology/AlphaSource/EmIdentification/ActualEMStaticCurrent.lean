import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMStaticTensor
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMObservable

set_option autoImplicit false
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMCarrierOwn
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open Stage10 CanonicalGradedSpatialSource ProofFreeRicherAnholonomicSource
open ActualEMCurrentSplit ActualEMResponseSplit ActualEMObservable
open PreparationVacuumOriginalGreenFeedback PreparationVacuumFullOriginResponse
open PreparationVacuumStaticPoleResponse PreparationPhysicalStaticSpatialCouplingReturn
open PreparationPhysicalActualPhaseChargeReturn PreparationVacuumPhysicalQuantumLockedCharge
open PreparationVacuumElectromagneticIdentity PreparationVacuumPhysicalFeedback
open PreparationVacuumPhysicalCharacteristic Stage9C.Material.SpinPair
open Filter Set
open scoped Matrix BigOperators Topology Matrix.Norms.Operator
attribute [local irreducible] emInsertion fullNativeOrigin sourceGreen emStaticLimitTensor
  sourceSpatialStaticNativeField

/-- The original static EM tensor evaluated on the actual bare four-current at both ends. -/
def emBareStaticLimit (n : PhysicalMomentum) (sideD sideS : Fin 2) : ℂ :=
  (16/9:ℂ)*(ActionNormalization.phaseMomentum:ℂ)^2*
    dotProduct (emBareRestDirection sideD) (emStaticLimitTensor n*ᵥemBareRestDirection sideS)

/-- All four entries selected by the actual longitudinal bare currents remain, with their independent side signs. -/
theorem em_bare_static_limit_entries (n : PhysicalMomentum) (sideD sideS : Fin 2) :
    emBareStaticLimit n sideD sideS=(16/9:ℂ)*(ActionNormalization.phaseMomentum:ℂ)^2*
      (emStaticLimitTensor n 0 0+
       (sourceRestSign sideS:ℂ)*(lapse:ℂ)*emStaticLimitTensor n 0 3+
       (sourceRestSign sideD:ℂ)*(lapse:ℂ)*emStaticLimitTensor n 3 0+
       (sourceRestSign sideD:ℂ)*(sourceRestSign sideS:ℂ)*(lapse:ℂ)^2*emStaticLimitTensor n 3 3) := by
  simp [emBareStaticLimit,emBareRestDirection,Matrix.mulVec,dotProduct,Fin.sum_univ_four]
  ring_nf
  simp

private theorem em_static_tensor_tendsto (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    Tendsto (fun kappa : staticDomain=>emResponseTensor (sourceGreen (sourceSpatialStaticRegularPoint n unit kappa)))
      staticApproach (𝓝 (emStaticLimitTensor n)) := by
  apply tendsto_pi_nhds.mpr
  intro mu
  apply tendsto_pi_nhds.mpr
  intro nu
  simpa only [emResponseTensor,←em_static_green_original] using em_static_green_limit n unit mu nu

/-- The actual bare kernel has the finite source-generated static limit, including its spatial current. -/
theorem em_bare_static_limit (n : PhysicalMomentum) (unit : spatialSquare n=1) (sideD sideS : Fin 2) :
    Tendsto (fun kappa : staticDomain=>emBareChargeKernel
      (sourceGreen (sourceSpatialStaticRegularPoint n unit kappa)) sideD sideS)
      staticApproach (𝓝 (emBareStaticLimit n sideD sideS)) := by
  have cont : Continuous (fun M : Matrix (Fin 4) (Fin 4) ℂ=>
      (16/9:ℂ)*(ActionNormalization.phaseMomentum:ℂ)^2*
        dotProduct (emBareRestDirection sideD) (M*ᵥemBareRestDirection sideS)) :=
    continuous_const.mul (continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const))
  exact (cont.tendsto _).comp (em_static_tensor_tendsto n unit)

/-- The original charged/neutral source vertices consume this finite EM tensor with their generated charge product. -/
theorem em_bare_actual_static_limit (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (pointD pointS : BasePoint) (sideD edgeD sideS edgeS : Fin 2) :
    Tendsto (fun kappa : staticDomain=>emPureObservation
      (sourceGreen (sourceSpatialStaticRegularPoint n unit kappa))
      (actualRestNativeComplexForcingCovector pointD (sourceChargedRestIndex sideD edgeD)
        (sourceChargedRestIndex sideD edgeD))
      (actualRestNativeComplexForcingCovector pointS (sourceChargedRestIndex sideS edgeS)
        (sourceChargedRestIndex sideS edgeS))) staticApproach
      (𝓝 ((sourceActualPhaseCharge edgeD:ℂ)*(sourceActualPhaseCharge edgeS:ℂ)*emBareStaticLimit n sideD sideS)) := by
  simpa only [em_bare_pure_charge_product] using
    (tendsto_const_nhds (x:=(sourceActualPhaseCharge edgeD:ℂ)*(sourceActualPhaseCharge edgeS:ℂ))).mul
      (em_bare_static_limit n unit sideD sideS)

/-- The actual static density still contains both mixed terms and the full rest response. -/
theorem em_bare_static_charge_split (n : PhysicalMomentum) (unit : spatialSquare n=1) (kappa : staticDomain)
    (pointD pointS : BasePoint) (sideD edgeD sideS edgeS : Fin 2) :
    let G:=sourceGreen (sourceSpatialStaticRegularPoint n unit kappa)
    let fd:=actualRestNativeComplexForcingCovector pointD (sourceChargedRestIndex sideD edgeD) (sourceChargedRestIndex sideD edgeD)
    let fs:=actualRestNativeComplexForcingCovector pointS (sourceChargedRestIndex sideS edgeS) (sourceChargedRestIndex sideS edgeS)
    sourceRestFieldDensityRead pointD (sourceChargedRestIndex sideD edgeD,sourceChargedRestIndex sideD edgeD) (G*ᵥfs)=
      (sourceActualPhaseCharge edgeD:ℂ)*(sourceActualPhaseCharge edgeS:ℂ)*emBareChargeKernel G sideD sideS+
      emCurrentObservation G (emCurrentForce fd) (emCurrentResidual fs)+
      emCurrentObservation G (emCurrentResidual fd) (emCurrentForce fs)+
      emCurrentObservation G (emCurrentResidual fd) (emCurrentResidual fs) := by
  dsimp only
  rw [em_rest_density_four_parts (sourceGreen (sourceSpatialStaticRegularPoint n unit kappa)) pointD pointS
    (sourceChargedRestIndex sideD edgeD,sourceChargedRestIndex sideD edgeD)
    (sourceChargedRestIndex sideS edgeS,sourceChargedRestIndex sideS edgeS),em_bare_pure_charge_product]

private theorem em_static_origin_matrix : emInsertion.transpose*fullNativeOrigin=0 := by
  ext mu j
  have result:=em_origin_projection (Pi.single j (1:ℂ)) mu
  rw [Matrix.mulVec_mulVec,Matrix.mulVec_single_one] at result
  exact result

/-- The Coulomb source residue annihilates the literal EM component of every full source current. -/
theorem em_static_residue_em_source (f : Fin 289→ℂ) : staticResidue (emCurrentForce f)=0 := by
  have reflected : fullNativeOrigin.transpose*emInsertion=0 := by
    rw [←Matrix.transpose_transpose emInsertion,←Matrix.transpose_mul,em_static_origin_matrix,Matrix.transpose_zero]
  have source : fullNativeOrigin.transpose*ᵥemCurrentForce f=0 := by
    rw [em_current_force_insertion,Matrix.mulVec_mulVec,reflected,Matrix.zero_mulVec]
  rw [staticResidue,source,Matrix.mulVec_zero,Matrix.mulVec_zero]

/-- The original Coulomb pole observed on an EM detector end is zero for any full source forcing. -/
theorem em_static_residue_em_detector (fd fs : Fin 289→ℂ) :
    dotProduct (emCurrentForce fd) (staticResidue fs)=0 := by
  rw [em_current_force_insertion,dotProduct_comm,←Matrix.dotProduct_transpose_mulVec]
  rw [staticResidue,Matrix.mulVec_mulVec,em_static_origin_matrix,Matrix.zero_mulVec,dotProduct_zero]

/-- The complete Coulomb coefficient is generated wholly by the two residual currents; cross terms are kept at finite momentum. -/
theorem em_static_residue_rest_pair (fd fs : Fin 289→ℂ) :
    dotProduct fd (staticResidue fs)=
      dotProduct (emCurrentResidual fd) (staticResidue (emCurrentResidual fs)) := by
  have source : staticResidue (emCurrentResidual fs)=staticResidue fs := by
    simp only [emCurrentResidual,staticResidue,Matrix.mulVec_sub]
    have zero:=em_static_residue_em_source fs
    change staticResidue fs-staticResidue (emCurrentForce fs)=staticResidue fs
    rw [zero,sub_zero]
  rw [source,emCurrentResidual,sub_dotProduct,em_static_residue_em_detector,sub_zero]

/-- The original full static Green delivers its source-fixed Coulomb coefficient to the remaining current pair. -/
theorem em_full_static_coulomb_rest_pair (n : PhysicalMomentum) (unit : spatialSquare n=1) (fd fs : Fin 289→ℂ) :
    Tendsto (fun kappa : staticDomain=>(-(kappa.val:ℂ)^2)*
      emCurrentObservation (sourceGreen (sourceSpatialStaticRegularPoint n unit kappa)) fd fs)
      staticApproach (𝓝 (dotProduct (emCurrentResidual fd) (staticResidue (emCurrentResidual fs)))) := by
  have cont : Continuous (fun V : Fin 289→ℂ=>dotProduct fd V) := continuous_const.dotProduct continuous_id
  have result:=(cont.tendsto _).comp (sourceSpatialStaticNativeFieldResidue n unit fs)
  rw [em_static_residue_rest_pair fd fs] at result
  simpa only [Function.comp_def,dotProduct_smul,smul_eq_mul,sourceSpatialStaticNativeField,
    PreparationVacuumOriginalGreenFeedback.sourceField,emCurrentObservation] using result

end LowEnergy.GaussComposite.ActualEMCarrierOwn
