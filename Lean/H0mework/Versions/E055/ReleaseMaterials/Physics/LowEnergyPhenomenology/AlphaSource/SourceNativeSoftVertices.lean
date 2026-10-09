import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceNativeSoftCoefficients
import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceNativePoleNoetherReturn

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalChargedSoftObservable
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum FullSpace
open PreparationPhysicalNormalizedFullField PreparationPhysicalChargedEnergyVariation
open PreparationPhysicalChargedEnergyPoleReturn PreparationPhysicalChargedPacketQuantumReturn
open PreparationPhysicalChargedPacketVoltage PreparationVacuumVoltageGaussGreen
open PreparationVacuumSourceFieldFamily PreparationVacuumActionFieldLift
open PreparationVacuumActualFieldQuantization PreparationVacuumNonlinearFieldCurve
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPhysicalChargedFieldFactor
open PreparationVacuumChargedLongRangeRead PreparationVacuumCausalPoleResponse
open PreparationVacuumChargedSpatialResponse PreparationVacuumNativeSlowCoupling
open PreparationVacuumFullSlowFieldResponse PreparationVacuumQuantumSlowResidue
open PreparationVacuumPhysicalFeedback PreparationVacuumChargedPacketGreen
open PreparationVacuumPhysicalQuantumLockedCharge PreparationVacuumElectromagneticIdentity
open CanonicalGradedSpatialSource FullQuantum.CoframeResponse FullQuantum.StateGreen
open GaussHistoryHilbert PreparationVacuumStaticVoltageSource
open MeasureTheory Filter
open scoped BigOperators Matrix Topology InnerProductSpace
local instance chargedSoftVerticesQuantumIndex : DecidableEq Quantum.Index:=Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder

open Stage10 DiracCliffordRepresentation DiracExteriorMatterAction YangMills.FullPairing
open PreparationPhysicalEnergyWeightsReturn PreparationPhysicalFilteredChargeVoltage
open PreparationPhysicalVoltageEnergyIdentity

open PreparationPhysicalEnergyPoleChargeReturn
open Stage9C.Material.SpinPair ProofFreeRicherAnholonomicSource StageNineHolonomicField
open FullQuantum.Triangular

open PreparationPhysicalEnergyCurrentWardReturn PreparationPhysicalJointGeneratorEnergyReturn
open PreparationVacuumMixedFieldReturn GaussComposite.PhysicalFullFieldScattering
open Electromagnetic.CanonicalCoframe

open PreparationPhysicalChargedHamiltonianRead PreparationPhysicalChargedScatteringPoleReturn

open PreparationPhysicalChargedVertexDomainReturn PreparationPhysicalChargedScatteringFourierReturn

open PreparationPhysicalChargedScatteringDomainPrice

open PreparationVacuumSoftPoleSelection PreparationVacuumNativePoleTensor PreparationVacuumSharedPoleCarrier
open PreparationVacuumPhysicalPoleSheet PreparationVacuumPhysicalCharacteristic PreparationVacuumWholeOrigin

open PreparationPhysicalChargedSoftScatteringReturn PreparationPhysicalNativePoleChargeReturn
open PreparationPhysicalScatteringFrequencyWard

open Stage10.CanonicalMatter StageNineCurrentCoframeMatterTemporalPrincipal
open PreparationVacuumGaugeSourceInjection GaussNativeMatter SourceQuantumFockGauge
open SourceQuantumGaugeSliceCoordinates SU7MotherLieAlgebra

attribute [local irreducible] nativeBranchVector sourceNativeOriginReal sourceNativeOriginImag
  realMixedCoefficientBilinear sourceSoftConnectionLower sourceNativeOriginCanonicalFiber

private theorem scalar_zero (c : ℂ) : c • (0:FiberOperators)=0 :=
  @_root_.smul_zero ℂ FiberOperators _ _ c
private theorem real_zero (c : ℝ) : c • (0:FiberOperators)=0 :=
  @_root_.smul_zero ℝ FiberOperators _ _ c

def sourceSoftDensityOperator (branch : Fin 2) : FiberOperators := canonicalMatrixRead (sourceSoftDensityMatrix branch)
def sourceSoftFrequencyOperator (branch : Fin 2) : FiberOperators := sourceEnergyMatrixRead (sourceSoftFrequencyMatrix branch)

private theorem native_scaled_real (c : ℂ) (branch : Fin 2) :
    (fun j=>((c • nativeBranchVector branch) j).re)=c.re • sourceNativeOriginReal branch := by
  funext j
  have imaginary:=congrFun (sourceNativeOriginImag_zero branch) j
  simp only [sourceNativeOriginImag,Pi.zero_apply] at imaginary
  simp only [Pi.smul_apply,smul_eq_mul,Complex.mul_re,imaginary,mul_zero,sub_zero,sourceNativeOriginReal]

private theorem native_scaled_im (c : ℂ) (branch : Fin 2) :
    (fun j=>((c • nativeBranchVector branch) j).im)=c.im • sourceNativeOriginReal branch := by
  funext j
  have imaginary:=congrFun (sourceNativeOriginImag_zero branch) j
  simp only [sourceNativeOriginImag,Pi.zero_apply] at imaginary
  simp only [Pi.smul_apply,smul_eq_mul,Complex.mul_im,imaginary,mul_zero,zero_add,sourceNativeOriginReal]

private theorem real_component_smul (c : ℂ) (T : FiberOperators) :
    c.re • T+Complex.I • (c.im • T)=c • T := by
  rw [RCLike.real_smul_eq_coe_smul (K:=ℂ) c.re T,
    RCLike.real_smul_eq_coe_smul (K:=ℂ) c.im T,smul_smul,←add_smul]
  congr 1
  rw [mul_comm Complex.I]
  exact Complex.re_add_im c

/-- Independent complex source amplitudes multiply the actual full density vertex. -/
theorem sourceSoftDensity_scaled (c : ℂ) (branch : Fin 2) (k : Fin 4) :
    complexCoefficients (originalComplexDirection (c • nativeBranchVector branch)) k=
      if k=0 then c • sourceSoftDensityOperator branch else 0 := by
  rw [complexCoefficients,originalComplexDirection,native_scaled_real,native_scaled_im]
  rw [←realDensityCoefficients_source,←realDensityCoefficients_source]
  simp only [map_smul]
  rw [real_component_smul,realDensityCoefficients_source,fieldCoefficients,sourceSoftDensityCoefficients]
  by_cases zero : k=0
  · simp only [if_pos zero,sourceSoftDensityOperator]
  · simp only [if_neg zero,map_zero,scalar_zero]

/-- The original frequency vertex uses the same complete energy operator and retains all complex source phases. -/
theorem sourceSoftFrequency_scaled (c : ℂ) (branch : Fin 2) (k : Fin 4) :
    complexFrequencyCoefficients (originalComplexDirection (c • nativeBranchVector branch)) k=
      if k=0 then c • sourceSoftFrequencyOperator branch else 0 := by
  rw [complexFrequencyCoefficients,originalComplexDirection,native_scaled_real,native_scaled_im]
  rw [←realFrequencyCoefficients_source,←realFrequencyCoefficients_source]
  simp only [map_smul]
  rw [real_component_smul,realFrequencyCoefficients_source,frequencyCoefficients,sourceSoftHamiltonianCoefficients]
  by_cases zero : k=0
  · simp only [if_pos zero]
    rfl
  · simp only [if_neg zero,map_zero,operator_zero,scalar_zero]

private theorem scaled_mixed_zero (left right : Fin 2) (a b : ℝ) (k : Fin 4) :
    mixedCoefficients (PreparationVacuumMixedFieldReturn.sourceField (a • sourceNativeOriginReal left))
      (PreparationVacuumMixedFieldReturn.sourceField (b • sourceNativeOriginReal right)) k=0 := by
  rw [mixedCoefficients_smul_left,mixedCoefficients_smul_right,sourceSoftMixedCoefficients]
  simp only [real_zero]

/-- The full mixed density and shell contact vanish by the source coframe Hessian, for both branches and both complex amplitudes. -/
theorem sourceSoftMixed_scaled (c d : ℂ) (left right : Fin 2) (k : Fin 4) :
    complexMixedCoefficients (originalComplexDirection (c • nativeBranchVector left))
      (originalComplexDirection (d • nativeBranchVector right)) k=0 := by
  simp only [complexMixedCoefficients,originalComplexDirection,native_scaled_real,native_scaled_im,scaled_mixed_zero,
    sub_zero,add_zero,scalar_zero]

private theorem source_volume : sourceVolume=(lapse:ℂ) := by
  rw [sourceVolume,actual_coframe,Stage9C.Dynamics.Homogeneous.homogeneousCoframe_det,abs_of_pos lapse_pos]

private theorem source_phase_inverse :
    (lapse:ℂ) • phaseInverse=Complex.I • currentCoframeMatterTemporalPrincipalInverse (actual.coframe 0) := by
  let C:=currentCoframeMatterTemporalPrincipal (actual.coframe 0)
  let R:=currentCoframeMatterTemporalPrincipalInverse (actual.coframe 0)
  have relation : phaseInverse*C=(Complex.I*(lapse:ℂ)⁻¹) • (1:YangMills.FullPairing.Mother) := by
    apply LinearMap.ext
    intro v
    change phaseInverse (currentCoframeMatterTemporalPrincipal (actual.coframe 0) v)=
      (Complex.I*(lapse:ℂ)⁻¹) • v
    rw [actual_temporal_principal,map_smul,phase_inverse_source]
  have inverse : C*R=(1:YangMills.FullPairing.Mother) := by
    apply LinearMap.ext
    intro v
    exact currentCoframeMatterTemporalPrincipalInverse_right _ (actual_noncharacteristic 0) v
  have generated:=congrArg (fun A : YangMills.FullPairing.Mother=>A*R) relation
  rw [mul_assoc,inverse,mul_one,smul_mul_assoc,one_mul] at generated
  rw [generated,smul_smul]
  congr 1
  have nonzero : (lapse:ℂ)≠0:=Complex.ofReal_ne_zero.mpr lapse_pos.ne'
  field_simp [nonzero]

/-- The canonical density and energy vertices have their original opposite sign, fixed by the actual temporal principal and volume. -/
theorem sourceSoftDensity_frequency (branch : Fin 2) :
    sourceSoftDensityOperator branch= -sourceSoftFrequencyOperator branch := by
  change operator (phaseInverse*Quantum.operatorMatrix.symm (sourceVolume • sourceSoftConnectionLower branch))=
    -operator (Quantum.operatorMatrix.symm ((-Complex.I) •
      (Ring.inverse (principalMatrix (actual.coframe 0))*sourceSoftConnectionLower branch)))
  rw [principal_inverse_original _ (actual_noncharacteristic 0)]
  simp only [map_smul,map_mul,AlgEquiv.symm_apply_apply]
  rw [source_volume,mul_smul_comm,←smul_mul_assoc,source_phase_inverse,smul_mul_assoc]
  simp only [operator_smul]
  have sign (A : FiberOperators) : (-Complex.I) • A= -(Complex.I • A) := by
    apply ContinuousLinearMap.ext
    intro v
    change (-Complex.I) • (A v)= -(Complex.I • (A v))
    exact neg_smul Complex.I (A v)
  rw [sign,neg_neg]

private theorem source_soft_connection (branch : Fin 2) (mu : Fin 4) :
    sourceNativeOriginConnection branch mu=Quantum.operatorMatrix
      (diracExteriorMotherLieAction (p286LieBlockEmbed
        (p286CoordinateEquiv.symm (fieldGauge (sourceNativeOriginReal branch) mu)))) := by
  have generated:=congrArg (fun state : ActionState=>state.2.1 mu) (sourceNativeOriginAction_state branch)
  rw [←stateDirection_source] at generated
  change spinLinear mu (fieldLorentz (sourceNativeOriginReal branch))+
    nativePrimal (fieldGauge (sourceNativeOriginReal branch) mu)=_ at generated
  rw [(sourceNativeOriginReal_remaining branch).2.2,map_zero,zero_add] at generated
  exact generated.symm

private theorem source_soft_density_matrix (branch : Fin 2) :
    sourceSoftDensityMatrix branch=Quantum.operatorMatrix (sourceNativeOriginDensityAction branch) := by
  simp only [sourceSoftDensityMatrix,sourceSoftConnectionLower,sourceNativeOriginDensityAction,
    Finset.smul_sum,map_sum]
  apply Finset.sum_congr rfl
  intro mu _
  rw [source_volume,source_soft_connection,coefficientMatrix,actual_coframe]
  change (lapse:ℂ) • ((Complex.I • Quantum.operatorMatrix
      (diracMatrixMatterAction (inverseCoframeDiracGamma {coframe:=Stage9C.Dynamics.Homogeneous.homogeneousCoframe lapse,derivative:=0} mu)))*
      Quantum.operatorMatrix (diracExteriorMotherLieAction (p286LieBlockEmbed
        (p286CoordinateEquiv.symm (fieldGauge (sourceNativeOriginReal branch) mu)))))=_
  rw [sourceGaugeDensityAction,map_smul,Quantum.matrix_composition,Matrix.smul_mul,smul_smul]

/-- The complete density vertex is exactly the independently generated Noether action, before any restriction to rest states. -/
theorem sourceSoftDensity_Noether (branch : Fin 2) :
    sourceSoftDensityOperator branch=sourceNativeOriginCanonicalFiber branch := by
  rw [sourceSoftDensityOperator,source_soft_density_matrix]
  change operator (phaseInverse*Quantum.operatorMatrix.symm (Quantum.operatorMatrix (sourceNativeOriginDensityAction branch)))=_
  rw [AlgEquiv.symm_apply_apply,sourceNativeOriginCanonicalFiber]
  rfl

theorem sourceSoftFrequency_Noether (branch : Fin 2) :
    sourceSoftFrequencyOperator branch= -sourceNativeOriginCanonicalFiber branch := by
  rw [←sourceSoftDensity_Noether,sourceSoftDensity_frequency,neg_neg]

end LowEnergy.PreparationPhysicalChargedSoftObservable
