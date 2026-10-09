import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceActualRestLegDefect

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalActualLegNormalization
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
local instance actualLegNormIndex : DecidableEq Quantum.Index:=Classical.decEq _
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


open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum FullSpace YangMills.FullPairing Stage9C.Material.SpinPair
open PreparationPhysicalNativeOriginPhaseWard PreparationPhysicalNativePoleChargeReturn
open PreparationPhysicalEnergyCurrentWardReturn PreparationPhysicalChargedSoftObservable
open PreparationPhysicalChargedPacketQuantumReturn PreparationPhysicalChargedSoftScatteringReturn
open PreparationPhysicalNormalizedFullField PreparationVacuumOriginalGreenFeedback
open PreparationVacuumPhysicalPoleSheet PreparationVacuumPhysicalCharacteristic
open Electromagnetic.CanonicalCoframe FullQuantum.Triangular
open MeasureTheory Filter
open scoped Topology InnerProductSpace

open PreparationPhysicalNativeSoftWardBoundary
open Set

open PreparationPhysicalFinitePoleVertices PreparationPhysicalFiniteOriginCovariance
open PreparationPhysicalNativePhotonFluxReturn PreparationPhysicalNativeWardFiniteObservation
open PreparationPhysicalNativePolarizationEmitter

open PreparationVacuumFullPoleContinuation PreparationVacuumPhysicalPoleHalfResponse
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumPhysicalCurrentLaplaceReturn
open PreparationPhysicalFiniteObservationSoftReturn PreparationVacuumSoftPoleSelection

open PreparationPhysicalCommonCurrentStaticRead PreparationPhysicalNativePhaseChargeInventory
open SU7MotherGaugeTheory SU7ExteriorMatterRepresentation SU7ExteriorMatterRestriction

open PreparationPhysicalActualPhaseChargeReturn
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge GaussCoreHilbert GaussFockLift
open GaussQuantumMultiplier GaussHalfDensity CanonicalGradedCharge GaussHistoryHilbert
open SourceQuantumGaugeSliceCoordinates
local instance : DecidableEq Mode:=Classical.decEq _

open PreparationPhysicalActualGaussChargeCurrent
open PreparationVacuumJointFieldResponse PreparationVacuumRawJointFeedback
open PreparationVacuumCurrentRegularAnchor PreparationVacuumPhysicalPoleAmputation

open PreparationPhysicalActualNoetherVertexReturn PreparationVacuumPhysicalPoleLegDynamics
open Stage9DEF Stage9DEF.Compatibility
attribute [local irreducible] jointGenerator jointResolvent sourceChargedGaussPrepared

def sourceActualAmputatedPrimal (q : PhysicalResponsePoint) (side edge : Fin 2) (z : ℂ) : H :=
  sourceChargedGaussPrepared q.epsilon q.precision side edge-
    jointResolvent 0 q.F z 0 (sourceActualColumnDefect q.epsilon q.precision side edge q.F)

def sourceActualAmputatedDual (q : PhysicalResponsePoint) (side edge : Fin 2) (z : ℂ) : H→L[ℂ]ℂ :=
  sourceActualLegDual q.epsilon q.precision side edge-
    (sourceActualDualDefect q.epsilon q.precision side edge q.F).comp (jointResolvent 0 q.F z 0)

theorem sourceActualPrimal_amputated (q : PhysicalResponsePoint) (side edge : Fin 2)
    (z : ℂ) (nonreal : z.im≠0) :
    sourceActualAmputatedPrimal q side edge z=
      ((sourceActualChargedRestEnergy side:ℂ)-z) •
        jointResolvent 0 q.F z 0 (sourceChargedGaussPrepared q.epsilon q.precision side edge) := by
  have inverse:=congrArg (fun A : H→L[ℂ]H=>A (sourceChargedGaussPrepared q.epsilon q.precision side edge))
    (sourceMaterialInverse_left 0 q.F z nonreal)
  simp only [mul_apply_eq_comp,sub_apply,smul_apply,one_apply_eq_self,map_sub,map_smul] at inverse
  have returned:=sub_eq_iff_eq_add.mp inverse
  simp only [sourceActualAmputatedPrimal,sourceActualColumnDefect,map_sub,map_smul]
  rw [returned]
  module

theorem sourceActualDual_amputated (q : PhysicalResponsePoint) (side edge : Fin 2)
    (z : ℂ) (nonreal : z.im≠0) :
    sourceActualAmputatedDual q side edge z=
      ((sourceActualChargedRestEnergy side:ℂ)-z) •
        (sourceActualLegDual q.epsilon q.precision side edge).comp (jointResolvent 0 q.F z 0) := by
  apply ContinuousLinearMap.ext
  intro v
  have inverse:=congrArg (fun A : H→L[ℂ]H=>A v) (sourceMaterialInverse_right 0 q.F z nonreal)
  simp only [mul_apply_eq_comp,sub_apply,smul_apply,one_apply_eq_self] at inverse
  have read:=congrArg (sourceActualLegDual q.epsilon q.precision side edge) inverse
  simp only [map_sub,map_smul] at read
  simp only [sourceActualAmputatedDual,sourceActualDualDefect,sub_apply,smul_apply,ContinuousLinearMap.comp_apply]
  linear_combination -read

theorem sourceActualReferenceGap_nonzero (side : Fin 2) (z : ℂ) (nonreal : z.im≠0) :
    (sourceActualChargedRestEnergy side:ℂ)-z≠0 := by
  intro same
  have im:=congrArg Complex.im same
  simp only [Complex.sub_im,Complex.ofReal_im,zero_sub,Complex.zero_im,neg_eq_zero] at im
  exact nonreal im

theorem sourceActualAmputatedPrimal_nonzero (q : PhysicalResponsePoint) (side edge : Fin 2)
    (z : ℂ) (nonreal : z.im≠0) : sourceActualAmputatedPrimal q side edge z≠0 := by
  rw [sourceActualPrimal_amputated q side edge z nonreal]
  apply smul_ne_zero (sourceActualReferenceGap_nonzero side z nonreal)
  intro zero
  have inverse:=congrArg (fun A : H→L[ℂ]H=>A (sourceChargedGaussPrepared q.epsilon q.precision side edge))
    (sourceMaterialInverse_right 0 q.F z nonreal)
  simp only [mul_apply_eq_comp,one_apply_eq_self,zero,map_zero] at inverse
  have unit:=sourceChargedGauss_unit q.epsilon q.precision side edge
  rw [←inverse,norm_zero] at unit
  norm_num at unit

theorem sourceActualAmputatedDual_nonzero (q : PhysicalResponsePoint) (side edge : Fin 2)
    (z : ℂ) (nonreal : z.im≠0) : sourceActualAmputatedDual q side edge z≠0 := by
  rw [sourceActualDual_amputated q side edge z nonreal]
  intro vanishedLeg
  have zero : (sourceActualLegDual q.epsilon q.precision side edge).comp (jointResolvent 0 q.F z 0)=0 := by
    have cancel:=congrArg (fun d : H→L[ℂ]ℂ=>((sourceActualChargedRestEnergy side:ℂ)-z)⁻¹ • d) vanishedLeg
    apply ContinuousLinearMap.ext
    intro v
    have value:=congrArg (fun d : H→L[ℂ]ℂ=>d v) cancel
    simpa only [smul_apply,smul_smul,inv_mul_cancel₀ (sourceActualReferenceGap_nonzero side z nonreal),
      one_smul,zero_apply,smul_eq_mul,mul_zero] using value
  have inverse:=congrArg (fun A : H→L[ℂ]H=>A (sourceChargedGaussPrepared q.epsilon q.precision side edge))
    (sourceMaterialInverse_left 0 q.F z nonreal)
  have read:=congrArg (sourceActualLegDual q.epsilon q.precision side edge) inverse
  have vanished:=congrArg (fun d : H→L[ℂ]ℂ=>d
    ((jointGenerator 0 q.F 0 0-z • 1) (sourceChargedGaussPrepared q.epsilon q.precision side edge))) zero
  simp only [mul_apply_eq_comp,one_apply_eq_self] at read
  simp only [ContinuousLinearMap.comp_apply,zero_apply] at vanished
  rw [vanished] at read
  simp only [sourceActualLegDual,innerSL_apply_apply,sourceChargedGauss_gram,ite_true] at read
  norm_num at read

def sourceActualUnitPrimal (q : PhysicalResponsePoint) (side edge : Fin 2) (z : ℂ) : H :=
  (‖sourceActualAmputatedPrimal q side edge z‖:ℂ)⁻¹ • sourceActualAmputatedPrimal q side edge z

def sourceActualUnitDual (q : PhysicalResponsePoint) (side edge : Fin 2) (z : ℂ) : H→L[ℂ]ℂ :=
  (‖sourceActualAmputatedDual q side edge z‖:ℂ)⁻¹ • sourceActualAmputatedDual q side edge z

theorem sourceActualUnitPrimal_norm (q : PhysicalResponsePoint) (side edge : Fin 2)
    (z : ℂ) (nonreal : z.im≠0) : ‖sourceActualUnitPrimal q side edge z‖=1 := by
  rw [sourceActualUnitPrimal,norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (sourceActualAmputatedPrimal_nonzero q side edge z nonreal))

theorem sourceActualUnitDual_norm (q : PhysicalResponsePoint) (side edge : Fin 2)
    (z : ℂ) (nonreal : z.im≠0) : ‖sourceActualUnitDual q side edge z‖=1 := by
  rw [sourceActualUnitDual,norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (sourceActualAmputatedDual_nonzero q side edge z nonreal))

theorem sourceActualAmputated_prices (q : PhysicalResponsePoint) (side edge : Fin 2) (z : ℂ) :
    ‖sourceActualAmputatedPrimal q side edge z‖≤1+
      ‖jointResolvent 0 q.F z 0‖*‖sourceActualColumnDefect q.epsilon q.precision side edge q.F‖ ∧
    ‖sourceActualAmputatedDual q side edge z‖≤1+
      ‖sourceActualDualDefect q.epsilon q.precision side edge q.F‖*‖jointResolvent 0 q.F z 0‖ := by
  constructor
  · exact (norm_sub_le _ _).trans ((add_le_add (le_refl _)
      ((jointResolvent 0 q.F z 0).le_opNorm _)).trans_eq (by rw [sourceChargedGauss_unit]))
  · exact (norm_sub_le _ _).trans ((add_le_add (le_refl _)
      (ContinuousLinearMap.opNorm_comp_le _ _)).trans_eq (by
        rw [sourceActualLegDual,innerSL_apply_norm,sourceChargedGauss_unit]))

end LowEnergy.PreparationPhysicalActualLegNormalization
