import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceNoetherObservationMeter

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
local instance actualLegNormalizationIndex : DecidableEq Quantum.Index:=Classical.decEq _
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

/-- The complete moving expansion is restricted by the actual reference rest energy, without selecting an eigenbasis label. -/
theorem sourceActualRestCoefficient_energy (side edge : Fin 2) (state : RestStateIndex) :
    (sourceMovingPoleEnergy 0 state:ℂ)*sourceChargedMovingCoefficient 0 side edge state=
      (sourceActualChargedRestEnergy side:ℂ)*sourceChargedMovingCoefficient 0 side edge state := by
  have eigen (a : RestStateIndex) :
      FullQuantum.hamiltonian actual 0 0 (actualMovingPolePreparation 0 a (embed (Source.vector 0)))=
        (sourceMovingPoleEnergy 0 a:ℂ) • actualMovingPolePreparation 0 a (embed (Source.vector 0)) := by
    rw [actualMovingPole_source,map_smul,map_smul]
    rw [←Runtime.configuration_eq,sourceMovingPole_hamiltonian]
    exact smul_comm _ _ _
  have pair (a b : RestStateIndex) :
      inner ℂ (naturalCoordinates (actualMovingPolePreparation 0 a (embed (Source.vector 0))))
        (naturalCoordinates (actualMovingPolePreparation 0 b (embed (Source.vector 0))))=
          if a=b then 1 else 0 := by
    simpa only [prepared,operator_coordinates] using actualMovingPole_orthonormal 0 0 a b
  have eqn:=sourceActualChargedRest_hamiltonian side edge
  rw [sourceChargedRestriction_moving 0 side edge] at eqn
  simp only [map_sum,map_smul,eigen,Finset.smul_sum,smul_smul] at eqn
  have read:=congrArg (fun v=>inner ℂ
    (naturalCoordinates (actualMovingPolePreparation 0 state (embed (Source.vector 0))))
      (naturalCoordinates v)) eqn
  simp only [map_sum,map_smul,inner_sum,inner_smul_right,pair,mul_ite,mul_one,mul_zero] at read
  simpa only [Finset.sum_ite_eq Finset.univ state,Finset.mem_univ,ite_true,mul_comm] using read

def sourceActualColumnDefect (epsilon : ℝ) (precision : 0<epsilon) (side edge : Fin 2)
    (F : GaussUnitaryHistory.Index) : H :=
  jointGenerator 0 F 0 0 (sourceChargedGaussPrepared epsilon precision side edge)-
    (sourceActualChargedRestEnergy side:ℂ) • sourceChargedGaussPrepared epsilon precision side edge

def sourceActualLegDual (epsilon : ℝ) (precision : 0<epsilon) (side edge : Fin 2) : H→L[ℂ]ℂ :=
  innerSL ℂ (sourceChargedGaussPrepared epsilon precision side edge)

def sourceActualDualDefect (epsilon : ℝ) (precision : 0<epsilon) (side edge : Fin 2)
    (F : GaussUnitaryHistory.Index) : H→L[ℂ]ℂ :=
  (sourceActualLegDual epsilon precision side edge).comp (jointGenerator 0 F 0 0)-
    (sourceActualChargedRestEnergy side:ℂ) • sourceActualLegDual epsilon precision side edge

theorem sourceActualColumnDefect_poles (epsilon : ℝ) (precision : 0<epsilon) (side edge : Fin 2)
    (F : GaussUnitaryHistory.Index) :
    sourceActualColumnDefect epsilon precision side edge F=
      ∑a : RestStateIndex,sourceChargedMovingCoefficient 0 side edge a •
        sourcePoleColumnDefect epsilon precision 0 a F := by
  rw [sourceActualColumnDefect,sourceChargedGaussPrepared_moving epsilon precision 0 side edge]
  simp only [map_sum,map_smul,Finset.smul_sum,←Finset.sum_sub_distrib,sourcePoleColumnDefect,smul_sub,smul_smul]
  apply Finset.sum_congr rfl
  intro a _
  rw [mul_comm _ (sourceMovingPoleEnergy 0 a:ℂ),sourceActualRestCoefficient_energy]

theorem sourceActualLegDual_poles (epsilon : ℝ) (precision : 0<epsilon) (side edge : Fin 2) :
    sourceActualLegDual epsilon precision side edge=
      ∑a : RestStateIndex,star (sourceChargedMovingCoefficient 0 side edge a) •
        sourcePoleDual epsilon precision 0 a := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [sourceActualLegDual,sourcePoleDual,innerSL_apply_apply,sum_apply,smul_apply]
  rw [sourceChargedGaussPrepared_moving epsilon precision 0 side edge, sum_inner]
  simp only [inner_smul_left,smul_eq_mul,starRingEnd_apply]

theorem sourceActualDualDefect_poles (epsilon : ℝ) (precision : 0<epsilon) (side edge : Fin 2)
    (F : GaussUnitaryHistory.Index) :
    sourceActualDualDefect epsilon precision side edge F=
      ∑a : RestStateIndex,star (sourceChargedMovingCoefficient 0 side edge a) •
        sourcePoleDualDefect epsilon precision 0 a F := by
  rw [sourceActualDualDefect,sourceActualLegDual_poles]
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply,sum_apply,smul_apply,sub_apply,sourcePoleDualDefect,
    smul_eq_mul,Finset.mul_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  have energy:=congrArg star (sourceActualRestCoefficient_energy side edge a)
  simp only [star_mul,Complex.star_def,Complex.conj_ofReal] at energy
  simp only [starRingEnd_apply] at energy
  linear_combination (sourcePoleDual epsilon precision 0 a v)*energy

end LowEnergy.PreparationPhysicalActualLegNormalization
