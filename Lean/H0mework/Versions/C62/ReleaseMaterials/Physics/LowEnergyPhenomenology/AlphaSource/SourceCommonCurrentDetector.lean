import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceActualSoftFiniteResponse

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalCommonCurrentStaticRead
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
local instance finiteObservationEmitterIndex : DecidableEq Quantum.Index:=Classical.decEq _
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

/-- The detector uses every original action-current coordinate, with independent material legs. -/
def sourceCommonDetector (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (l r : RestStateIndex) (lambda : ℂ) (T : ℝ) : (Fin 289→ℂ)→L[ℂ]ℂ :=
  ∑i : Fin 289,(ContinuousLinearMap.proj i : (Fin 289→ℂ)→L[ℂ]ℂ).smulRight
    (returnedCurrentWindow q pL pR l r lambda T i)

theorem sourceCommonDetector_current (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (l r : RestStateIndex) (lambda : ℂ) (T : ℝ) (V : Fin 289→ℂ) :
    sourceCommonDetector q pL pR l r lambda T V=
      ∑i : Fin 289,returnedCurrentWindow q pL pR l r lambda T i*V i := by
  simp only [sourceCommonDetector,sum_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply,smul_eq_mul,mul_comm]

/-- The same actual source tensor, before any field-channel restriction. -/
theorem sourceCommonDetector_action (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (l r : RestStateIndex) (lambda : ℂ) (T : ℝ) (V : Fin 289→ℂ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    sourceCommonDetector q pL pR l r lambda T V=
      ∫t in (0:ℝ)..T,laplaceWeight lambda t*
        (-sourcePoleRead q.epsilon q.precision 0 0 l r
          (∑i : Fin 289,V i • actualJointKernel q pL pR t i)) := by
  have continuous (i : Fin 289) : Continuous (fun t : ℝ=>
      laplaceWeight lambda t*returnedCurrentTensor q pL pR t i l r) := by
    have argument : Continuous (fun t : ℝ=>(pL,pR,t)) := continuous_const.prodMk (continuous_const.prodMk continuous_id)
    have matrix := (returnedCurrentTensor_continuous q i nonrealL nonrealR).comp argument
    have entry := (continuous_apply r).comp ((continuous_apply l).comp matrix)
    have weight : Continuous (laplaceWeight lambda) := by unfold laplaceWeight;fun_prop
    exact weight.mul entry
  rw [sourceCommonDetector_current]
  simp only [returnedCurrentWindow,←intervalIntegral.integral_mul_const]
  rw [←intervalIntegral.integral_finsetSum (fun i _=>(continuous i |>.mul_const (V i)).intervalIntegrable _ _)]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [returnedCurrentTensor,Matrix.neg_apply,sourceTensor,map_sum,map_smul,
    smul_eq_mul,Finset.mul_sum,Finset.sum_neg_distrib,mul_neg,neg_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The propagation family is literally the same full current used by this detector. -/
theorem sourceCommonDetector_soft (leg : SourceChargedSoftLeg) (branch : Fin 2)
    (n : PhysicalMomentum) (unit : spatialSquare n=1) (e : scaleDomain) (V : Fin 289→ℂ) :
    sourceCommonDetector leg.q (sheetLeft e.val n 0) 0
      (sourceChargedRestIndex leg.sideL leg.edgeL) (sourceChargedRestIndex leg.sideR leg.edgeR)
      (sheetLambda e.val (sourceSheet branch n unit e.val)) leg.window V=
      ∑i : Fin 289,sourceChargedSoftCurrent leg branch n unit e i*V i := by
  rw [sourceCommonDetector_current]
  rfl

end LowEnergy.PreparationPhysicalCommonCurrentStaticRead
