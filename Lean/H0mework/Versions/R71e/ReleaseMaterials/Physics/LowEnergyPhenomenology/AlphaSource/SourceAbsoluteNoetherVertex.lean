import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceActualPreparedNoetherWard

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalActualNoetherVertexReturn
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
local instance actualNoetherVertexIndex : DecidableEq Quantum.Index:=Classical.decEq _
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

attribute [local irreducible] jointGenerator jointResolvent sourceActualGaussCharge

/-- The absolute charge operator uses the already generated source action unit. -/
def sourceAbsoluteCharge : H→L[ℂ]H :=
  (Stage10.ActionNormalization.phaseMomentum:ℂ) • sourceActualGaussCharge

def sourceAbsoluteNoetherVertex (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) : H→L[ℂ]H :=
  jointResolvent pL q.F q.z 0*sourceAbsoluteCharge*jointResolvent pR q.F q.w 0

/-- The response is generated by both original whole generators, including transfer and full Y. -/
def sourceAbsoluteNoetherResponse (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) : H→L[ℂ]H :=
  jointResolvent pL q.F q.z 0*
    (jointGenerator pL q.F 0 0*sourceAbsoluteCharge-sourceAbsoluteCharge*jointGenerator pR q.F 0 0)*
      jointResolvent pR q.F q.w 0

private theorem inverse_ward {R : Type*} [Ring R] [Algebra ℂ R]
    (CLeft CRight invLeft invRight Q : R) (z w : ℂ)
    (left : invLeft*(CLeft-z • 1)=1) (right : (CRight-w • 1)*invRight=1) :
    (z-w) • (invLeft*Q*invRight)=invLeft*Q-Q*invRight+invLeft*(CLeft*Q-Q*CRight)*invRight := by
  have l : invLeft*CLeft=1+z • invLeft := by
    have h:=left
    rw [mul_sub,mul_smul_comm,mul_one] at h
    exact sub_eq_iff_eq_add.mp h
  have r : CRight*invRight=1+w • invRight := by
    have h:=right
    rw [sub_mul,smul_mul_assoc,one_mul] at h
    exact sub_eq_iff_eq_add.mp h
  have generated : invLeft*(CLeft*Q-Q*CRight)*invRight=Q*invRight-invLeft*Q+(z-w) • (invLeft*Q*invRight) := by
    calc
      _=(invLeft*CLeft)*Q*invRight-invLeft*Q*(CRight*invRight) := by noncomm_ring
      _=(1+z • invLeft)*Q*invRight-invLeft*Q*(1+w • invRight) := by rw [l,r]
      _=_ := by
        simp only [add_mul,mul_add,one_mul,mul_one,smul_mul_assoc,mul_smul_comm,sub_smul]
        abel
  rw [generated]
  abel

/-- The original spectral subtraction and the two actual inverse mouths fix the endpoint signs. -/
theorem sourceAbsoluteNoether_ward (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left : q.z.im≠0) (right : q.w.im≠0) :
    (q.z-q.w) • sourceAbsoluteNoetherVertex q pL pR=
      jointResolvent pL q.F q.z 0*sourceAbsoluteCharge-
        sourceAbsoluteCharge*jointResolvent pR q.F q.w 0+sourceAbsoluteNoetherResponse q pL pR := by
  exact inverse_ward _ _ _ _ _ _ _ (sourceMaterialInverse_left pL q.F q.z left)
    (sourceMaterialInverse_right pR q.F q.w right)

/-- Each actual prepared end carries the same absolute source h-charge. -/
theorem sourceAbsoluteCharge_prepared (epsilon : ℝ) (precision : 0<epsilon) (side edge : Fin 2) :
    sourceAbsoluteCharge (sourceChargedGaussPrepared epsilon precision side edge)=
      ((Stage10.ActionNormalization.phaseMomentum:ℂ)*(sourceActualPhaseCharge edge:ℂ)) •
        sourceChargedGaussPrepared epsilon precision side edge := by
  rw [sourceAbsoluteCharge,smul_apply,sourceActualGaussCharge_prepared,smul_smul]

/-- The actual observed Noether vertex has its full two-point endpoint relation before any charge normalization or physical pole limit. -/
theorem sourceAbsoluteNoether_prepared (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (sL eL sR eR : Fin 2) (left : q.z.im≠0) (right : q.w.im≠0) :
    (q.z-q.w)*sourceQuantumChargedRead q sL eL sR eR (sourceAbsoluteNoetherVertex q pL pR)=
      (Stage10.ActionNormalization.phaseMomentum:ℂ)*(sourceActualPhaseCharge eR:ℂ)*
        sourceQuantumChargedRead q sL eL sR eR (jointResolvent pL q.F q.z 0)-
      (Stage10.ActionNormalization.phaseMomentum:ℂ)*(sourceActualPhaseCharge eL:ℂ)*
        sourceQuantumChargedRead q sL eL sR eR (jointResolvent pR q.F q.w 0)+
      sourceQuantumChargedRead q sL eL sR eR (sourceAbsoluteNoetherResponse q pL pR) := by
  have generated:=congrArg (sourceQuantumChargedRead q sL eL sR eR)
    (sourceAbsoluteNoether_ward q pL pR left right)
  simp only [map_smul,smul_eq_mul,map_add,map_sub,sourceAbsoluteCharge,mul_smul_comm,
    smul_mul_assoc,(sourceActualPreparedCharge_ends q sL eL sR eR _).1,
    (sourceActualPreparedCharge_ends q sL eL sR eR _).2] at generated
  convert generated using 1
  ring

end LowEnergy.PreparationPhysicalActualNoetherVertexReturn
