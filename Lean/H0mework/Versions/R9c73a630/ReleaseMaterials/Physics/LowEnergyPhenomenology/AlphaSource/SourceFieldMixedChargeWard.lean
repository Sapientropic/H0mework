import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceFieldChargeDerivative

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalActualFieldNoetherResponse
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
local instance actualFieldMixedIndex : DecidableEq Quantum.Index:=Classical.decEq _
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

open PreparationPhysicalCommonSpatialGreen
open scoped SchwartzMap

open PreparationPhysicalActualLegNormalization PreparationVacuumPhysicalTailPrice
local instance : NormedAlgebra ℝ (Operator) := NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] jointVertex mixedVertex jointCurrent jointHessian sourceAbsoluteCharge

open PreparationPhysicalActualUnitFourPointReturn PreparationPhysicalSourceHarmonicReturn

def sourceFieldChargeBracket (A : Operator) : Operator :=
  sourceAbsoluteCharge*A-A*sourceAbsoluteCharge

def sourceFieldGreenCharge (q : PhysicalResponsePoint) (p : PhysicalMomentum) (z : ℂ) : Operator :=
  -(jointResolvent p q.F z 0*sourceFieldChargeBracket (jointGenerator p q.F 0 0)*
    jointResolvent p q.F z 0)

private theorem inverse_bracket {R : Type*} [Ring R] [Algebra ℂ R]
    (Q C G : R) (z : ℂ) (left : G*(C-z • 1)=1) (right : (C-z • 1)*G=1) :
    -(G*(Q*C-C*Q)*G)=Q*G-G*Q := by
  have gc : G*C=1+z • G := by
    rw [mul_sub,mul_smul_comm,mul_one] at left
    exact sub_eq_iff_eq_add.mp left
  have cg : C*G=1+z • G := by
    rw [sub_mul,smul_mul_assoc,one_mul] at right
    exact sub_eq_iff_eq_add.mp right
  have regroup : -(G*(Q*C-C*Q)*G)= -(G*Q*(C*G))+(G*C)*Q*G := by noncomm_ring
  rw [regroup,gc,cg]
  simp only [mul_add,add_mul,one_mul,mul_one,mul_smul_comm,smul_mul_assoc,neg_add_rev]
  abel

theorem sourceFieldGreenCharge_generated (q : PhysicalResponsePoint) (p : PhysicalMomentum)
    (z : ℂ) (nonreal : z.im≠0) :
    sourceFieldGreenCharge q p z=sourceFieldChargeBracket (jointResolvent p q.F z 0) := by
  exact inverse_bracket _ _ _ _ (sourceMaterialInverse_left p q.F z nonreal)
    (sourceMaterialInverse_right p q.F z nonreal)

/-- This is the original full mixed core before its two exterior resolvents. -/
def sourceFieldMixedCore (q : PhysicalResponsePoint) (p k : PhysicalMomentum) (f g : Field289) : Operator :=
  jointCurrent (p+k) q.F q.z 0 f*jointResolvent (p+k) q.F q.z 0*jointCurrent p q.F q.w 0 g+
  jointCurrent p q.F q.w 0 g*jointResolvent p q.F q.w 0*jointCurrent p q.F q.w 0 f-
  jointHessian p q.F q.w f g

/-- Each interior current, original whole generator and direct Hessian contributes its actual torque. -/
def sourceFieldMixedCoreTorque (q : PhysicalResponsePoint) (p k : PhysicalMomentum) (f g : Field289) : Operator :=
  let A:=jointCurrent (p+k) q.F q.z 0 f
  let B:=jointCurrent p q.F q.w 0 g
  let C:=jointCurrent p q.F q.w 0 f
  let L:=jointResolvent (p+k) q.F q.z 0
  let R:=jointResolvent p q.F q.w 0
  sourceFieldChargeBracket A*L*B+A*sourceFieldGreenCharge q (p+k) q.z*B+A*L*sourceFieldChargeBracket B+
  sourceFieldChargeBracket B*R*C+B*sourceFieldGreenCharge q p q.w*C+B*R*sourceFieldChargeBracket C-
  sourceFieldChargeBracket (jointHessian p q.F q.w f g)

def sourceFieldMixedChargeResponse (q : PhysicalResponsePoint) (p k : PhysicalMomentum)
    (f g : Field289) : Operator :=
  sourceFieldGreenCharge q (p+k) q.z*sourceFieldMixedCore q p k f g*jointResolvent p q.F q.w 0+
  jointResolvent (p+k) q.F q.z 0*sourceFieldMixedCoreTorque q p k f g*jointResolvent p q.F q.w 0+
  jointResolvent (p+k) q.F q.z 0*sourceFieldMixedCore q p k f g*sourceFieldGreenCharge q p q.w

private theorem mixed_factor {R : Type*} [Ring R] (L G A B C S : R) :
    L*A*L*B*G+L*B*G*C*G-L*S*G=L*(A*L*B+B*G*C-S)*G := by noncomm_ring

private theorem mixed_bracket {R : Type*} [Ring R] (Q L G A B C S : R) :
    (Q*A-A*Q)*L*B+A*(Q*L-L*Q)*B+A*L*(Q*B-B*Q)+
    (Q*B-B*Q)*G*C+B*(Q*G-G*Q)*C+B*G*(Q*C-C*Q)-(Q*S-S*Q)=
      Q*(A*L*B+B*G*C-S)-(A*L*B+B*G*C-S)*Q := by noncomm_ring

private theorem sandwich_bracket {R : Type*} [Ring R] (Q L G A : R) :
    (Q*L-L*Q)*A*G+L*(Q*A-A*Q)*G+L*A*(Q*G-G*Q)=Q*(L*A*G)-(L*A*G)*Q := by
  noncomm_ring

theorem sourceFieldMixedCore_return (q : PhysicalResponsePoint) (p k : PhysicalMomentum) (f g : Field289) :
    mixedVertex f g p k q.F q.z q.w=
      jointResolvent (p+k) q.F q.z 0*sourceFieldMixedCore q p k f g*jointResolvent p q.F q.w 0 := by
  simp only [mixedVertex,sourceFieldMixedCore]
  exact mixed_factor _ _ _ _ _ _

theorem sourceFieldMixedCoreTorque_return (q : PhysicalResponsePoint) (p k : PhysicalMomentum)
    (f g : Field289) (left : q.z.im≠0) (right : q.w.im≠0) :
    sourceFieldMixedCoreTorque q p k f g=sourceFieldChargeBracket (sourceFieldMixedCore q p k f g) := by
  simp only [sourceFieldMixedCoreTorque,sourceFieldGreenCharge_generated q (p+k) q.z left,
    sourceFieldGreenCharge_generated q p q.w right,sourceFieldChargeBracket,sourceFieldMixedCore]
  exact mixed_bracket _ _ _ _ _ _ _

/-- Full four-point charge identity retains all three Green torques, both current orderings and Hessian torque. -/
theorem sourceFieldMixedCharge_return (q : PhysicalResponsePoint) (p k : PhysicalMomentum)
    (f g : Field289) (left : q.z.im≠0) (right : q.w.im≠0) :
    sourceFieldMixedChargeResponse q p k f g=sourceFieldChargeBracket (mixedVertex f g p k q.F q.z q.w) := by
  rw [sourceFieldMixedChargeResponse,sourceFieldMixedCoreTorque_return q p k f g left right,
    sourceFieldGreenCharge_generated q (p+k) q.z left,sourceFieldGreenCharge_generated q p q.w right,
    sourceFieldMixedCore_return]
  simp only [sourceFieldChargeBracket]
  exact sandwich_bracket _ _ _ _

/-- The charge-contracted four-point response is produced by the original three-point field derivative. -/
theorem sourceFieldMixedCharge_generated (q : PhysicalResponsePoint) (p k : PhysicalMomentum)
    (f g : Field289) (left : q.z.im≠0) (right : q.w.im≠0) :
    HasDerivAt (fun r : ℝ=>sourceFieldChargeBracket (jointVertex g p k q.F q.z q.w (r • f)))
      (sourceFieldMixedChargeResponse q p k f g) 0 := by
  rw [sourceFieldMixedCharge_return q p k f g left right]
  have generated:=mixedVertex_generated f g p k q.F q.z q.w left right
  convert (generated.const_mul sourceAbsoluteCharge).sub (generated.mul_const sourceAbsoluteCharge) using 1 <;>
    simp only [sourceFieldChargeBracket] <;> rfl

theorem sourceFieldAbsoluteCharge_read (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (A : Operator) :
    sourceQuantumChargedRead q sL eL sR eR (sourceFieldChargeBracket A)=
      (Stage10.ActionNormalization.phaseMomentum:ℂ)*
        ((sourceActualPhaseCharge eL:ℂ)-(sourceActualPhaseCharge eR:ℂ))*
          sourceQuantumChargedRead q sL eL sR eR A := by
  have identity : sourceFieldChargeBracket A=(Stage10.ActionNormalization.phaseMomentum:ℂ) •
      (sourceActualGaussCharge*A-A*sourceActualGaussCharge) := by
    simp only [sourceFieldChargeBracket,sourceAbsoluteCharge,smul_mul_assoc,mul_smul_comm,smul_sub]
  rw [identity,map_smul,sourceActualPreparedCharge_commutator,smul_eq_mul,mul_assoc]

/-- All four actual preparation columns, including charged-neutral transitions, read the same full mixed response. -/
theorem sourceFieldMixedCharge_prepared (q : PhysicalResponsePoint) (p k : PhysicalMomentum)
    (sL eL sR eR : Fin 2) (f g : Field289) (left : q.z.im≠0) (right : q.w.im≠0) :
    sourceQuantumChargedRead q sL eL sR eR (sourceFieldMixedChargeResponse q p k f g)=
      (Stage10.ActionNormalization.phaseMomentum:ℂ)*
        ((sourceActualPhaseCharge eL:ℂ)-(sourceActualPhaseCharge eR:ℂ))*
          sourceQuantumChargedRead q sL eL sR eR (mixedVertex f g p k q.F q.z q.w) := by
  rw [sourceFieldMixedCharge_return q p k f g left right,sourceFieldAbsoluteCharge_read]

end LowEnergy.PreparationPhysicalActualFieldNoetherResponse
