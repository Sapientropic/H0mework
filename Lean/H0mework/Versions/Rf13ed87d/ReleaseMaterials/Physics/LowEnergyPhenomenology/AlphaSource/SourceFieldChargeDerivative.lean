import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceHarmonicPacketReturn

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
local instance actualUnitFourIndex : DecidableEq Quantum.Index:=Classical.decEq _
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

/-- Original absolute hQ insertion on the same full field-dependent two Green operators. -/
def sourceFieldChargeVertex (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (field : Field289) : Operator :=
  jointResolvent pL q.F q.z field*sourceAbsoluteCharge*jointResolvent pR q.F q.w field

def sourceFieldChargeTorque (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (field : Field289) : Operator :=
  jointGenerator pL q.F 0 field*sourceAbsoluteCharge-
    sourceAbsoluteCharge*jointGenerator pR q.F 0 field

def sourceFieldChargeResponse (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (field : Field289) : Operator :=
  jointResolvent pL q.F q.z field*sourceFieldChargeTorque q pL pR field*
    jointResolvent pR q.F q.w field

def sourceFieldInverseVariation (q : PhysicalResponsePoint) (p : PhysicalMomentum)
    (z : ℂ) (f : Field289) : Operator :=
  -(jointResolvent p q.F z 0*jointCurrent p q.F z 0 f*jointResolvent p q.F z 0)

def sourceFieldChargeInsertion (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (f : Field289) : Operator :=
  sourceFieldInverseVariation q pL q.z f*sourceAbsoluteCharge*jointResolvent pR q.F q.w 0+
    jointResolvent pL q.F q.z 0*sourceAbsoluteCharge*sourceFieldInverseVariation q pR q.w f

def sourceFieldChargeCurrentTorque (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (f : Field289) : Operator :=
  jointCurrent pL q.F 0 0 f*sourceAbsoluteCharge-
    sourceAbsoluteCharge*jointCurrent pR q.F 0 0 f

def sourceFieldChargeResponseInsertion (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (f : Field289) : Operator :=
  sourceFieldInverseVariation q pL q.z f*sourceFieldChargeTorque q pL pR 0*
    jointResolvent pR q.F q.w 0+
  jointResolvent pL q.F q.z 0*sourceFieldChargeCurrentTorque q pL pR f*
    jointResolvent pR q.F q.w 0+
  jointResolvent pL q.F q.z 0*sourceFieldChargeTorque q pL pR 0*
    sourceFieldInverseVariation q pR q.w f

theorem sourceFieldChargeVertex_generated (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (f : Field289) (left : q.z.im≠0) (right : q.w.im≠0) :
    HasDerivAt (fun r : ℝ=>sourceFieldChargeVertex q pL pR (r • f))
      (sourceFieldChargeInsertion q pL pR f) 0 := by
  have l:=inverse_direction pL q.F q.z left f
  have r:=inverse_direction pR q.F q.w right f
  convert (l.mul_const sourceAbsoluteCharge).mul r using 1 <;> simp only [sourceFieldChargeVertex,sourceFieldChargeInsertion,sourceFieldInverseVariation,zero_smul] <;> rfl

theorem sourceFieldChargeTorque_generated (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (f : Field289) :
    HasDerivAt (fun r : ℝ=>sourceFieldChargeTorque q pL pR (r • f))
      (sourceFieldChargeCurrentTorque q pL pR f) 0 := by
  have l:=(jointGenerator_ray_derivative f pL q.F 0).self_of_nhds
  have r:=(jointGenerator_ray_derivative f pR q.F 0).self_of_nhds
  convert (l.mul_const sourceAbsoluteCharge).sub (r.const_mul sourceAbsoluteCharge) using 1 <;>
    simp only [sourceFieldChargeTorque,sourceFieldChargeCurrentTorque,zero_smul] <;> rfl

theorem sourceFieldChargeResponse_generated (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (f : Field289) (left : q.z.im≠0) (right : q.w.im≠0) :
    HasDerivAt (fun r : ℝ=>sourceFieldChargeResponse q pL pR (r • f))
      (sourceFieldChargeResponseInsertion q pL pR f) 0 := by
  have l:=inverse_direction pL q.F q.z left f
  have t:=sourceFieldChargeTorque_generated q pL pR f
  have r:=inverse_direction pR q.F q.w right f
  convert (l.mul t).mul r using 1 <;> simp only [sourceFieldChargeResponse,sourceFieldChargeResponseInsertion,sourceFieldInverseVariation,
    zero_smul,Pi.mul_apply,add_mul,add_assoc] <;> rfl

private theorem variation_ward {R : Type*} [Ring R] [Algebra ℂ R]
    (L Rg C D Q A B : R) (z w : ℂ)
    (li : L*(C-z • 1)=1) (ri : (D-w • 1)*Rg=1) :
    (z-w) • ((-(L*A*L))*Q*Rg+L*Q*(-(Rg*B*Rg)))=
      (-(L*A*L))*Q-Q*(-(Rg*B*Rg))+
      ((-(L*A*L))*(C*Q-Q*D)*Rg+L*(A*Q-Q*B)*Rg+L*(C*Q-Q*D)*(-(Rg*B*Rg))) := by
  have lc : L*C=1+z • L := by
    rw [mul_sub,mul_smul_comm,mul_one] at li
    exact sub_eq_iff_eq_add.mp li
  have dr : D*Rg=1+w • Rg := by
    rw [sub_mul,smul_mul_assoc,one_mul] at ri
    exact sub_eq_iff_eq_add.mp ri
  have subword :
      ((-(L*A*L))*(C*Q-Q*D)*Rg+L*(A*Q-Q*B)*Rg+L*(C*Q-Q*D)*(-(Rg*B*Rg)))=
      -L*A*(L*C)*Q*Rg+L*A*L*Q*(D*Rg)+L*A*Q*Rg-L*Q*B*Rg-
      (L*C)*Q*Rg*B*Rg+L*Q*(D*Rg)*B*Rg := by noncomm_ring
  rw [subword,lc,dr]
  simp only [add_mul,mul_add,one_mul,mul_one,neg_mul,mul_neg,smul_mul_assoc,mul_smul_comm,
    smul_add,smul_neg,sub_smul,mul_assoc]
  abel

/-- Differentiated absolute Ward: both induced current torque and both Green variations remain. -/
theorem sourceFieldChargeInsertion_ward (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (f : Field289) (left : q.z.im≠0) (right : q.w.im≠0) :
    (q.z-q.w) • sourceFieldChargeInsertion q pL pR f=
      sourceFieldInverseVariation q pL q.z f*sourceAbsoluteCharge-
        sourceAbsoluteCharge*sourceFieldInverseVariation q pR q.w f+
          sourceFieldChargeResponseInsertion q pL pR f := by
  unfold sourceFieldChargeInsertion sourceFieldChargeResponseInsertion sourceFieldChargeTorque
    sourceFieldChargeCurrentTorque sourceFieldInverseVariation
  simp only [jointCurrent_spectral]
  exact variation_ward (jointResolvent pL q.F q.z 0) (jointResolvent pR q.F q.w 0)
    (jointGenerator pL q.F 0 0) (jointGenerator pR q.F 0 0) sourceAbsoluteCharge
    (jointCurrent pL q.F 0 0 f) (jointCurrent pR q.F 0 0 f) q.z q.w
    (sourceMaterialInverse_left pL q.F q.z left) (sourceMaterialInverse_right pR q.F q.w right)

end LowEnergy.PreparationPhysicalActualFieldNoetherResponse
