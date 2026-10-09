import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceNoetherPreparedMatrices
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceCommonSpatialReturn

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
local instance actualNoetherObservationIndex : DecidableEq Quantum.Index:=Classical.decEq _
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

open PreparationPhysicalCommonSpatialGreen
open scoped SchwartzMap

attribute [local irreducible] jointGenerator jointResolvent physicalTime sourceAbsoluteCharge
  sourceAbsoluteNoetherVertex sourceAbsoluteNoetherResponse sourceActualPreparedKernel
  sourceActualGaussCharge sourceQuantumChargedRead

/-- Both original time transports contribute their own charge torque. -/
def sourceNoetherTimeChargeCorrection (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (t : ℝ) : H→L[ℂ]H :=
  physicalTime pL q.F (-t) 0*jointResolvent pL q.F q.z 0*
      (sourceAbsoluteCharge*physicalTime pR q.F t 0-physicalTime pR q.F t 0*sourceAbsoluteCharge)-
    (physicalTime pL q.F (-t) 0*sourceAbsoluteCharge-sourceAbsoluteCharge*physicalTime pL q.F (-t) 0)*
      jointResolvent pR q.F q.w 0*physicalTime pR q.F t 0

private theorem timed_ward {R : Type*} [Ring R] [Algebra ℂ R]
    (L U A B Q V W : R) (d : ℂ) (ward : d • V=A*Q-Q*B+W) :
    d • (L*V*U)=(L*A*U)*Q-Q*(L*B*U)+L*W*U+
      (L*A*(Q*U-U*Q)-(L*Q-Q*L)*B*U) := by
  have generated:=congrArg (fun X : R=>L*X*U) ward
  rw [mul_smul_comm,smul_mul_assoc] at generated
  rw [generated]
  noncomm_ring

/-- The literal hQ vertex in the original two-time observation retains its entire generator and time responses. -/
theorem sourceNoetherTimed_prepared (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (sL eL sR eR : Fin 2) (t : ℝ) (left : q.z.im≠0) (right : q.w.im≠0) :
    (q.z-q.w)*sourceQuantumChargedRead q sL eL sR eR
      (physicalTime pL q.F (-t) 0*sourceAbsoluteNoetherVertex q pL pR*physicalTime pR q.F t 0)=
      (Stage10.ActionNormalization.phaseMomentum:ℂ)*(sourceActualPhaseCharge eR:ℂ)*
        sourceQuantumChargedRead q sL eL sR eR
          (physicalTime pL q.F (-t) 0*jointResolvent pL q.F q.z 0*physicalTime pR q.F t 0)-
      (Stage10.ActionNormalization.phaseMomentum:ℂ)*(sourceActualPhaseCharge eL:ℂ)*
        sourceQuantumChargedRead q sL eL sR eR
          (physicalTime pL q.F (-t) 0*jointResolvent pR q.F q.w 0*physicalTime pR q.F t 0)+
      sourceQuantumChargedRead q sL eL sR eR
        (physicalTime pL q.F (-t) 0*sourceAbsoluteNoetherResponse q pL pR*physicalTime pR q.F t 0)+
      sourceQuantumChargedRead q sL eL sR eR (sourceNoetherTimeChargeCorrection q pL pR t) := by
  have original:=timed_ward (physicalTime pL q.F (-t) 0) (physicalTime pR q.F t 0)
    (jointResolvent pL q.F q.z 0) (jointResolvent pR q.F q.w 0) sourceAbsoluteCharge
    (sourceAbsoluteNoetherVertex q pL pR) (sourceAbsoluteNoetherResponse q pL pR) (q.z-q.w)
    (sourceAbsoluteNoether_ward q pL pR left right)
  change (q.z-q.w) • (_ : H→L[ℂ]H)=_+sourceNoetherTimeChargeCorrection q pL pR t at original
  have generated:=congrArg (sourceQuantumChargedRead q sL eL sR eR) original
  simp only [map_smul,smul_eq_mul,map_add,map_sub,sourceAbsoluteCharge,mul_smul_comm,smul_mul_assoc,
    (sourceActualPreparedCharge_ends q sL eL sR eR _).1,
    (sourceActualPreparedCharge_ends q sL eL sR eR _).2] at generated
  convert generated using 1
  ring

/-- This charge meter is the literal source hQ insertion at the prepared end of the original full289 observation. -/
def sourceNoetherFieldMeter (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (lambda : ℂ) (T : ℝ) (V : Fin 289→ℂ) : Matrix ActualPreparedIndex ActualPreparedIndex ℂ :=
  -(Stage10.ActionNormalization.phaseMomentum:ℂ)⁻¹ •
    sourcePreparedCurrentMatrix q (sourceActualPreparedKernel q pL pR lambda T V*sourceAbsoluteCharge)

def sourcePreparedFieldMatrix (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (lambda : ℂ) (T : ℝ) (V : Fin 289→ℂ) : Matrix ActualPreparedIndex ActualPreparedIndex ℂ :=
  fun i j=>sourceActualPreparedDetector q pL pR i.1 i.2 j.1 j.2 lambda T V

/-- Charge normalization is generated by the same actual operator insertion, while the unprojected field matrix remains explicit. -/
theorem sourceNoetherFieldMeter_generated (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (lambda : ℂ) (T : ℝ) (V : Fin 289→ℂ) (left : q.z.im≠0) (right : q.w.im≠0) :
    sourceNoetherFieldMeter q pL pR lambda T V=
      sourcePreparedFieldMatrix q pL pR lambda T V*sourcePreparedChargeUnitMatrix := by
  ext i j
  rw [sourceNoetherFieldMeter,sourcePreparedChargeUnitMatrix,Matrix.mul_diagonal]
  simp only [Matrix.smul_apply,sourcePreparedCurrentMatrix,sourcePreparedFieldMatrix,smul_eq_mul]
  rw [sourceAbsoluteCharge,mul_smul_comm,map_smul,smul_eq_mul,
    (sourceActualPreparedCharge_ends q i.1 i.2 j.1 j.2 _).2,
    sourceActualPreparedDetector_action q pL pR i.1 i.2 j.1 j.2 lambda T V left right]
  have nonzero : (Stage10.ActionNormalization.phaseMomentum:ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr Stage10.ActionNormalization.phaseMomentum_positive.ne'
  field_simp

/-- The static inverse-square tensor reaches the same source-charge meter without angular or material averaging. -/
theorem sourceNoetherStaticMeter_return (qd : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (lambda : ℂ) (T : ℝ) (left : qd.z.im≠0) (right : qd.w.im≠0)
    (q : PhysicalResponsePoint) (n : PhysicalMomentum) (a b : RestStateIndex) :
    sourceNoetherFieldMeter qd pL pR lambda T (sourceCommonStaticSimple q n a b)=
      (spatialSquare n:ℂ)⁻¹ •
        sourceNoetherFieldMeter qd pL pR lambda T (sourceCommonCoulombTensor q n a b) := by
  ext i j
  rw [sourceNoetherFieldMeter_generated qd pL pR lambda T _ left right,
    sourceNoetherFieldMeter_generated qd pL pR lambda T _ left right]
  simp only [sourcePreparedChargeUnitMatrix,Matrix.mul_diagonal,Matrix.smul_apply,
    sourcePreparedFieldMatrix,smul_eq_mul]
  rw [sourceActualPreparedDetector_static]
  ring

/-- The full original causal spatial field, including all source and detector pairs, is consumed by the normalized charge meter. -/
theorem sourceNoetherSpatialMeter_return (qd q : PhysicalResponsePoint)
    (sL eL sR eR : Fin 2) (T c eta : ℝ) (nonzero : c≠0) (positive : 0<eta)
    (left : qd.z.im≠0) (right : qd.w.im≠0)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) (i j : ActualPreparedIndex) :
    sourceNoetherFieldMeter qd 0 0 0 T
      (sourceActualSpatialField q sL eL sR eR c eta test x) i j=
      sourceActualSpatialAmplitude q sL eL sR eR c eta test x*
        sourceActualPreparedGaussWeight qd i.1 i.2 j.1 j.2 T*(sourceActualPhaseCharge j.2:ℂ) := by
  rw [sourceNoetherFieldMeter_generated qd 0 0 0 T _ left right,
    sourcePreparedChargeUnitMatrix,Matrix.mul_diagonal]
  change sourceActualPreparedDetector qd 0 0 i.1 i.2 j.1 j.2 0 T
    (sourceActualSpatialField q sL eL sR eR c eta test x)*_=_
  rw [sourceActualSpatialDetector_generated qd q i.1 i.2 j.1 j.2 sL eL sR eR T c eta nonzero positive left right]
  rfl

/-- The same charge meter consumes the original frequency residue and its independent beta reader. -/
theorem sourceNoetherFrequencyMeter_return (qd : PhysicalResponsePoint) (pDL pDR : PhysicalMomentum)
    (lambda : ℂ) (T : ℝ) (left : qd.z.im≠0) (right : qd.w.im≠0)
    (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,∀(qs : PhysicalResponsePoint)(pSL pSR : PhysicalMomentum)
      (a b c d : Fin 2)(mu : ℂ)(S : ℝ),
      sourceNoetherFieldMeter qd pDL pDR lambda T
        (sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n*ᵥ
          sourceActualPreparedCurrent qs pSL pSR a b c d mu S)=
      sourcePhotonLeftReader branch e.val (sourceSheet branch n unit e.val) n
        (sourceActualPreparedCurrent qs pSL pSR a b c d mu S) •
      sourceNoetherFieldMeter qd pDL pDR lambda T
        (sourceNativeFrequencyPolarization branch e.val (sourceSheet branch n unit e.val) n) := by
  filter_upwards [sourceWholePhotonResidue_factor branch n unit] with e factor
  intro qs pSL pSR a b c d mu S
  ext i j
  rw [sourceNoetherFieldMeter_generated qd pDL pDR lambda T _ left right,
    sourceNoetherFieldMeter_generated qd pDL pDR lambda T _ left right]
  simp only [sourcePreparedChargeUnitMatrix,Matrix.mul_diagonal,Matrix.smul_apply,
    sourcePreparedFieldMatrix,smul_eq_mul]
  rw [sourceWholePhotonFrequencyResidue,Matrix.smul_mulVec,factor,smul_comm,
    ←sourceNativeFrequencyPolarization,map_smul,smul_eq_mul]
  ring

end LowEnergy.PreparationPhysicalActualNoetherVertexReturn
