import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceActualPreparedDetector

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalActualGaussChargeCurrent
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
local instance actualGaussNoetherIndex : DecidableEq Quantum.Index:=Classical.decEq _
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

open PreparationVacuumJointFieldResponse PreparationVacuumRawJointFeedback

attribute [local irreducible] sourceActualGaussCharge sourceActualGaussChargeMatrix
  sourceChargedGaussPrepared sourceActualPreparedKernel actualJointKernel
  physicalTime jointResolvent PreparationVacuumRawJointFeedback.rawReader sourcePhaseNoether sourceNativeOriginGenerator

/-- Charge acts on the two actual normalized external preparations, while the entire operator between them remains free to mix charges. -/
theorem sourceActualPreparedCharge_ends (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (A : H→L[ℂ]H) :
    sourceQuantumChargedRead q sL eL sR eR (sourceActualGaussCharge*A)=
      (sourceActualPhaseCharge eL:ℂ)*sourceQuantumChargedRead q sL eL sR eR A ∧
    sourceQuantumChargedRead q sL eL sR eR (A*sourceActualGaussCharge)=
      (sourceActualPhaseCharge eR:ℂ)*sourceQuantumChargedRead q sL eL sR eR A := by
  simp only [sourceQuantumChargedRead,ContinuousLinearMap.comp_apply,ContinuousLinearMap.apply_apply,
    innerSL_apply_apply,mul_apply_eq_comp]
  constructor
  · rw [←sourceActualGaussCharge_pair,sourceActualGaussCharge_prepared,inner_smul_left]
    simp
  · rw [sourceActualGaussCharge_prepared,map_smul,inner_smul_right]

/-- The actual full response obeys the prepared charge commutator identity. -/
theorem sourceActualPreparedCharge_commutator (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (A : H→L[ℂ]H) :
    sourceQuantumChargedRead q sL eL sR eR (sourceActualGaussCharge*A-A*sourceActualGaussCharge)=
      ((sourceActualPhaseCharge eL:ℂ)-(sourceActualPhaseCharge eR:ℂ))*
        sourceQuantumChargedRead q sL eL sR eR A := by
  rw [map_sub,(sourceActualPreparedCharge_ends q sL eL sR eR A).1,
    (sourceActualPreparedCharge_ends q sL eL sR eR A).2,sub_mul]

/-- The measured source h-charge on either actual preparation returns through the same full field detector. -/
theorem sourceActualPreparedDetector_charge (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (sL eL sR eR : Fin 2) (lambda : ℂ) (T : ℝ) (V : Fin 289→ℂ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    (-(Stage10.ActionNormalization.phaseMomentum:ℂ)*sourceQuantumChargedRead q sL eL sR eR
        (sourceActualGaussCharge*sourceActualPreparedKernel q pL pR lambda T V),
      -(Stage10.ActionNormalization.phaseMomentum:ℂ)*sourceQuantumChargedRead q sL eL sR eR
        (sourceActualPreparedKernel q pL pR lambda T V*sourceActualGaussCharge))=
    ((Stage10.ActionNormalization.phaseMomentum:ℂ)*(sourceActualPhaseCharge eL:ℂ)*
        sourceActualPreparedDetector q pL pR sL eL sR eR lambda T V,
      (Stage10.ActionNormalization.phaseMomentum:ℂ)*(sourceActualPhaseCharge eR:ℂ)*
        sourceActualPreparedDetector q pL pR sL eL sR eR lambda T V) := by
  rw [(sourceActualPreparedCharge_ends q sL eL sR eR _).1,
    (sourceActualPreparedCharge_ends q sL eL sR eR _).2,
    sourceActualPreparedDetector_action q pL pR sL eL sR eR lambda T V nonrealL nonrealR]
  congr 1 <;> ring

/-- Every Green, time, and full289 field-reader commutator is retained on its original side. -/
def sourceActualPreparedNoetherExchange (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (V : Fin 289→ℂ) (t : ℝ) : H→L[ℂ]H :=
  let L:=physicalTime pL q.F (-t) 0
  let G:=jointResolvent pL q.F q.z 0
  let R:=∑i : Fin 289,V i • PreparationVacuumRawJointFeedback.rawReader (fieldUnit i) pR q.F 0
  let K:=jointResolvent pR q.F q.w 0
  let U:=physicalTime pR q.F t 0
  (sourceActualGaussCharge*L-L*sourceActualGaussCharge)*G*R*K*U+
  L*(sourceActualGaussCharge*G-G*sourceActualGaussCharge)*R*K*U+
  L*G*(sourceActualGaussCharge*R-R*sourceActualGaussCharge)*K*U+
  L*G*R*(sourceActualGaussCharge*K-K*sourceActualGaussCharge)*U+
  L*G*R*K*(sourceActualGaussCharge*U-U*sourceActualGaussCharge)

private theorem product_bracket {R : Type*} [Ring R] (Q L G A K U : R) :
    (Q*L-L*Q)*G*A*K*U+L*(Q*G-G*Q)*A*K*U+L*G*(Q*A-A*Q)*K*U+
      L*G*A*(Q*K-K*Q)*U+L*G*A*K*(Q*U-U*Q)=Q*(L*G*A*K*U)-(L*G*A*K*U)*Q := by
  noncomm_ring

theorem sourceActualPreparedNoetherExchange_return (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (V : Fin 289→ℂ) (t : ℝ) :
    sourceActualPreparedNoetherExchange q pL pR V t=
      sourceActualGaussCharge*(∑i : Fin 289,V i • actualJointKernel q pL pR t i)-
      (∑i : Fin 289,V i • actualJointKernel q pL pR t i)*sourceActualGaussCharge := by
  have product : (∑i : Fin 289,V i • actualJointKernel q pL pR t i)=
      physicalTime pL q.F (-t) 0*jointResolvent pL q.F q.z 0*
        (∑i : Fin 289,V i • PreparationVacuumRawJointFeedback.rawReader (fieldUnit i) pR q.F 0)*
          jointResolvent pR q.F q.w 0*physicalTime pR q.F t 0 := by
    simp only [actualJointKernel,Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc]
  rw [product,sourceActualPreparedNoetherExchange]
  exact product_bracket _ _ _ _ _ _

/-- This equality retains both time transports and both independent material resolvents; it does not assume charge conservation for an individual factor. -/
theorem sourceActualPreparedNoether_ward (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (sL eL sR eR : Fin 2) (lambda : ℂ) (T : ℝ) (V : Fin 289→ℂ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    ((sourceActualPhaseCharge eL:ℂ)-(sourceActualPhaseCharge eR:ℂ))*
      sourceActualPreparedDetector q pL pR sL eL sR eR lambda T V=
      -(∫t in (0:ℝ)..T,laplaceWeight lambda t*
        sourceQuantumChargedRead q sL eL sR eR (sourceActualPreparedNoetherExchange q pL pR V t)) := by
  rw [sourceActualPreparedDetector_action q pL pR sL eL sR eR lambda T V nonrealL nonrealR]
  have argument : Continuous (fun t : ℝ=>(pL,pR,t)) := continuous_const.prodMk (continuous_const.prodMk continuous_id)
  have kernel (i : Fin 289) := (actualJointKernel_continuous q i nonrealL nonrealR).comp argument
  have sum := continuous_finsetSum Finset.univ (fun i _=>(kernel i).const_smul (V i))
  have weight : Continuous (laplaceWeight lambda) := by unfold laplaceWeight;fun_prop
  have integrable : IntervalIntegrable (fun t : ℝ=>laplaceWeight lambda t •
      (∑i : Fin 289,V i • actualJointKernel q pL pR t i)) volume 0 T :=
    (weight.smul sum).intervalIntegrable 0 T
  have exchange := (sourceQuantumChargedRead q sL eL sR eR).intervalIntegral_comp_comm integrable
  have exchange' : (∫t in (0:ℝ)..T,sourceQuantumChargedRead q sL eL sR eR
      (laplaceWeight lambda t • (∑i : Fin 289,V i • actualJointKernel q pL pR t i)))=
        sourceQuantumChargedRead q sL eL sR eR (sourceActualPreparedKernel q pL pR lambda T V) := by
    simpa only [sourceActualPreparedKernel] using exchange
  simp only [map_smul,smul_eq_mul] at exchange'
  rw [←exchange',mul_neg]
  simp_rw [sourceActualPreparedNoetherExchange_return,sourceActualPreparedCharge_commutator]
  congr 1
  rw [←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  ring

/-- The actual four-column detector's complete Gauss weight is generated from all original source-pole pairs. -/
def sourceActualPreparedGaussWeight (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2) (T : ℝ) : ℂ :=
  ∑a : RestStateIndex,∑b : RestStateIndex,
    sourceActualPreparedWeight 0 0 sL eL sR eR a b*actualGaussWeight q a b T

theorem sourceActualPreparedDetector_gauss (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (T : ℝ) (branch : Fin 2) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    sourceActualPreparedDetector q 0 0 sL eL sR eR 0 T (nativeBranchVector branch)=
      if branch=0 then sourceActualPreparedGaussWeight q sL eL sR eR T else 0 := by
  simp only [sourceActualPreparedDetector,sum_apply,smul_apply,smul_eq_mul,
    sourceCommonDetector_gauss q _ _ T branch nonrealL nonrealR]
  split_ifs <;> simp [sourceActualPreparedGaussWeight]

/-- The complete Gauss weight and the source charge difference meet in the actual Green/time/reader Ward response. -/
theorem sourceActualPreparedGauss_noether (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (T : ℝ) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    ((sourceActualPhaseCharge eL:ℂ)-(sourceActualPhaseCharge eR:ℂ))*
      sourceActualPreparedGaussWeight q sL eL sR eR T=
      -(∫t in (0:ℝ)..T,sourceQuantumChargedRead q sL eL sR eR
        (sourceActualPreparedNoetherExchange q 0 0 (nativeBranchVector 0) t)) := by
  have generated:=sourceActualPreparedNoether_ward q 0 0 sL eL sR eR 0 T
    (nativeBranchVector 0) nonrealL nonrealR
  rw [sourceActualPreparedDetector_gauss q sL eL sR eR T 0 nonrealL nonrealR,if_pos rfl] at generated
  simpa only [laplaceWeight,zero_mul,neg_zero,Complex.exp_zero,one_mul] using generated

end LowEnergy.PreparationPhysicalActualGaussChargeCurrent
