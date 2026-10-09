import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceActualGaussCharge

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
local instance actualGaussCurrentIndex : DecidableEq Quantum.Index:=Classical.decEq _
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

/-- Both coefficients are the paid inner products of the original four preparations with their independent moving carriers. -/
def sourceActualPreparedWeight (pL pR : PhysicalMomentum) (sL eL sR eR : Fin 2)
    (a b : RestStateIndex) : ℂ :=
  star (sourceChargedMovingCoefficient pL sL eL a)*sourceChargedMovingCoefficient pR sR eR b

theorem sourceActualGaussRead_poles (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (sL eL sR eR : Fin 2) (A : H→L[ℂ]H) :
    sourceQuantumChargedRead q sL eL sR eR A=
      ∑a : RestStateIndex,∑b : RestStateIndex,
        sourceActualPreparedWeight pL pR sL eL sR eR a b*sourcePoleRead q.epsilon q.precision pL pR a b A := by
  simp only [sourceQuantumChargedRead,ContinuousLinearMap.comp_apply,ContinuousLinearMap.apply_apply,innerSL_apply_apply]
  rw [sourceChargedGaussPrepared_moving q.epsilon q.precision pL sL eL,
    sourceChargedGaussPrepared_moving q.epsilon q.precision pR sR eR]
  simp only [map_sum,map_smul,sum_inner,inner_sum,inner_smul_left,inner_smul_right,
    starRingEnd_apply,Finset.mul_sum,sourceActualPreparedWeight,sourcePoleRead_actual,mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

def sourceActualPreparedDetector (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (sL eL sR eR : Fin 2) (lambda : ℂ) (T : ℝ) : (Fin 289→ℂ)→L[ℂ]ℂ :=
  ∑a : RestStateIndex,∑b : RestStateIndex,
    sourceActualPreparedWeight 0 0 sL eL sR eR a b • sourceCommonDetector q pL pR a b lambda T

def sourceActualPreparedCurrent (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (sL eL sR eR : Fin 2) (lambda : ℂ) (T : ℝ) : Fin 289→ℂ :=
  ∑a : RestStateIndex,∑b : RestStateIndex,
    sourceActualPreparedWeight 0 0 sL eL sR eR a b • returnedCurrentWindow q pL pR a b lambda T

/-- The generated detector contracts its actual all-eight-by-eight original current. -/
theorem sourceActualPreparedDetector_current (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (sL eL sR eR : Fin 2) (lambda : ℂ) (T : ℝ) (V : Fin 289→ℂ) :
    sourceActualPreparedDetector q pL pR sL eL sR eR lambda T V=
      ∑i : Fin 289,sourceActualPreparedCurrent q pL pR sL eL sR eR lambda T i*V i := by
  simp only [sourceActualPreparedDetector,sum_apply,smul_apply,sourceCommonDetector_current,
    sourceActualPreparedCurrent,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,Finset.sum_mul,mul_assoc]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]

/-- The unchanged full five-factor matter response is integrated at the actual finite source window. -/
def sourceActualPreparedKernel (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (lambda : ℂ) (T : ℝ) (V : Fin 289→ℂ) : H→L[ℂ]H :=
  ∫t in (0:ℝ)..T,laplaceWeight lambda t • (∑i : Fin 289,V i • actualJointKernel q pL pR t i)

private theorem kernel_integrable (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (lambda : ℂ) (T : ℝ) (V : Fin 289→ℂ) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    IntervalIntegrable (fun t : ℝ=>laplaceWeight lambda t •
      (∑i : Fin 289,V i • actualJointKernel q pL pR t i)) volume 0 T := by
  have argument : Continuous (fun t : ℝ=>(pL,pR,t)) := continuous_const.prodMk (continuous_const.prodMk continuous_id)
  have kernel (i : Fin 289) := (actualJointKernel_continuous q i nonrealL nonrealR).comp argument
  have sum := continuous_finsetSum Finset.univ (fun i _=>(kernel i).const_smul (V i))
  have weight : Continuous (laplaceWeight lambda) := by unfold laplaceWeight;fun_prop
  exact (weight.smul sum).intervalIntegrable _ _

/-- Both actual prepared ends enter the same full289 detector; no identification of eigenbasis labels is needed. -/
theorem sourceActualPreparedDetector_action (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (sL eL sR eR : Fin 2) (lambda : ℂ) (T : ℝ) (V : Fin 289→ℂ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    sourceActualPreparedDetector q pL pR sL eL sR eR lambda T V=
      -sourceQuantumChargedRead q sL eL sR eR (sourceActualPreparedKernel q pL pR lambda T V) := by
  have entry (a b : RestStateIndex) : sourceCommonDetector q pL pR a b lambda T V=
      -sourcePoleRead q.epsilon q.precision 0 0 a b (sourceActualPreparedKernel q pL pR lambda T V) := by
    rw [sourceCommonDetector_action q pL pR a b lambda T V nonrealL nonrealR]
    simp only [mul_neg,intervalIntegral.integral_neg]
    congr 1
    have exchange := (sourcePoleRead q.epsilon q.precision 0 0 a b).intervalIntegral_comp_comm
      (kernel_integrable q pL pR lambda T V nonrealL nonrealR)
    simpa only [sourceActualPreparedKernel,map_smul,smul_eq_mul] using exchange
  rw [sourceActualGaussRead_poles q 0 0]
  simp only [sourceActualPreparedDetector,sum_apply,smul_apply,smul_eq_mul,entry,mul_neg,Finset.sum_neg_distrib]

/-- Independent physical momenta use their own actual source overlap coefficients at both ends. -/
theorem sourceActualPreparedDetector_moving (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (sL eL sR eR : Fin 2) (lambda : ℂ) (T : ℝ) (V : Fin 289→ℂ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    sourceActualPreparedDetector q pL pR sL eL sR eR lambda T V=
      -(∑a : RestStateIndex,∑b : RestStateIndex,
        sourceActualPreparedWeight pL pR sL eL sR eR a b*
          sourcePoleRead q.epsilon q.precision pL pR a b (sourceActualPreparedKernel q pL pR lambda T V)) := by
  rw [sourceActualPreparedDetector_action q pL pR sL eL sR eR lambda T V nonrealL nonrealR,
    sourceActualGaussRead_poles q pL pR]

/-- The static source tensor is observed by the actual four-column preparation, including every original channel. -/
theorem sourceActualPreparedDetector_static (qd : PhysicalResponsePoint) (pDL pDR : PhysicalMomentum)
    (sL eL sR eR : Fin 2) (lambda : ℂ) (T : ℝ)
    (q : PhysicalResponsePoint) (n : PhysicalMomentum) (l r : RestStateIndex) :
    sourceActualPreparedDetector qd pDL pDR sL eL sR eR lambda T (sourceCommonStaticSimple q n l r)=
      (spatialSquare n:ℂ)⁻¹*sourceActualPreparedDetector qd pDL pDR sL eL sR eR lambda T
        (sourceCommonCoulombTensor q n l r) := by
  rw [sourceCommonStaticSimple_green,map_smul,smul_eq_mul]

/-- Both independent actual preparations factor the same full source frequency residue, with its original left reader. -/
theorem sourceActualPreparedDetector_frequency (qd : PhysicalResponsePoint) (pDL pDR : PhysicalMomentum)
    (sL eL sR eR : Fin 2) (lambda : ℂ) (T : ℝ)
    (qs : PhysicalResponsePoint) (pSL pSR : PhysicalMomentum) (a b c d : Fin 2) (mu : ℂ) (S : ℝ)
    (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,
      sourceActualPreparedDetector qd pDL pDR sL eL sR eR lambda T
        (sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n*ᵥ
          sourceActualPreparedCurrent qs pSL pSR a b c d mu S)=
      sourcePhotonLeftReader branch e.val (sourceSheet branch n unit e.val) n
        (sourceActualPreparedCurrent qs pSL pSR a b c d mu S)*
      sourceActualPreparedDetector qd pDL pDR sL eL sR eR lambda T
        (sourceNativeFrequencyPolarization branch e.val (sourceSheet branch n unit e.val) n) := by
  filter_upwards [sourceWholePhotonResidue_factor branch n unit] with e factor
  rw [sourceWholePhotonFrequencyResidue,Matrix.smul_mulVec,factor,smul_comm,
    ←sourceNativeFrequencyPolarization,map_smul,smul_eq_mul]

end LowEnergy.PreparationPhysicalActualGaussChargeCurrent
