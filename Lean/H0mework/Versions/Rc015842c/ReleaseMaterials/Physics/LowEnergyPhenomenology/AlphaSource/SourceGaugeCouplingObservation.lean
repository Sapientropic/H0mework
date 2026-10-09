import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceGaugeWeightedUnitReader

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalGaugeMomentumCoupling
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
open scoped BigOperators Matrix Topology InnerProductSpace Matrix.Norms.L2Operator
local instance actualGaugeCouplingIndex : DecidableEq Quantum.Index:=Classical.decEq _
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

open PreparationPhysicalActualFieldNoetherResponse PreparationVacuumPhysicalModeChargeRead
open SU7ExteriorMatterGaugeCovariantJet StageNineFullDiracAdjointLocalOperator
open GaussComposite GaussComposite.PhysicalModeEMCurrent SourceQuantumScalarChart

open PreparationVacuumPhysicalElectromagneticDirection PreparationVacuumLowerClassical
open PreparationVacuumOriginalDensity SourceQuantumScalarOrbitDimensions PreparationCoordinates StageNineDynamicBreakingVacuum

open PreparationPhysicalPhaseGaugeRealization PreparationVacuumNoetherChart
open PreparationPhysicalVoltageNoether PreparationPhysicalActionUnits
open PreparationPhysicalVoltageNoetherChargeReturn PreparationVacuumNoetherOrdinaryWard
local instance : NormedAlgebra ℝ SourceMatrix := NormedAlgebra.restrictScalars ℝ ℂ _

open PreparationVacuumFullElectricWard PreparationVacuumFullFieldRiesz
open GaussCoreDifferential CanonicalGradedCurrent GaussFockPair PreparationVacuumSourceActionJets
attribute [local irreducible] noetherReader noetherReaderContact

open PreparationPhysicalCommonObservableUnits PreparationVacuumFieldConstraintResponse
attribute [local irreducible] actualJointKernel sourceUnitRead sourceActualUnitLegRead sourcePhaseGaugeField
  sourceActualLegNormalization sourceActualLegCorrection sourceActualPreparedDetector sourceNativeFrequencyPolarization

/-- The retained W is the original physical time momentum matrix in the source action unit. -/
theorem sourceGaugeMomentumWeight_clock (base : ActionState) :
    sourceGaugeMomentumWeight base=(ActionNormalization.actionScale:ℂ) • sourcePreparedTimeMatrix base := by
  rw [sourcePreparedTimeMatrix_normalized]
  rfl

/-- The generated unit reader carries its own physical current and both independent Green-time legs. -/
def sourceGaugeUnitObservation (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (pL pR : PhysicalMomentum) (lambda : ℂ) (T : ℝ) : ℂ :=
  ∫t in (0:ℝ)..T,laplaceWeight lambda t*
    (-sourceUnitRead q sL eL sR eR (sourceGaugeUnitKernel q pL pR t))

theorem sourceGaugePreparedWindow_momentum (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (pL pR : PhysicalMomentum) (lambda : ℂ) (T : ℝ) :
    (∫t in (0:ℝ)..T,laplaceWeight lambda t*
      (-sourceUnitRead q sL eL sR eR
        (fiveKernel (sourcePhaseGaugeField 0) pR (pL-pR) q.F q.z q.w t 0)))=
      (ActionNormalization.phaseMomentum:ℂ)*sourceGaugeUnitObservation q sL eL sR eR pL pR lambda T := by
  simp only [sourceGaugeActualPrepared_momentum,sourceGaugeUnitObservation]
  rw [←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  ring

/-- Full observed response divided by its original action and propagation speed; no angular or field average is taken. -/
def sourceGaugeCouplingRead (branch : Fin 2) (qd : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (lambda : ℂ) (T : ℝ) (V : Fin 289→ℂ) : ℂ :=
  sourceActualUnitFieldRead qd sL eL sR eR lambda T V/
    ((ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ)

theorem sourceGaugeCouplingRead_generated (branch : Fin 2) (qd : PhysicalResponsePoint)
    (sL eL sR eR : Fin 2) (lambda : ℂ) (T : ℝ) (V : Fin 289→ℂ)
    (left : qd.z.im≠0) (right : qd.w.im≠0) :
    sourceGaugeCouplingRead branch qd sL eL sR eR lambda T V=
      sourceActualLegNormalization qd sL eL sR eR*
        (sourceActualPreparedDetector qd 0 0 sL eL sR eR lambda T V-
          sourceActualLegCorrection qd sL eL sR eR (sourceActualPreparedKernel qd 0 0 lambda T V))/
            ((ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ) := by
  rw [sourceGaugeCouplingRead,sourceActualUnitField_return qd sL eL sR eR lambda T V left right]

private theorem gauge_actual_kernel (q : PhysicalResponsePoint) (t : ℝ) :
    (∑i : Fin 289,(sourcePhaseGaugeField 0 i:ℂ) • actualJointKernel q 0 0 t i)=
      fiveKernel (sourcePhaseGaugeField 0) 0 0 q.F q.z q.w t 0 := by
  have generated:=sourceModeGaussKernel_generated (fun i=>(sourcePhaseGaugeField 0 i:ℂ)) q 0 0 t
  have kernel (i : Fin 289) : actualJointKernel q 0 0 t i=fiveKernel (fieldUnit i) 0 0 q.F q.z q.w t 0 := by
    simp only [actualJointKernel,fiveKernel,zero_add]
  simp only [sub_self] at generated
  simp only [kernel]
  rw [←generated,sourceModeGaussKernel,sourceModeGaussReader_real]
  simp only [fiveKernel,sub_self,add_zero]

/-- The h-normalized coupling consumer actually accepts the generated weighted gauge current, cancelling h once. -/
theorem sourceGaugeCouplingRead_unit (branch : Fin 2) (q : PhysicalResponsePoint)
    (sL eL sR eR : Fin 2) (lambda : ℂ) (T : ℝ)
    (left : q.z.im≠0) (right : q.w.im≠0) :
    sourceGaugeCouplingRead branch q sL eL sR eR lambda T (fun i=>(sourcePhaseGaugeField 0 i:ℂ))=
      sourceGaugeUnitObservation q sL eL sR eR 0 0 lambda T/(sourceSpeed branch:ℂ) := by
  have continuous : Continuous (fun t : ℝ=>laplaceWeight lambda t •
      (∑i : Fin 289,(sourcePhaseGaugeField 0 i:ℂ) • actualJointKernel q 0 0 t i)) := by
    have argument : Continuous (fun t : ℝ=>((0:PhysicalMomentum),(0:PhysicalMomentum),t)) :=
      continuous_const.prodMk (continuous_const.prodMk continuous_id)
    have kernel (i : Fin 289) : Continuous (fun t : ℝ=>actualJointKernel q 0 0 t i) := by
      convert (actualJointKernel_continuous q i left right).comp argument using 1
      rfl
    have weight : Continuous (laplaceWeight lambda) := by unfold laplaceWeight;fun_prop
    exact weight.smul (continuous_finsetSum Finset.univ (fun i _=>(kernel i).const_smul (sourcePhaseGaugeField 0 i:ℂ)))
  have integrable : IntervalIntegrable (fun t : ℝ=>laplaceWeight lambda t •
      (∑i : Fin 289,(sourcePhaseGaugeField 0 i:ℂ) • actualJointKernel q 0 0 t i)) volume 0 T :=
    continuous.intervalIntegrable 0 T
  have integral := (sourceUnitRead q sL eL sR eR).intervalIntegral_comp_comm integrable
  simp only [sourceUnitRead_original,map_smul,smul_eq_mul] at integral
  unfold sourceGaugeCouplingRead sourceActualUnitFieldRead sourceActualPreparedKernel
  rw [←integral,←intervalIntegral.integral_neg]
  simp_rw [←sourceUnitRead_original,gauge_actual_kernel,←mul_neg]
  have window:=sourceGaugePreparedWindow_momentum q sL eL sR eR 0 0 lambda T
  simp only [sub_self] at window
  rw [window]
  have nonzero : (ActionNormalization.phaseMomentum:ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr ActionNormalization.phaseMomentum_positive.ne'
  rw [Complex.ofReal_mul]
  field_simp [nonzero]

/-- The source physical clock and the actual pole sheet, rather than an external speed/unit, fix the denominator. -/
theorem sourceGaugeCouplingSpeed_return (branch : Fin 2) (qd : PhysicalResponsePoint)
    (sL eL sR eR : Fin 2) (lambda : ℂ) (T : ℝ) (V : Fin 289→ℂ)
    (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    Tendsto (fun e : scaleDomain=>sourceActualUnitFieldRead qd sL eL sR eR lambda T V/
      ((ActionNormalization.phaseMomentum*sourceObservablePhaseSpeed branch n unit e:ℝ):ℂ)) scaleApproach
      (𝓝 (sourceGaugeCouplingRead branch qd sL eL sR eR lambda T V)) := by
  have speed:=(sourceObservablePhaseSpeed_limit branch n unit).const_mul ActionNormalization.phaseMomentum
  have cast:=Complex.continuous_ofReal.continuousAt.tendsto.comp speed
  have nonzero : ((ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (mul_pos ActionNormalization.phaseMomentum_positive (sourceSpeed_positive branch)).ne'
  exact tendsto_const_nhds.div cast nonzero

/-- All actual source endpoints, all original 64 source weights and all three static channels remain. -/
def sourceGaugeActualCoulombField (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (n : PhysicalMomentum) : Fin 289→ℂ :=
  ∑a : RestStateIndex,∑b : RestStateIndex,
    sourceActualPreparedWeight 0 0 sL eL sR eR a b • sourceCommonCoulombTensor q n a b

def sourceGaugeStaticCouplingTensor (branch : Fin 2) (qd q : PhysicalResponsePoint)
    (dSL dEL dSR dER sL eL sR eR : Fin 2) (T : ℝ) (n : PhysicalMomentum) : ℂ :=
  sourceGaugeCouplingRead branch qd dSL dEL dSR dER 0 T (sourceGaugeActualCoulombField q sL eL sR eR n)

theorem sourceGaugeStaticCoupling_return (branch : Fin 2) (qd q : PhysicalResponsePoint)
    (dSL dEL dSR dER sL eL sR eR : Fin 2) (T : ℝ) (n : PhysicalMomentum)
    (left : qd.z.im≠0) (right : qd.w.im≠0) :
    sourceGaugeStaticCouplingTensor branch qd q dSL dEL dSR dER sL eL sR eR T n=
      sourceActualLegNormalization qd dSL dEL dSR dER*
        ((∑a : RestStateIndex,∑b : RestStateIndex,sourceActualPreparedWeight 0 0 sL eL sR eR a b*
          sourceActualPreparedDetector qd 0 0 dSL dEL dSR dER 0 T (sourceCommonCoulombTensor q n a b))-
        sourceActualLegCorrection qd dSL dEL dSR dER
          (sourceActualPreparedKernel qd 0 0 0 T (sourceGaugeActualCoulombField q sL eL sR eR n)))/
            ((ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ) := by
  rw [sourceGaugeStaticCouplingTensor,sourceGaugeCouplingRead_generated branch qd dSL dEL dSR dER 0 T _ left right]
  have detector : sourceActualPreparedDetector qd 0 0 dSL dEL dSR dER 0 T
      (sourceGaugeActualCoulombField q sL eL sR eR n)=
      ∑a : RestStateIndex,∑b : RestStateIndex,sourceActualPreparedWeight 0 0 sL eL sR eR a b*
        sourceActualPreparedDetector qd 0 0 dSL dEL dSR dER 0 T (sourceCommonCoulombTensor q n a b) := by
    simp only [sourceGaugeActualCoulombField,map_sum,map_smul,smul_eq_mul]
  rw [detector]

/-- The whole source angular dependence is retained; only positive radial scaling is removed by the original Coulomb coefficient. -/
theorem sourceGaugeStaticCoupling_radial (branch : Fin 2) (qd q : PhysicalResponsePoint)
    (dSL dEL dSR dER sL eL sR eR : Fin 2) (T : ℝ) (n : PhysicalMomentum) (r : ℝ) (positive : 0<r) :
    sourceGaugeStaticCouplingTensor branch qd q dSL dEL dSR dER sL eL sR eR T (r • n)=
      sourceGaugeStaticCouplingTensor branch qd q dSL dEL dSR dER sL eL sR eR T n := by
  simp only [sourceGaugeStaticCouplingTensor,sourceGaugeActualCoulombField,sourceCommonCoulombTensor_radial q n r positive]

/-- The actual physical-frequency field is returned through all 36 original curvature rows. -/
def sourceGaugePhotonCurvature (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (pL pR : PhysicalMomentum) (lambda : ℂ) (T epsilon sigma : ℝ) (n : PhysicalMomentum) : Fin 36→ℂ :=
  originalReader36 (frequencyRay epsilon sigma n)*ᵥ
    sourcePhaseGaugePhotonField q sL eL sR eR pL pR lambda T epsilon sigma n

theorem sourceGaugePhotonCurvature_generated (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (pL pR : PhysicalMomentum) (lambda : ℂ) (T : ℝ) (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,
      sourceGaugePhotonCurvature q sL eL sR eR pL pR lambda T e.val (sourceSheet branch n unit e.val) n=
        sourcePhotonLeftReader branch e.val (sourceSheet branch n unit e.val) n
          (sourceActualPreparedCurrent q pL pR sL eL sR eR lambda T) •
          (originalReader36 (frequencyRay e.val (sourceSheet branch n unit e.val) n)*ᵥ
            sourceNativeFrequencyPolarization branch e.val (sourceSheet branch n unit e.val) n) := by
  filter_upwards [sourcePhaseGaugePhotonField_factor q sL eL sR eR pL pR lambda T branch n unit] with e factor
  rw [sourceGaugePhotonCurvature,factor,Matrix.mulVec_smul]

/-- This complete current-current pole observation is normalized on the same actual unit legs and clock. -/
def sourceGaugePhotonCoupling (branch : Fin 2) (qd q : PhysicalResponsePoint)
    (dSL dEL dSR dER sL eL sR eR : Fin 2) (pL pR : PhysicalMomentum)
    (lambdaD lambdaS : ℂ) (T epsilon sigma : ℝ) (n : PhysicalMomentum) : ℂ :=
  sourceGaugeCouplingRead branch qd dSL dEL dSR dER lambdaD T
    (sourcePhaseGaugePhotonField q sL eL sR eR pL pR lambdaS T epsilon sigma n)

/-- Source-current visibility, complete physical polarization and full exterior corrections occur in one observable. -/
theorem sourceGaugePhotonCoupling_return (branch : Fin 2) (qd q : PhysicalResponsePoint)
    (dSL dEL dSR dER sL eL sR eR : Fin 2) (pL pR : PhysicalMomentum)
    (lambdaD lambdaS : ℂ) (T : ℝ) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (left : qd.z.im≠0) (right : qd.w.im≠0) :
    ∀ᶠ e in scaleApproach,
      sourceGaugePhotonCoupling branch qd q dSL dEL dSR dER sL eL sR eR pL pR lambdaD lambdaS T
        e.val (sourceSheet branch n unit e.val) n=
      sourceActualLegNormalization qd dSL dEL dSR dER*
        (sourcePhotonLeftReader branch e.val (sourceSheet branch n unit e.val) n
            (sourceActualPreparedCurrent q pL pR sL eL sR eR lambdaS T)*
          sourceActualPreparedDetector qd 0 0 dSL dEL dSR dER lambdaD T
            (sourceNativeFrequencyPolarization branch e.val (sourceSheet branch n unit e.val) n)-
          sourceActualLegCorrection qd dSL dEL dSR dER
            (sourceActualPreparedKernel qd 0 0 lambdaD T
              (sourcePhaseGaugePhotonField q sL eL sR eR pL pR lambdaS T e.val (sourceSheet branch n unit e.val) n)))/
        ((ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ) := by
  filter_upwards [sourcePhaseGaugePhotonField_factor q sL eL sR eR pL pR lambdaS T branch n unit] with e factor
  rw [sourceGaugePhotonCoupling,sourceGaugeCouplingRead_generated branch qd dSL dEL dSR dER lambdaD T _ left right]
  have detector := congrArg (sourceActualPreparedDetector qd 0 0 dSL dEL dSR dER lambdaD T) factor
  simp only [map_smul,smul_eq_mul] at detector
  rw [detector]

end LowEnergy.PreparationPhysicalGaugeMomentumCoupling
