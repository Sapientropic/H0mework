import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourcePhaseGaugeField
import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalPoleCharge

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalPhaseGaugeRealization
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
local instance actualGaugeObservationIndex : DecidableEq Quantum.Index:=Classical.decEq _
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

def sourcePhaseGaugeCurrent (mu : Fin 4) : YangMills.FullPairing.Mother :=
  Complex.I • (diracMatrixMatterAction (diracGamma mu)).comp sourcePhaseGaugeGenerator

def sourcePhaseGaugeCurrentDifference (mu : Fin 4) : YangMills.FullPairing.Mother :=
  Complex.I • (diracMatrixMatterAction (diracGamma mu)).comp sourcePhaseGaugeDifference

/-- The current is produced by the actual original full289 connection field. -/
theorem sourcePhaseGaugeField_current (mu : Fin 4) :
    sourceModeCurrent (fun j=>(sourcePhaseGaugeField mu j:ℂ)) mu=sourcePhaseGaugeCurrent mu := by
  have mother : sourceModeMother (fun j=>(sourcePhaseGaugeField mu j:ℂ)) mu=sourcePhaseGaugeGenerator := by
    apply Quantum.operatorMatrix.injective
    rw [sourceModeMother_generated,sourcePhaseGaugeField_connection,if_pos rfl]
  rw [sourceModeCurrent,mother]
  rfl

theorem sourcePhaseGaugeCurrent_full :
    sourcePhaseNoether=sourcePhaseGaugeCurrent 0+sourcePhaseGaugeCurrentDifference 0 := by
  rw [sourcePhaseNoether,sourcePhaseGaugeGenerator_full]
  simp only [sourcePhaseGaugeCurrent,sourcePhaseGaugeCurrentDifference,LinearMap.comp_add,smul_add]
  rfl

theorem sourcePhaseGaugeCurrent_column (side edge : Fin 2) :
    sourcePhaseGaugeCurrent 0 (sourceChargedRestriction side edge)=
      sourcePhaseNoether (sourceChargedRestriction side edge) := by
  simp only [sourcePhaseGaugeCurrent,sourcePhaseNoether,LinearMap.smul_apply,LinearMap.comp_apply,
    sourcePhaseGauge_actualColumn,sourceActualRestriction_generator]
  rfl

/-- Actual independent dual and source action unit generate the unit/neutral read; no charge size is selected. -/
theorem sourcePhaseGaugeCurrent_actual (side edge : Fin 2) :
    actual.conjugateMatter 0
      (canonicalDual (actualRestStatePreparation (sourceChargedRestIndex side edge))
        (sourceModeCurrent (fun j=>(sourcePhaseGaugeField 0 j:ℂ)) 0
          (actualRestStatePreparation (sourceChargedRestIndex side edge) (actual.matter 0))))=
      (Stage10.ActionNormalization.phaseMomentum:ℂ)*(sourceActualPhaseCharge edge:ℂ) := by
  have reconstructed : actual.matter 0=(2:ℂ) • Stage9DEF.Compatibility.embed (Source.vector 0) := by
    rw [←Source.amplitude_reconstruction 0,←map_smul]
    congr 1
    ext spin color
    exact Source.amplitude_eq_twice_vector 0 (spin,color)
  have argument : actualRestStatePreparation (sourceChargedRestIndex side edge) (actual.matter 0)=
      (2:ℂ) • sourceChargedRestriction side edge := by
    rw [reconstructed,map_smul]
    rfl
  have returned : sourcePhaseGaugeCurrent 0
      (actualRestStatePreparation (sourceChargedRestIndex side edge) (actual.matter 0))=
      sourcePhaseNoether (actualRestStatePreparation (sourceChargedRestIndex side edge) (actual.matter 0)) := by
    rw [argument,map_smul,map_smul,sourcePhaseGaugeCurrent_column]
  rw [sourcePhaseGaugeField_current,returned]
  exact sourceActualIndependent_current side edge

private theorem gauge_matrix_smul (c : ℂ) (A : YangMills.FullPairing.Mother) :
    Quantum.operatorMatrix (c • A)=c • Quantum.operatorMatrix A :=
  Quantum.operatorMatrix.toLinearEquiv.map_smul c A

private theorem gauge_matrix_add (A B : YangMills.FullPairing.Mother) :
    Quantum.operatorMatrix (A+B)=Quantum.operatorMatrix A+Quantum.operatorMatrix B :=
  Quantum.operatorMatrix.map_add A B

private theorem gauge_charge_branches :
    chargeMatrix sourcePhaseGaugeLie=SourceRealScalarFock.branches (Quantum.operatorMatrix sourcePhaseGaugeCharge) := by
  rw [sourcePhaseGaugeCharge,gauge_matrix_smul,sourcePhaseGaugeGenerator_native]
  ext i j
  cases i <;> cases j <;>
    simp [chargeMatrix,GaussNativeMatter.nativeFull,SourceRealScalarFock.branches,Matrix.fromBlocks,
      Matrix.map_apply,Matrix.smul_apply,smul_eq_mul]

open Lean Elab Term in
elab "paidPhaseGaugeBoundedLift%" : term => do
  let wanted := `LowEnergy.GaussComposite.PhysicalPoleCharge.bounded_matrix_lift
  let names := (← getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.startsWith "_private.H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalPoleCharge." && privateToUserName name == wanted then some name else none
  match names with
  | [name] =>
    logInfo m!"Original private payer: {name}"
    return mkConst name
  | _ =>
    let related := (← getEnv).constants.toList.filterMap fun (name,_) =>
      if privateToUserName name == wanted then some name else none
    throwError "Expected unique original PhysicalPoleCharge.bounded_matrix_lift; actual candidates {related}"

private abbrev sourceGaugeBoundedMatrixLift := paidPhaseGaugeBoundedLift%

def sourcePhaseGaugeGaussDifference : H→L[ℂ]H :=
  lift (quantized (SourceRealScalarFock.branches
    (Quantum.operatorMatrix (Complex.I • sourcePhaseGaugeDifference))))

/-- Full504 CAR and the original Gauss carrier retain the computed full252 generator difference. -/
theorem sourcePhaseGaugeGauss_full :
    sourceActualGaussCharge=chargeReader sourcePhaseGaugeLie+sourcePhaseGaugeGaussDifference := by
  have matrix : sourceActualGaussChargeMatrix=chargeMatrix sourcePhaseGaugeLie+
      SourceRealScalarFock.branches (Quantum.operatorMatrix (Complex.I • sourcePhaseGaugeDifference)) := by
    rw [gauge_charge_branches,sourceActualGaussChargeMatrix,sourcePhaseNoether_canonical,
      sourcePhaseGaugeGenerator_full,smul_add,gauge_matrix_add]
    exact (branchesLinear.map_add _ _)
  rw [sourceActualGaussCharge,matrix,sourcePhaseGaugeGaussDifference,
    show chargeReader sourcePhaseGaugeLie=lift (quantized (chargeMatrix sourcePhaseGaugeLie)) from sourceGaugeBoundedMatrixLift _]
  change lift (quantizer (_+_))=lift (quantizer _)+lift (quantizer _)
  rw [map_add,lift_add]

/-- Both original full Green operators retain this literal source difference after the gauge restriction. -/
theorem sourcePhaseGaugeGreen_full (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) :
    sourceAbsoluteNoetherVertex q pL pR=
      (Stage10.ActionNormalization.phaseMomentum:ℂ) •
        (jointResolvent pL q.F q.z 0*chargeReader sourcePhaseGaugeLie*jointResolvent pR q.F q.w 0)+
      (Stage10.ActionNormalization.phaseMomentum:ℂ) •
        (jointResolvent pL q.F q.z 0*sourcePhaseGaugeGaussDifference*jointResolvent pR q.F q.w 0) := by
  rw [sourceAbsoluteNoetherVertex,sourceAbsoluteCharge,sourcePhaseGaugeGauss_full]
  simp only [smul_add,mul_add,add_mul,mul_smul_comm,smul_mul_assoc]

private theorem gauge_charge_coordinates (side edge : Fin 2) :
    chargeMatrix sourcePhaseGaugeLie*ᵥsourceChargedCoordinates side edge=
      (sourceActualPhaseCharge edge:ℂ) • sourceChargedCoordinates side edge := by
  have primal:=congrArg Quantum.coordinates (sourcePhaseGaugeCharge_actualColumn side edge)
  rw [←Quantum.matrix_action,map_smul] at primal
  have matrix : Quantum.operatorMatrix sourcePhaseGaugeCharge=
      Complex.I • GaussNativeMatter.nativePrimal sourcePhaseGaugeLie := by
    rw [sourcePhaseGaugeCharge,gauge_matrix_smul,sourcePhaseGaugeGenerator_native]
  rw [matrix,Matrix.smul_mulVec] at primal
  change (Complex.I • Matrix.fromBlocks (GaussNativeMatter.nativePrimal sourcePhaseGaugeLie)
      (0:SourceMatrix) (0:SourceMatrix) ((GaussNativeMatter.nativePrimal sourcePhaseGaugeLie).map (starRingEnd ℂ)))*ᵥ
      Sum.elim (Quantum.coordinates (sourceChargedRestriction side edge)) (fun _ : Quantum.Index=>(0:ℂ))=
    (sourceActualPhaseCharge edge:ℂ) •
      Sum.elim (Quantum.coordinates (sourceChargedRestriction side edge)) (fun _ : Quantum.Index=>(0:ℂ))
  rw [Matrix.smul_mulVec,Matrix.fromBlocks_mulVec]
  have first : (Sum.elim (Quantum.coordinates (sourceChargedRestriction side edge))
      (fun _ : Quantum.Index=>(0:ℂ))) ∘ Sum.inl=Quantum.coordinates (sourceChargedRestriction side edge) := rfl
  have second : (Sum.elim (Quantum.coordinates (sourceChargedRestriction side edge))
      (fun _ : Quantum.Index=>(0:ℂ))) ∘ Sum.inr=0 := rfl
  rw [first,second,Matrix.zero_mulVec,Matrix.zero_mulVec,Matrix.mulVec_zero,add_zero,zero_add]
  funext index
  cases index with
  | inl index=>exact congrFun primal index
  | inr index=>simp

private theorem gauge_charge_fiber (side edge : Fin 2) :
    quantized (chargeMatrix sourcePhaseGaugeLie) (sourceChargedFiber side edge)=
      (sourceActualPhaseCharge edge:ℂ) • sourceChargedFiber side edge := by
  rw [sourceChargedFiber,quantized_oneParticle,gauge_charge_coordinates]
  change fiberCoordinates.symm (Fermion.oneParticleLinear
    ((sourceActualPhaseCharge edge:ℂ) • sourceChargedCoordinates side edge))=_
  rw [map_smul,map_smul]
  rfl

/-- Original full CAR and half-density transport put the generated gauge charge on both actual Gauss preparations. -/
theorem sourcePhaseGaugeGauss_prepared (epsilon : ℝ) (precision : 0<epsilon) (side edge : Fin 2) :
    chargeReader sourcePhaseGaugeLie (sourceChargedGaussPrepared epsilon precision side edge)=
      (sourceActualPhaseCharge edge:ℂ) • sourceChargedGaussPrepared epsilon precision side edge := by
  rw [show chargeReader sourcePhaseGaugeLie=lift (quantized (chargeMatrix sourcePhaseGaugeLie)) from sourceGaugeBoundedMatrixLift _]
  apply GaussHalfDensity.fockHalfDensityEquiv.injective
  rw [map_smul]
  apply PiLp.ext
  intro word
  rw [sourceChargedGauss_action_coordinates,gauge_charge_fiber]
  simp only [PiLp.smul_apply,sourceChargedGaussPrepared_coordinates,smul_smul,smul_eq_mul]

theorem sourcePhaseGaugeGaussDifference_prepared (epsilon : ℝ) (precision : 0<epsilon) (side edge : Fin 2) :
    sourcePhaseGaugeGaussDifference (sourceChargedGaussPrepared epsilon precision side edge)=0 := by
  have generated:=congrArg (fun A : H→L[ℂ]H=>A (sourceChargedGaussPrepared epsilon precision side edge)) sourcePhaseGaugeGauss_full
  simp only [add_apply,sourceActualGaussCharge_prepared,sourcePhaseGaugeGauss_prepared] at generated
  exact add_eq_left.mp generated.symm

private theorem gaugeFiber_source (values : Source.Index→ℂ) :
    operator sourcePhaseGaugeCharge (naturalCoordinates (embed values))=
      Electromagnetic.CanonicalPacket.densityReader sourcePhaseNoether (naturalCoordinates (embed values)) := by
  change operator sourcePhaseGaugeCharge (naturalCoordinates (embed values))=
    operator (phaseInverse.comp sourcePhaseNoether) (naturalCoordinates (embed values))
  rw [operator_coordinates,operator_coordinates,sourcePhaseNoether_canonical]
  simp only [sourcePhaseGaugeCharge,LinearMap.smul_apply,sourcePhaseGaugeGenerator_embed]

/-- The original complete eight-pole expansion pays the equality on the actual filtered packet. -/
theorem sourcePhaseGauge_filtered (side edge : Fin 2) :
    (operator sourcePhaseGaugeCharge).compLpL 2 volume (sourceChargedFilteredPacket side edge)=
      (Electromagnetic.CanonicalPacket.densityReader sourcePhaseNoether).compLpL 2 volume (sourceChargedFilteredPacket side edge) := by
  apply fourier.injective
  rw [FullQuantum.GaugeGreen.constant_fourier,FullQuantum.GaugeGreen.constant_fourier]
  apply Lp.ext
  filter_upwards [(operator sourcePhaseGaugeCharge).coeFn_compLpL (fourier (sourceChargedFilteredPacket side edge)),
    (Electromagnetic.CanonicalPacket.densityReader sourcePhaseNoether).coeFn_compLpL (fourier (sourceChargedFilteredPacket side edge)),
    sourceActualFilteredPacket_poles side edge] with k left right poles
  rw [left,right,poles]
  simp only [map_sum,map_smul,gaugeFiber_source]

def sourcePhaseGaugePhysicalCurrent : FullMatterL2→L[ℂ]FullMatterL2 :=
  (Stage10.ActionNormalization.phaseMomentum:ℂ) • (operator sourcePhaseGaugeCharge).compLpL 2 volume

/-- Filtered nonpurity is retained: this true gauge current reads the actual unit-sector share, not an assumed unit vector charge. -/
theorem sourcePhaseGaugePhysicalCurrent_return (sL eL sR eR : Fin 2) :
    sourceChargedQuantumRead sL eL sR eR sourcePhaseGaugePhysicalCurrent=
      (Stage10.ActionNormalization.phaseMomentum:ℂ)*inner ℂ (sourceChargedFilteredPacket sL eL)
        (sourcePhaseSpatial 0 (sourceChargedFilteredPacket sR eR)) := by
  rw [←sourceActualFiltered_current sL eL sR eR]
  simp only [sourceChargedQuantumRead_generated,sourcePhaseGaugePhysicalCurrent,sourcePhaseCurrentOperator,
    smul_apply,sourcePhaseGauge_filtered]

/-- The actual full289 gauge direction varies the same complete source response; both orderings and Hessian contact remain. -/
theorem sourcePhaseGaugeField_fourPoint (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (mu : Fin 4) (s : SourceHarmonicOccurrence) (i : Fin 4) (x : Position) (imaginary : Bool)
    (left : q.z.im≠0) (right : q.w.im≠0) :
    let g : Field289:=fun a=>if imaginary then (sourceHarmonicProfile s i x a).im else (sourceHarmonicProfile s i x a).re
    HasDerivAt (fun r : ℝ=>
      (sourceActualLegNormalization q sL eL sR eR*
        ((sourceActualChargedRestEnergy sL:ℂ)-q.z)*((sourceActualChargedRestEnergy sR:ℂ)-q.w))*
      sourceQuantumChargedRead q sL eL sR eR
        (jointVertex g 0 0 q.F q.z q.w (r • sourcePhaseGaugeField mu)))
      ((sourceUnitFourPointPair q sL eL sR eR (sourcePhaseGaugeField mu) g).1+
        (sourceUnitFourPointPair q sL eL sR eR (sourcePhaseGaugeField mu) g).2) 0 := by
  dsimp only
  exact sourceUnitFourPoint_generated q sL eL sR eR (sourcePhaseGaugeField mu) _ left right

/-- The candidate gauge insertion consumes the full actual-profile charge response, including all Green/Y/current/contact torque. -/
theorem sourcePhaseGaugeField_chargeWard (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (mu : Fin 4) (s : SourceHarmonicOccurrence) (i : Fin 4) (x : Position) (imaginary : Bool)
    (p k : PhysicalMomentum) (left : q.z.im≠0) (right : q.w.im≠0) :
    let g : Field289:=fun a=>if imaginary then (sourceHarmonicProfile s i x a).im else (sourceHarmonicProfile s i x a).re
    sourceQuantumChargedRead q sL eL sR eR
      (sourceFieldMixedChargeResponse q p k (sourcePhaseGaugeField mu) g)=
      (Stage10.ActionNormalization.phaseMomentum:ℂ)*
        ((sourceActualPhaseCharge eL:ℂ)-(sourceActualPhaseCharge eR:ℂ))*
          sourceQuantumChargedRead q sL eL sR eR
            (mixedVertex (sourcePhaseGaugeField mu) g p k q.F q.z q.w) := by
  dsimp only
  exact sourceFieldMixedCharge_prepared q p k sL eL sR eR _ _ left right

/-- The source is the same complete actual-four-column current, propagated by the original physical-frequency residue. -/
def sourcePhaseGaugePhotonField (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (pL pR : PhysicalMomentum) (lambda : ℂ) (T epsilon sigma : ℝ) (n : PhysicalMomentum) : Fin 289→ℂ :=
  sourceWholePhotonFrequencyResidue epsilon sigma n*ᵥ
    sourceActualPreparedCurrent q pL pR sL eL sR eR lambda T

/-- The independent beta reader and the actual full polarization remain distinct from the candidate gauge direction. -/
theorem sourcePhaseGaugePhotonField_factor (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (pL pR : PhysicalMomentum) (lambda : ℂ) (T : ℝ) (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,
      sourcePhaseGaugePhotonField q sL eL sR eR pL pR lambda T e.val (sourceSheet branch n unit e.val) n=
        sourcePhotonLeftReader branch e.val (sourceSheet branch n unit e.val) n
          (sourceActualPreparedCurrent q pL pR sL eL sR eR lambda T) •
            sourceNativeFrequencyPolarization branch e.val (sourceSheet branch n unit e.val) n := by
  filter_upwards [sourceWholePhotonResidue_factor branch n unit] with e factor
  unfold sourcePhaseGaugePhotonField sourceWholePhotonFrequencyResidue sourceNativeFrequencyPolarization
  rw [Matrix.smul_mulVec,factor]
  exact smul_comm _ _ _

/-- Original full289 Jacobi constraints are paid on the same current-generated pole field. -/
theorem sourcePhaseGaugePhotonField_equation (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (pL pR : PhysicalMomentum) (lambda : ℂ) (T : ℝ) (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,
      originalJacobi (frequencyRay e.val (sourceSheet branch n unit e.val) n)*ᵥ
        sourcePhaseGaugePhotonField q sL eL sR eR pL pR lambda T e.val (sourceSheet branch n unit e.val) n=0 := by
  filter_upwards [sourceWholePhotonResidue_homogeneous branch n unit] with e equations
  unfold sourcePhaseGaugePhotonField sourceWholePhotonFrequencyResidue
  rw [Matrix.smul_mulVec,Matrix.mulVec_smul,Matrix.mulVec_mulVec,equations.2,Matrix.zero_mulVec,smul_zero]

/-- The same generated photon field enters the true gauge-current variation with the original two ordered terms and direct contact. -/
theorem sourcePhaseGaugePhoton_fourPoint (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (sourceQ : PhysicalResponsePoint) (aL bL aR bR : Fin 2) (pL pR : PhysicalMomentum)
    (lambda : ℂ) (T epsilon sigma : ℝ) (n : PhysicalMomentum) (mu : Fin 4) (imaginary : Bool)
    (left : q.z.im≠0) (right : q.w.im≠0) :
    let V:=sourcePhaseGaugePhotonField sourceQ aL bL aR bR pL pR lambda T epsilon sigma n
    let g : Field289:=fun a=>if imaginary then (V a).im else (V a).re
    HasDerivAt (fun r : ℝ=>
      (sourceActualLegNormalization q sL eL sR eR*
        ((sourceActualChargedRestEnergy sL:ℂ)-q.z)*((sourceActualChargedRestEnergy sR:ℂ)-q.w))*
      sourceQuantumChargedRead q sL eL sR eR
        (jointVertex g 0 0 q.F q.z q.w (r • sourcePhaseGaugeField mu)))
      ((sourceUnitFourPointPair q sL eL sR eR (sourcePhaseGaugeField mu) g).1+
        (sourceUnitFourPointPair q sL eL sR eR (sourcePhaseGaugeField mu) g).2) 0 := by
  dsimp only
  exact sourceUnitFourPoint_generated q sL eL sR eR (sourcePhaseGaugeField mu) _ left right

end LowEnergy.PreparationPhysicalPhaseGaugeRealization
