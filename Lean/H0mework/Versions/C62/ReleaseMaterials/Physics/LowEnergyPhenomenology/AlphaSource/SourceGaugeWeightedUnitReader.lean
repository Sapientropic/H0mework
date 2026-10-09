import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceGaugeFixedMomentum

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
local instance actualGaugeUnitReaderIndex : DecidableEq Quantum.Index:=Classical.decEq _
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

/-- The full independent-dual momentum weight is generated from the same source W, with its exact branch signs. -/
def sourceGaugeFullMomentumWeight (base : ActionState) : FullMatrix :=
  oppositeDual*Matrix.fromBlocks (sourceGaugeMomentumWeight base) 0 0
    ((sourceGaugeMomentumWeight base).map star)

private theorem charge_branches :
    chargeMatrix sourcePhaseGaugeLie=SourceRealScalarFock.branches (Quantum.operatorMatrix sourcePhaseGaugeCharge) := by
  have matrix : Quantum.operatorMatrix sourcePhaseGaugeCharge=
      Complex.I • GaussNativeMatter.nativePrimal sourcePhaseGaugeLie := by
    have smul : Quantum.operatorMatrix (Complex.I • sourcePhaseGaugeGenerator)=
        Complex.I • Quantum.operatorMatrix sourcePhaseGaugeGenerator :=
      Quantum.operatorMatrix.toLinearEquiv.map_smul _ _
    rw [sourcePhaseGaugeCharge,smul,sourcePhaseGaugeGenerator_native]
  rw [matrix]
  ext i j
  cases i <;> cases j <;>
    simp [chargeMatrix,GaussNativeMatter.nativeFull,SourceRealScalarFock.branches,Matrix.fromBlocks,
      Matrix.map_apply,Matrix.smul_apply,smul_eq_mul]

private theorem branch_product (W Q : SourceMatrix) :
    Matrix.fromBlocks W (0:SourceMatrix) (0:SourceMatrix) (W.map star)*SourceRealScalarFock.branches Q=
      SourceRealScalarFock.branches (W*Q) := by
  rw [SourceRealScalarFock.branches,Matrix.fromBlocks_multiply]
  ext i j
  cases i <;> cases j <;>
    simp [SourceRealScalarFock.branches,Matrix.fromBlocks,Matrix.map_apply,Matrix.mul_apply,
      mul_neg]

theorem sourceGaugeUnitSymbol_factor (base : ActionState) (p : PhysicalMomentum) :
    sourceGaugeUnitSymbol base p=sourceGaugeFullMomentumWeight base*chargeMatrix sourcePhaseGaugeLie := by
  simp only [sourceGaugeUnitSymbol,rawFourier]
  change oppositeDual*realFourierMatrix
    (fun row=>if row=0 then sourceGaugeUnitCoefficient base else 0) p=_
  have symbol : realFourierMatrix (fun row=>if row=0 then sourceGaugeUnitCoefficient base else 0) p=
      SourceRealScalarFock.branches (sourceGaugeUnitCoefficient base) := by
    simp [realFourierMatrix,affineMatrix,SourceRealScalarFock.branches]
  rw [symbol,sourceGaugeFullMomentumWeight,charge_branches,mul_assoc,branch_product]
  rfl

/-- Original full CAR returns the momentum-weighted charge and its exact quartic correction. -/
theorem sourceGaugeUnitQuantized_fullCAR (base : ActionState) (p : PhysicalMomentum) :
    quantized (sourceGaugeUnitSymbol base p)=
      quantized (sourceGaugeFullMomentumWeight base)*quantized (chargeMatrix sourcePhaseGaugeLie)-
        pairFiber (sourceGaugeFullMomentumWeight base) (chargeMatrix sourcePhaseGaugeLie) := by
  rw [sourceGaugeUnitSymbol_factor,quantized_normal_order]
  abel

def sourceGaugeUnitForm (p : PhysicalMomentum) (a b : QuantumTest) : ℂ :=
  ∫z,pairSample z (a z) (quantizer (sourceGaugeUnitSymbol (sourceState z) p) (b z))
    ∂GaussHistoryHilbert.configurationMeasure

def sourceGaugeUnitReader (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : H→L[ℂ]H :=
  finiteRiesz F (fun i j=>sourceGaugeUnitForm p (frameTest F i) (frameTest F j))

/-- This is the complete finite reader, not the bare uncompressed chargeReader. -/
theorem sourceGaugeUnitForm_fullCAR (p : PhysicalMomentum) (a b : QuantumTest) :
    sourceGaugeUnitForm p a b=
      ∫z,pairSample z (a z)
        ((quantized (sourceGaugeFullMomentumWeight (sourceState z))*quantized (chargeMatrix sourcePhaseGaugeLie)-
          pairFiber (sourceGaugeFullMomentumWeight (sourceState z)) (chargeMatrix sourcePhaseGaugeLie)) (b z))
        ∂GaussHistoryHilbert.configurationMeasure := by
  unfold sourceGaugeUnitForm
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  change pairSample z (a z) (quantized (sourceGaugeUnitSymbol (sourceState z) p) (b z))=_
  rw [sourceGaugeUnitQuantized_fullCAR]

theorem sourceGaugeNoetherForm_momentum (p : PhysicalMomentum) (a b : QuantumTest) :
    noetherForm (sourcePhaseGaugeField 0) p a b 0=
      (ActionNormalization.phaseMomentum:ℂ)*sourceGaugeUnitForm p a b := by
  rw [noetherForm,sourceGaugeUnitForm,←integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  by_cases inside : z∈tsupport a
  · have valid:=PreparationVacuumNonlinearFieldCurve.sourceState_valid (⟨z,a.tsupport_subset inside⟩:physicalChart)
    change pairSample z (a z) (quantizer (transportedRawSymbol (sourcePhaseGaugeField 0) (sourceState z) (ambientState (0,z)) p) (b z))=_
    rw [ambientState_zero,sourceGaugeTransportedSymbol _ _ valid,quantizer.map_smul_of_tower]
    simp only [RCLike.real_smul_eq_coe_smul (K:=ℂ),smul_apply,pairSample_smul_right]
    rfl
  · simp only [noetherSample_zero _ _ _ _ _ _ inside,image_eq_zero_of_notMem_tsupport inside,
      pairSample_zero_left,mul_zero]

theorem sourceGaugeNoetherReader_momentum (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    noetherReader (sourcePhaseGaugeField 0) p F 0=ActionNormalization.phaseMomentum • sourceGaugeUnitReader p F := by
  simp only [noetherReader,sourceGaugeUnitReader,sourceGaugeNoetherForm_momentum,finiteRiesz,
    Finset.smul_sum,RCLike.real_smul_eq_coe_smul (K:=ℂ),smul_smul]
  rfl

theorem sourceGaugeNoetherContactForm_zero (force : Field289) (p : PhysicalMomentum) (a b : QuantumTest) :
    noetherContactForm (sourcePhaseGaugeField 0) force p a b=0 := by
  rw [noetherContactForm]
  have zero : (fun z=>pairSample z (a z)
      (quantizer (noetherContactSymbol (sourcePhaseGaugeField 0) force (sourceState z) p) (b z)))=0 := by
    funext z
    by_cases inside : z∈tsupport a
    · rw [sourceGaugeNoetherContactSymbol force (⟨z,a.tsupport_subset inside⟩:physicalChart),map_zero,zero_apply]
      simp [pairSample]
    · simp only [image_eq_zero_of_notMem_tsupport inside,pairSample_zero_left,Pi.zero_apply]
  rw [zero]
  exact integral_zero _ _

theorem sourceGaugeNoetherReaderContact_zero (force : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    noetherReaderContact (sourcePhaseGaugeField 0) force p F=0 := by
  rw [noetherReaderContact_source]
  simp only [sourceGaugeNoetherContactForm_zero,finiteRiesz,zero_smul,Finset.sum_const_zero]

/-- Both actual Green legs and both physical times carry the original weighted current. -/
def sourceGaugeUnitKernel (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (time : ℝ) : H→L[ℂ]H :=
  physicalTime pL q.F (-time) 0*jointResolvent pL q.F q.z 0*sourceGaugeUnitReader pR q.F*
    jointResolvent pR q.F q.w 0*physicalTime pR q.F time 0

private theorem scalar_word {R : Type*} [Ring R] [Algebra ℝ R] (L G A K U : R) (c : ℝ) :
    L*G*(c • A)*K*U=c • (L*G*A*K*U) := by
  simp only [smul_mul_assoc,mul_smul_comm]

theorem sourceGaugeFiveKernel_momentum (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (time : ℝ) :
    fiveKernel (sourcePhaseGaugeField 0) pR (pL-pR) q.F q.z q.w time 0=
      ActionNormalization.phaseMomentum • sourceGaugeUnitKernel q pL pR time := by
  have momentum : pR+(pL-pR)=pL := by ext i;simp
  unfold fiveKernel sourceGaugeUnitKernel
  rw [momentum,←noetherReader_source,sourceGaugeNoetherReader_momentum]
  exact scalar_word _ _ _ _ _ _

/-- The actual four-column read retains its normalization/whole-C and both independent Green-time legs. -/
theorem sourceGaugeActualPrepared_momentum (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (pL pR : PhysicalMomentum) (time : ℝ) :
    sourceUnitRead q sL eL sR eR (fiveKernel (sourcePhaseGaugeField 0) pR (pL-pR) q.F q.z q.w time 0)=
      (ActionNormalization.phaseMomentum:ℂ)*sourceUnitRead q sL eL sR eR (sourceGaugeUnitKernel q pL pR time) := by
  rw [sourceGaugeFiveKernel_momentum]
  change sourceUnitRead q sL eL sR eR ((ActionNormalization.phaseMomentum:ℂ) • sourceGaugeUnitKernel q pL pR time)=_
  rw [map_smul,smul_eq_mul]

end LowEnergy.PreparationPhysicalGaugeMomentumCoupling
