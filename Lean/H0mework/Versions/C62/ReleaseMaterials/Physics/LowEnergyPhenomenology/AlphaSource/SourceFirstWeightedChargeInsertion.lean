import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceFirstMaterialVertexReturn
import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourcePolarizationConfiguration

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalFirstChargeFourPointReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationPhysicalFirstPoleGaugeVertex PreparationPhysicalNormalizedFullField
open PreparationVacuumNativeFieldInjection PreparationVacuumSourceFieldFamily PreparationVacuumNonlinearFieldCurve
open PreparationVacuumMixedFieldReturn PreparationVacuumActionFieldLift PreparationVacuumGaugeSourceInjection
open PreparationVacuumActualFieldQuantization PreparationVacuumOriginalGreenFeedback
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open GaussNativeMatter GaussHistoryHilbert GaussQuantumMultiplier
open StageNineHolonomicField StageNineDynamicBreakingVacuum DiracExteriorMatterAction DiracCliffordRepresentation
open Stage9C.Material.SpinPair FullQuantum.CoframeResponse FullQuantum.StateGreen
open PointwiseLorentzianCoframeJet PointwiseDiracSpinConnectionLift
open Filter Set
open scoped BigOperators Matrix Topology ContDiff Matrix.Norms.L2Operator
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
local instance : NormedAlgebra ℝ SourceMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ FullMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : FiniteDimensional ℂ SourceMatrix:=Matrix.finiteDimensional
local instance : FiniteDimensional ℂ FullMatrix:=Matrix.finiteDimensional
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace

open PreparationPhysicalFirstGaugeBackgroundReturn PreparationPhysicalSourceHarmonicReturn
open PreparationVacuumPhysicalCharacteristic ProofFreeRicherAnholonomicSource
open CanonicalGradedSpatialSource FullQuantum FullSpace PreparationVacuumLowerClassical

open PreparationPhysicalActualNoetherVertexReturn PreparationPhysicalActualPhaseChargeReturn
open PreparationPhysicalNativePoleChargeReturn PreparationPhysicalNativePhotonFluxReturn PreparationPhysicalNativePolarizationEmitter
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumNativeSlowCoupling PreparationVacuumPhysicalFeedback
open PreparationPhysicalResponseChargeGrading PreparationVacuumLorentzFieldInjection
open PreparationVacuumPhysicalChargedFieldFactor PreparationPhysicalPoleChargeMatrix
open GaussFockLift GaussCoreHilbert PreparationVacuumPhysicalQuantumLockedCharge
open PreparationPhysicalChargedEnergyPoleReturn PreparationPhysicalNativePhaseChargeInventory
open scoped InnerProductSpace

open PreparationPhysicalFirstPoleGaugeRemainder PreparationPhysicalMaterialChargeTorque
open PreparationPhysicalActualGaussChargeCurrent PreparationPhysicalPhaseGaugeRealization
open PreparationPhysicalCoframeChargeSelection PreparationPhysicalCoframeChargeExchange
open SourceQuantumGaugeSliceCoordinates SourceQuantumResidualGaugeSlice CanonicalGradedCharge GaussCoreDifferential GaussQuantumMultiplier
open GaussFockPair GaussLiveMomentum GaussNativePotential
open scoped ContDiff

open NativeHistoryGrade GaussUnitaryHistory CanonicalPhysicalSpatial CanonicalPhysicalWardCore
open PreparationVacuumGradedTransport PreparationVacuumUncutYukawa PreparationPhysicalActualLegNormalization
open PreparationVacuumPhysicalHalfAxis PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse
open PreparationVacuumPhysicalPoleAmputation PreparationPhysicalChargedScatteringPoleReturn
open GaussFockWeights GaussDensityCore MeasureTheory PreparationVacuumFieldConstraintResponse PreparationVacuumYukawaTransport
local instance : Fintype NativeHistoryGrade.Label:=Fintype.ofFinite _
local instance : NormedAlgebra ℝ (H→L[ℂ]H):=NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] jointGenerator jointResolvent actualC gradedTest

open PreparationPhysicalFirstGaugeMaterialDifference PreparationPhysicalActualUnitFourPointReturn
open PreparationPhysicalActualPolarizationResponse PreparationVacuumFullFieldRiesz PreparationVacuumSourceActionJets

/-- The actual source action weight stays in the charge insertion. -/
def sourceFirstWeightCharge (s : ActionState) : FullMatrix :=
  sourceActionWeight s*sourceFirstChargeMatrix-sourceFirstChargeMatrix*sourceActionWeight s

private theorem weight_native (s : ActionState) : Commute (nativeFull sourceFirstTemporalLie) (sourceActionWeight s) := by
  have flip : Commute (nativePrimal sourceFirstTemporalLie) (Quantum.operatorMatrix YangMills.FullPairing.flipMatter) := by
    have same : YangMills.FullPairing.flipMatter=DiracExteriorMatterAction.diracMatrixMatterAction
        StageNineFullDiracAdjointMaterial.diracAdjointSpinSwap :=
      LinearMap.ext YangMills.FullPairing.flipMatter_source
    rw [same,GaussCoframeSpin.spinLift_source]
    exact (GaussMatterCore.spin_native_commute _ sourceFirstTemporalLie).symm
  have principal : Commute (nativePrimal sourceFirstTemporalLie) (principalMatrix s.1) := by
    rw [principalMatrix_coefficient]
    change _*(Complex.I • spinCoordinates (inverseCoframeDiracGamma {coframe:=s.1,derivative:=0} 0))=
      (Complex.I • spinCoordinates (inverseCoframeDiracGamma {coframe:=s.1,derivative:=0} 0))*_
    rw [mul_smul_comm,smul_mul_assoc,originalSpin_internal_commute]
  have phase : Commute (nativePrimal sourceFirstTemporalLie) (inversePhase s) :=
    principal.smul_right _
  let M : SourceMatrix:=(Stage9C.Material.SpinPair.spinScale:ℂ) •
    (Quantum.operatorMatrix YangMills.FullPairing.flipMatter*inversePhase s)
  have h : nativePrimal sourceFirstTemporalLie*M=M*nativePrimal sourceFirstTemporalLie :=
    ((flip.mul_right phase).smul_right (Stage9C.Material.SpinPair.spinScale:ℂ)).eq
  have dual:=congrArg (fun A : SourceMatrix=>A.map (starRingEnd ℂ)) h
  rw [Matrix.map_mul,Matrix.map_mul] at dual
  change Matrix.fromBlocks (nativePrimal sourceFirstTemporalLie) 0 0 ((nativePrimal sourceFirstTemporalLie).map (starRingEnd ℂ))*
      Matrix.fromBlocks M 0 0 (-(M.map (starRingEnd ℂ)))=
    Matrix.fromBlocks M 0 0 (-(M.map (starRingEnd ℂ)))*
      Matrix.fromBlocks (nativePrimal sourceFirstTemporalLie) 0 0 ((nativePrimal sourceFirstTemporalLie).map (starRingEnd ℂ))
  rw [Matrix.fromBlocks_multiply,Matrix.fromBlocks_multiply]
  simp only [Matrix.zero_mul,Matrix.mul_zero,add_zero,zero_add,Matrix.mul_neg,Matrix.neg_mul,neg_zero,h,dual]

/-- The actual adjoint spin swap and source principal matrix generate this weight cancellation for GT on both independent branches. -/
theorem sourceFirstWeightCharge_zero (s : ActionState) : sourceFirstWeightCharge s=0 := by
  change sourceActionWeight s*((-Complex.I) • nativeFull sourceFirstTemporalLie)-
    ((-Complex.I) • nativeFull sourceFirstTemporalLie)*sourceActionWeight s=0
  rw [mul_smul_comm (-Complex.I) (sourceActionWeight s) (nativeFull sourceFirstTemporalLie),
    smul_mul_assoc (-Complex.I) (nativeFull sourceFirstTemporalLie) (sourceActionWeight s),
    (weight_native s).eq,sub_self]

/-- Full background Hessian plus its field-dependent contact, with the original weight correction. -/
def sourceFirstWeightedInsertion (p : PhysicalMomentum) (s : ActionState) (f : Field289) : FullMatrix :=
  -(4:ℂ) • (Complex.I • (sourceActionWeight s*sourceFirstBackgroundMixed p s f)+
    sourceFirstWeightCharge s*symbolFirst p s (fieldDirection f))

private theorem symbol_charge (p : PhysicalMomentum) (s : ActionState) (valid : s∈validStates) (f : Field289) :
    symbolFirst p s (fieldDirection f)*sourceFirstChargeMatrix-
      sourceFirstChargeMatrix*symbolFirst p s (fieldDirection f)=Complex.I • sourceFirstBackgroundMixed p s f := by
  rw [sourceFirstBackgroundMixed_return p s valid f]
  change symbolFirst p s (fieldDirection f)*((-Complex.I) • sourceFirstBackgroundFullGenerator)-
    ((-Complex.I) • sourceFirstBackgroundFullGenerator)*symbolFirst p s (fieldDirection f)=
    Complex.I • (sourceFirstBackgroundFullGenerator*symbolFirst p s (fieldDirection f)-
      symbolFirst p s (fieldDirection f)*sourceFirstBackgroundFullGenerator)
  rw [mul_smul_comm (-Complex.I) (symbolFirst p s (fieldDirection f)) sourceFirstBackgroundFullGenerator,
    smul_mul_assoc (-Complex.I) sourceFirstBackgroundFullGenerator (symbolFirst p s (fieldDirection f))]
  ext a b
  simp only [Matrix.smul_apply,Matrix.sub_apply,smul_eq_mul]
  ring

private theorem weighted_comm {R : Type*} [Ring R] (W S Q : R) :
    W*S*Q-Q*(W*S)=W*(S*Q-Q*S)+(W*Q-Q*W)*S := by noncomm_ring

/-- No source field is projected away: the weighted raw current consumes the full GT covariance and its true mixed contact. -/
theorem sourceFirstWeightedInsertion_generated (p : PhysicalMomentum) (s : ActionState)
    (valid : s∈validStates) (f : Field289) :
    rawActionSymbol f p s*sourceFirstChargeMatrix-sourceFirstChargeMatrix*rawActionSymbol f p s=
      sourceFirstWeightedInsertion p s f := by
  rw [rawActionSymbol_source f p s valid]
  simp only [smul_mul_assoc,mul_smul_comm,←smul_sub]
  rw [weighted_comm,symbol_charge p s valid f,mul_smul_comm]
  rfl

theorem sourceFirstWeightedInsertion_reduced (p : PhysicalMomentum) (s : ActionState) (f : Field289) :
    sourceFirstWeightedInsertion p s f= -(4:ℂ) • (Complex.I •
      (sourceActionWeight s*sourceFirstBackgroundMixed p s f)) := by
  rw [sourceFirstWeightedInsertion,sourceFirstWeightCharge_zero,zero_mul,add_zero]

/-- The literal full first gauge column is inserted in the same evaluated weighted current. -/
theorem sourceFirstAxisInsertion_generated (p : PhysicalMomentum) (s : ActionState)
    (valid : s∈validStates) (k : Fin 4) :
    (-(4:ℂ) • (sourceActionWeight s*SourceRealScalarFock.branches (sourcePolarizationAxisEnergy s k)))*sourceFirstChargeMatrix-
      sourceFirstChargeMatrix*(-(4:ℂ) • (sourceActionWeight s*SourceRealScalarFock.branches (sourcePolarizationAxisEnergy s k)))=
      sourceFirstWeightedInsertion p s (sourceEnergyAxisField 1 k) := by
  rw [←sourcePolarizationAxis_raw s valid p k]
  exact sourceFirstWeightedInsertion_generated p s valid _

/-- The same real quadrature occurrence retains both the primitive mixed contact and its compensating remainder contact. -/
theorem sourceFirstQuadratureInsertion_generated (imaginary : Bool) (omega : ℝ) (k : PhysicalMomentum)
    (x : BasePoint) (p : PhysicalMomentum) (s : ActionState) (valid : s∈validStates) :
    rawActionSymbol (sourceFirstModeField imaginary omega k x) p s*sourceFirstChargeMatrix-
      sourceFirstChargeMatrix*rawActionSymbol (sourceFirstModeField imaginary omega k x) p s=
      sourceFirstWeightedInsertion p s (sourceFirstModeField imaginary omega k x) :=
  sourceFirstWeightedInsertion_generated p s valid _

private abbrev End := QuantumTest→ₗ[ℂ]QuantumTest
local instance : Semiring End:=Module.End.instSemiring (R:=ℂ) (M:=QuantumTest)

def sourceFirstRawCore (f : Field289) (p : PhysicalMomentum) : End :=
  localMultiplier (rawMode false f 0 p) (rawMode_smooth false f 0 p)

private theorem raw_core_apply (f : Field289) (p : PhysicalMomentum) (a : QuantumTest) (z : SourceCoordinateSlice) :
    sourceFirstRawCore f p a z=rawStateFiber f p (sourceState z) (a z) := rfl

private theorem charge_core_apply (a : QuantumTest) (z : SourceCoordinateSlice) :
    sourceFirstChargeCore a z=quantized sourceFirstChargeMatrix (a z) := rfl

def sourceFirstRawChargeCore (f : Field289) (p : PhysicalMomentum) : End :=
  (sourceFirstRawCore f p).comp sourceFirstChargeCore-sourceFirstChargeCore.comp (sourceFirstRawCore f p)

theorem sourceFirstRawChargeCore_generated (f : Field289) (p : PhysicalMomentum) (a : QuantumTest) (z : physicalChart) :
    sourceFirstRawChargeCore f p a z.val=
      quantizer (sourceFirstWeightedInsertion p (sourceState z.val) f) (a z.val) := by
  have generated:=congrArg quantizer (sourceFirstWeightedInsertion_generated p (sourceState z.val)
    (PreparationVacuumNonlinearFieldCurve.sourceState_valid z) f)
  rw [paidCoframeQuantizerComm%] at generated
  change sourceFirstRawCore f p (sourceFirstChargeCore a) z.val-
    sourceFirstChargeCore (sourceFirstRawCore f p a) z.val=_
  rw [raw_core_apply,charge_core_apply,charge_core_apply,raw_core_apply]
  rw [←rawActionSymbol_actual]
  exact congrArg (fun A : FockFiber→L[ℂ]FockFiber=>A (a z.val)) generated

private theorem raw_form_core (f : Field289) (p : PhysicalMomentum) (a b : QuantumTest) :
    rawForm f p a b 0=sourcePair a (sourceFirstRawCore f p b) := by
  rw [rawForm_original,sourcePair_integral]
  apply integral_congr_ae
  exact Eventually.of_forall fun z=>by
    rw [←pairSample_source,raw_core_apply]

private theorem first_core_pair (a b : QuantumTest) :
    sourcePair a (sourceFirstChargeCore b)=sourcePair (sourceFirstChargeCore a) b := by
  change inner ℂ (embed a) (embed (sourceFirstChargeCore b))=inner ℂ (embed (sourceFirstChargeCore a)) (embed b)
  rw [←sourceFirstChargeCore_embed,←sourceFirstChargeCore_embed,sourceFirstCharge_pair]

def sourceFirstRawChargeIntegral (f : Field289) (p : PhysicalMomentum) (a b : QuantumTest) : ℂ :=
  ∫z,pairSample z (a z) (quantizer (-(4:ℂ) • (Complex.I •
    (sourceActionWeight (sourceState z)*sourceFirstBackgroundMixed p (sourceState z) f))) (b z))
    ∂GaussHistoryHilbert.configurationMeasure

/-- Actual Gaussian preparations read the computed whole weighted insertion; charge is never moved through a finite frame by assumption. -/
theorem sourceFirstRawChargeIntegral_generated (f : Field289) (p : PhysicalMomentum) (a b : QuantumTest) :
    rawForm f p a (sourceFirstChargeCore b) 0-rawForm f p (sourceFirstChargeCore a) b 0=
      sourceFirstRawChargeIntegral f p a b := by
  rw [raw_form_core,raw_form_core,←first_core_pair]
  have same : sourcePair a (sourceFirstRawChargeCore f p b)=sourceFirstRawChargeIntegral f p a b := by
    rw [sourcePair_integral]
    apply integral_congr_ae
    filter_upwards with z
    rw [←pairSample_source]
    by_cases inside : z∈tsupport a
    · rw [sourceFirstRawChargeCore_generated f p b ⟨z,a.tsupport_subset inside⟩,sourceFirstWeightedInsertion_reduced]
    · simp only [image_eq_zero_of_notMem_tsupport inside,pairSample_zero_left]
  rw [←same]
  simp only [sourceFirstRawChargeCore,LinearMap.sub_apply,LinearMap.comp_apply,sourcePair,map_sub,inner_sub_right]

/-- The original raw density contact is zero for these two actual first-axis fields; this does not remove the material Hessian. -/
theorem sourceFirstAxisRawContact_charge (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (k l : Fin 4) :
    rawReaderContact (sourceEnergyAxisField 1 k) (sourceEnergyAxisField 1 l) p F*sourceFirstCharge-
      sourceFirstCharge*rawReaderContact (sourceEnergyAxisField 1 k) (sourceEnergyAxisField 1 l) p F=0 := by
  rw [sourcePolarizationAxis_readerContact]
  simp only [zero_mul,mul_zero,sub_self]

end LowEnergy.PreparationPhysicalFirstChargeFourPointReturn
