import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMOriginWardWeight
import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMMovingUnitUniform

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMOriginWard
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationPhysicalNormalizedFullField PreparationVacuumNativeFieldInjection
open PreparationVacuumNativeLocalWard PreparationVacuumSourceFieldFamily PreparationVacuumNonlinearFieldCurve
open PreparationVacuumLowerClassical PreparationVacuumMixedFieldReturn PreparationVacuumActionFieldLift
open PreparationVacuumOriginalGreenFeedback PreparationVacuumGaugeSourceInjection PreparationVacuumActualFieldQuantization
open SourceQuantumScalarChart SourceQuantumFockGauge SourceQuantumConfigurationHilbert GaussNativeMatter GaussHistoryHilbert GaussQuantumMultiplier
open StageNineHolonomicField StageNineDynamicBreakingVacuum StageNineEnrichedProofFreeSource ProofFreeRicherAnholonomicSource
open StageNineP286InfinitesimalGaugeTransformation StageNineCoframeGravityGaugeRegularity
open StageNineP286GaugeAuxiliaryVariation StageNineP286BracketCalculus
open StageNineP286GaugeConnectionVariation StageNineCompactSupportIntegrationByParts
open SU7MotherLieAlgebra SU7MotherGaugeTheory DiracExteriorMatterAction StageNineDiracDualYukawaSpinJurisdiction DiracCliffordRepresentation
open Stage9C.Material.SpinPair FullQuantum.CoframeResponse FullQuantum.StateGreen
open PointwiseLorentzianCoframeJet PointwiseDiracSpinConnectionLift
open PreparationPhysicalPhaseGaugeRealization PreparationPhysicalJointEMCouplingUnitReturn
open ActualEMCompleteOrbit PhysicalEMGaugeRealization PreparationPhysicalNativePoleChargeReturn
open PreparationVacuumPhysicalModeContact PreparationVacuumRestModeCoupling
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

open PreparationVacuumSourceActionJets PreparationVacuumHalfDensityFiber PreparationVacuumFullFieldRiesz
open PreparationVacuumFieldConstraintResponse PreparationVacuumGradedTransport PreparationVacuumRawJointFeedback
open SourceQuantumGaugeSliceCoordinates GaussCoreHilbert CanonicalGradedSpatialSource MeasureTheory
open PreparationVacuumFullElectricWard PreparationVacuumActionDecomposition CanonicalGradedCharge CanonicalPhysicalSpatial
open PreparationVacuumFullPoleContinuation PreparationVacuumPhysicalFeedback PreparationVacuumPhysicalCurrentLaplaceReturn
open GaussCoreDifferential CanonicalPhysicalWardCore
local instance : Fintype NativeHistoryGrade.Label := Fintype.ofFinite _
open ActualEMCarrierOwn
attribute [local irreducible] emOriginRawWard emOriginRawScalar emOriginRawDeviation sourceSymbol sourceActionWeight

def emOriginActionSample (A : ActionState→FullMatrix) (a b : QuantumTest) (z : SourceCoordinateSlice) : ℂ :=
  pairSample z (a z) (quantizer (A (sourceState z)) (b z))

def emOriginWardForm (p : PhysicalMomentum) (a b : QuantumTest) : ℂ :=
  ∫z,emOriginActionSample (emOriginRawWard p) a b z ∂GaussHistoryHilbert.configurationMeasure

def emOriginScalarForm (p : PhysicalMomentum) (a b : QuantumTest) : ℂ :=
  ∫z,emOriginActionSample (emOriginRawScalar p) a b z ∂GaussHistoryHilbert.configurationMeasure

def emOriginDeviationForm (p : PhysicalMomentum) (a b : QuantumTest) : ℂ :=
  ∫z,emOriginActionSample (emOriginRawDeviation p) a b z ∂GaussHistoryHilbert.configurationMeasure

attribute [local irreducible] sourceModeReader sourceModeForm rawForm emOriginWardForm emOriginScalarForm emOriginDeviationForm

private theorem actionSample_integrable (A : ActionState→FullMatrix)
    (smooth : ∀s : ActionState,s∈validStates → ContDiffAt ℝ ∞ A s) (a b : QuantumTest) :
    Integrable (emOriginActionSample A a b) GaussHistoryHilbert.configurationMeasure := by
  have fiberSmooth (z : physicalChart) : ContDiffAt ℝ ∞ (fun w=>quantizer (A (sourceState w))) z.val :=
    (quantizer.restrictScalars ℝ).toContinuousLinearMap.contDiff.contDiffAt.comp z.val
      ((smooth (sourceState z.val) (PreparationVacuumNonlinearFieldCurve.sourceState_valid z)).comp z.val sourceState_smooth.contDiffAt)
  have paid:=fixedFiber_integrable (fun z=>quantizer (A (sourceState z))) fiberSmooth 0 a b 0
    (by simpa only [abs_zero] using fieldRadius_positive 0 a)
  unfold emOriginActionSample
  simpa only [fixedSample,curve_zero] using paid

private theorem rawWard_smooth (p : PhysicalMomentum) (s : ActionState) (valid : s∈validStates) :
    ContDiffAt ℝ ∞ (emOriginRawWard p) s := by
  unfold emOriginRawWard
  have inner:=(emBackgroundFullAd.restrictScalars ℝ).toContinuousLinearMap.contDiff.contDiffAt.comp s
    (sourceSymbol_smooth p s valid)
  exact ((sourceActionWeight_smooth s valid).mul inner).const_smul (-(4:ℂ))

private theorem rawScalar_smooth (p : PhysicalMomentum) (s : ActionState) (valid : s∈validStates) :
    ContDiffAt ℝ ∞ (emOriginRawScalar p) s := by
  unfold emOriginRawScalar
  have inner:=((sourceSymbol_smooth p s valid).fderiv_right (m:=∞) (by simp)).clm_apply
    (contDiffAt_const (c:=emScalarCounterState))
  exact ((sourceActionWeight_smooth s valid).mul inner).const_smul (-(4:ℂ))

private theorem rawDeviation_smooth (p : PhysicalMomentum) (s : ActionState) (valid : s∈validStates) :
    ContDiffAt ℝ ∞ (emOriginRawDeviation p) s := by
  unfold emOriginRawDeviation
  have direction : ContDiff ℝ ∞ emOriginDeviationState :=
    emGaugeState.toContinuousLinearMap.contDiff.comp (contDiff_id.sub contDiff_const)
  have inner:=((sourceSymbol_smooth p s valid).fderiv_right (m:=∞) (by simp)).clm_apply direction.contDiffAt
  exact ((sourceActionWeight_smooth s valid).mul inner).const_smul (-(4:ℂ))

/-- Every EM, scalar and configuration-deviation form is separately integrable on the original source measure; the original profile is arbitrary within QuantumTest. -/
theorem em_origin_forms_integrable (p : PhysicalMomentum) (a b : QuantumTest) :
    Integrable (emOriginActionSample (emOriginRawWard p) a b) GaussHistoryHilbert.configurationMeasure ∧
    Integrable (emOriginActionSample (emOriginRawScalar p) a b) GaussHistoryHilbert.configurationMeasure ∧
    Integrable (emOriginActionSample (emOriginRawDeviation p) a b) GaussHistoryHilbert.configurationMeasure :=
  ⟨actionSample_integrable _ (rawWard_smooth p) a b,
    actionSample_integrable _ (rawScalar_smooth p) a b,
    actionSample_integrable _ (rawDeviation_smooth p) a b⟩

private theorem actionSample_mode (p : PhysicalMomentum) (a b : QuantumTest) (z : SourceCoordinateSlice) :
    (gaugeScale/2:ℝ) • sourceModeSample a b z=
      emOriginActionSample (emOriginRawWard p) a b z-emOriginActionSample (emOriginRawScalar p) a b z-
        emOriginActionSample (emOriginRawDeviation p) a b z := by
  by_cases inside : z∈tsupport a
  · have relation:=em_origin_raw_mode_ward p (sourceState z)
      (PreparationVacuumNonlinearFieldCurve.sourceState_valid ⟨z,a.tsupport_subset inside⟩)
    have paired:=congrArg (fun M : FullMatrix=>(pairRight z (a z)) (quantizer M (b z))) relation
    simp only [map_sub,LinearMap.map_smul_of_tower,ContinuousLinearMap.map_smul_of_tower,sub_apply,smul_apply] at paired
    exact paired
  · simp only [sourceModeSample,emOriginActionSample,image_eq_zero_of_notMem_tsupport inside,pairSample_zero_left,
      smul_zero,sub_self]

/-- The literal original raw chi form is the complete EM Ward minus its scalar countervariation and emitted-configuration deviation. -/
theorem em_origin_form_ward (p : PhysicalMomentum) (a b : QuantumTest) :
    (gaugeScale/2:ℝ) • sourceModeForm a b=
      emOriginWardForm p a b-emOriginScalarForm p a b-emOriginDeviationForm p a b := by
  rw [sourceModeForm,←integral_smul]
  have paid:=em_origin_forms_integrable p a b
  have pointwise : (fun z : SourceCoordinateSlice=>(gaugeScale/2:ℝ) • sourceModeSample a b z)=
      fun z=>emOriginActionSample (emOriginRawWard p) a b z-emOriginActionSample (emOriginRawScalar p) a b z-
        emOriginActionSample (emOriginRawDeviation p) a b z := funext (actionSample_mode p a b)
  rw [pointwise]
  unfold emOriginWardForm emOriginScalarForm emOriginDeviationForm
  have first:=integral_sub (paid.1.sub paid.2.1) paid.2.2
  have second:=integral_sub paid.1 paid.2.1
  simp only [Pi.sub_apply] at first
  rw [first,second]

theorem em_origin_raw_form_ward (p : PhysicalMomentum) (a b : QuantumTest) :
    (gaugeScale/2:ℝ) • (rawForm (gaugeField 1 0) p a b 0-rawForm (gaugeField 2 1) p a b 0)=
      emOriginWardForm p a b-emOriginScalarForm p a b-emOriginDeviationForm p a b := by
  rw [sourceModeForm_generated]
  exact em_origin_form_ward p a b

/-- The original finite Riesz frame consumes the separately integrated complete EM/scalar/deviation forms. -/
def emOriginWardReader (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : H→L[ℂ]H :=
  finiteRiesz F (fun i j=>emOriginWardForm p (frameTest F i) (frameTest F j))

def emOriginScalarReader (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : H→L[ℂ]H :=
  finiteRiesz F (fun i j=>emOriginScalarForm p (frameTest F i) (frameTest F j))

def emOriginDeviationReader (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : H→L[ℂ]H :=
  finiteRiesz F (fun i j=>emOriginDeviationForm p (frameTest F i) (frameTest F j))

attribute [local irreducible] emOriginWardReader emOriginScalarReader emOriginDeviationReader frameTest frameVector
local instance : NormedAlgebra ℝ (H→L[ℂ]H) := NormedAlgebra.restrictScalars ℝ ℂ _

private theorem finite_ward_sum {ι M : Type*} [Fintype ι] [AddCommGroup M] [Module ℂ M]
    (n w s d : ι→ι→ℂ) (v : ι→ι→M) (c : ℂ)
    (paid : ∀i j,c*n i j=w i j-s i j-d i j) :
    c • (∑i,∑j,n i j • v i j)=
      (∑i,∑j,w i j • v i j)-(∑i,∑j,s i j • v i j)-(∑i,∑j,d i j • v i j) := by
  simp only [Finset.smul_sum,smul_smul,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [paid,sub_smul,sub_smul]

theorem em_origin_mode_reader_ward (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    ((gaugeScale/2:ℝ):ℂ) • sourceModeReader F=
      emOriginWardReader p F-emOriginScalarReader p F-emOriginDeviationReader p F := by
  unfold sourceModeReader emOriginWardReader emOriginScalarReader emOriginDeviationReader finiteRiesz
  have generated := finite_ward_sum (ι:=FrameIndex F) (M:=H→L[ℂ]H)
    (fun i j=>sourceModeForm (frameTest F i) (frameTest F j))
    (fun i j=>emOriginWardForm p (frameTest F i) (frameTest F j))
    (fun i j=>emOriginScalarForm p (frameTest F i) (frameTest F j))
    (fun i j=>emOriginDeviationForm p (frameTest F i) (frameTest F j))
    (fun i j=>InnerProductSpace.rankOne ℂ (frameVector F i) (frameVector F j))
    ((gaugeScale/2:ℝ):ℂ) (fun i j=>by
      simpa only [Complex.real_smul] using em_origin_form_ward p (frameTest F i) (frameTest F j))
  exact generated

/-- The same EM source Lie direction is consumed by the original full action, retaining configuration, transferred current, pair and Yukawa torques. -/
theorem em_origin_original_action_ward (p k : PhysicalMomentum) (f : QuantumTest) :
    (GaussNativeForm.nativeAction+GaussCoframeForm.coframeAction+actualCore (p+k)-retainedCore)
        (chargeAction sourcePhaseGaugeLie f)-
      chargeAction sourcePhaseGaugeLie ((GaussNativeForm.nativeAction+GaussCoframeForm.coframeAction+actualCore p-retainedCore) f)=
    configurationTorque sourcePhaseGaugeLie f+CanonicalPhysicalWardCore.currentAction k sourcePhaseGaugeLie f+
      pairCurrent k sourcePhaseGaugeLie f+yukawaTorque sourcePhaseGaugeLie f := by
  exact original_action_components p k sourcePhaseGaugeLie f

end LowEnergy.GaussComposite.ActualEMOriginWard
