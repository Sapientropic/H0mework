import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedPhaseTranspose

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedPhaseConfiguration
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField FullQuantum.StateGreen
open SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert
open GaussCoreHilbert GaussCoreDifferential GaussQuantumMultiplier GaussHistoryHilbert
open PreparationVacuumMixedFieldReturn CanonicalGradedSpatialSource
open PreparationVacuumSourceFieldFamily PreparationVacuumNonlinearFieldCurve
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift PreparationVacuumActualFieldQuantization
open PreparationVacuumOriginalDensity PreparationVacuumJointFieldResponse PreparationVacuumRawJointFeedback
open PreparationVacuumFullFieldRiesz PreparationVacuumSourceActionJets PreparationVacuumPhysicalFeedback
open PreparationVacuumNoetherChart
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators Matrix Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
local instance : NormedAlgebra ℝ SourceMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : FiniteDimensional ℂ SourceMatrix:=Matrix.finiteDimensional
local instance : NormedAlgebra ℝ FullMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : FiniteDimensional ℂ FullMatrix:=Matrix.finiteDimensional
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace
local instance : NormedAlgebra ℝ Operator:=NormedAlgebra.restrictScalars ℝ ℂ _

open PreparationVacuumNativeLocalWard PreparationVacuumNativeSourceRestriction PreparationVacuumHalfDensityFiber
local instance : Fintype NativeHistoryGrade.Label:=Fintype.ofFinite _
open ActualEMOriginWard Stage9C.Material.SpinPair PreparationVacuumPhysicalModeContact


open GaussLiveMomentum GaussNativeMatter SourceQuantumScalarChart SourceQuantumResidualGaugeSlice
open StageNineP286GaugeConnectionVariationDensity
open PreparationPhysicalPhaseGaugeRealization PreparationVacuumNativeFieldInjection
open PreparationVacuumActionDecomposition StageNineHolonomicField
open ActualEMCompleteOrbit

open PreparationVacuumFieldConstraintResponse SourceGraph
open ActualDressedPhaseWard ActualDressedNoether ActualDressedFullCoulomb ActualDressedSourcePreparation
open PreparationVacuumElectricConstraint PreparationVacuumFullElectricWard CanonicalPhysicalWardCore
open CanonicalGradedCharge GaussFockPair PreparationVacuumSourcePreparedResponse
attribute [local irreducible] sourceState sourceSymbol sourceActionWeight phaseHeldAction phaseHeldMixed
  sourceReferenceState sourceDressedUnit sourceProfile jointResolvent chargeReader dressedEulerObserver prepared

def phaseConfigurationDirection (z : SourceCoordinateSlice) : SourceCoordinateSlice :=
  (0,(inverseL z (phaseAmbientDeviation z)).2)

def phaseConfigurationConnection (z : SourceCoordinateSlice) : NativeLie :=
  (inverseL z (phaseAmbientDeviation z)).1

private theorem ambient_slice (w : Slice) : phaseAmbientState (sliceMap w)=sliceState (0,w) := by
  apply Prod.ext
  · change (0:LorentzianCoframe)=GaussNativeEnergy.coframe 0 (0:Coframe)
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  apply Prod.ext
  · funext mu
    refine Fin.cases ?_ (fun j=>?_) mu
    · change spinLinear 0 0+nativePrimal 0=0
      rw [map_zero,map_zero,zero_add]
    · change spinLinear j.succ 0+nativePrimal (gaugeCoordinates (w.2:Gauge) j)=
        nativePrimal (gaugeCoordinates (w.2:Gauge) j)
      rw [map_zero,zero_add]
  · rfl

/-- The original ambient inverse generates both the genuine configuration displacement and its connection compensation. -/
theorem phase_configuration_tangent (z : physicalChart) :
    emOriginDeviationState (sourceState z.val)=
      sliceState (phaseConfigurationDirection z.val)+
        phaseAmbientState (orbitMap z.val (phaseConfigurationConnection z.val)) := by
  have full:=congrArg phaseAmbientState (inverse_right z (phaseAmbientDeviation z.val))
  change phaseAmbientState (orbitMap z.val (phaseConfigurationConnection z.val)+
    sliceMap (inverseL z.val (phaseAmbientDeviation z.val)).2)=phaseAmbientState (phaseAmbientDeviation z.val) at full
  rw [map_add,ambient_slice] at full
  exact (phase_deviation_actual_state z.val).trans (full.symm.trans (add_comm _ _))

private theorem configuration_symbol_derivative (p : PhysicalMomentum) (z : physicalChart) (h : SourceCoordinateSlice) :
    fderiv ℝ (fun w : SourceCoordinateSlice=>sourceSymbol p (sourceState w)) z.val h=
      symbolFirst p (sourceState z.val) (sliceState h) := by
  have valid : sourceState z.val∈validStates := by
    unfold sourceState
    exact ⟨coframe_nondegenerate z,temporal_noncharacteristic z⟩
  have outer:=(sourceSymbol_smooth p (sourceState z.val) valid).differentiableAt (by simp)
  have inner:=(sourceState_smooth.differentiable (by simp)).differentiableAt (x:=z.val)
  change fderiv ℝ (sourceSymbol p ∘ sourceState) z.val h=_
  rw [fderiv_comp z.val outer inner,sourceState_fderiv]
  rfl

/-- The same held full504 Noether deviation consumes the actual source-coordinate derivative plus its uncompensated vertical state. -/
theorem phase_deviation_held_configuration (p : PhysicalMomentum) (z : physicalChart) :
    phaseHeldAction .deviation p (sourceState z.val) (sourceState z.val)=
      -(4:ℂ) • (sourceActionWeight (sourceState z.val)*
        (fderiv ℝ (fun w : SourceCoordinateSlice=>sourceSymbol p (sourceState w)) z.val
          (phaseConfigurationDirection z.val)+
        symbolFirst p (sourceState z.val)
          (phaseAmbientState (orbitMap z.val (phaseConfigurationConnection z.val))))) := by
  have first:=congrArg (fderiv ℝ (sourceSymbol p) (sourceState z.val)) (phase_configuration_tangent z)
  rw [map_add] at first
  have generated:=congrArg (fun M : FullMatrix=> -(4:ℂ) • (sourceActionWeight (sourceState z.val)*M)) first
  rw [configuration_symbol_derivative]
  simpa only [phaseHeldAction,phaseDirection,symbolFirst] using generated

/-- The original full289 mixed contact keeps the source-coordinate variation and every non-chart fiber/coframe complement. -/
theorem phase_deviation_mixed_configuration (force : Field289) (p : PhysicalMomentum) (z : physicalChart) :
    phaseHeldMixed .deviation force p (sourceState z.val) (sourceState z.val)=
      -(4:ℂ) • (sourceActionWeight (sourceState z.val)*
        (symbolSecond p (sourceState z.val) (sliceState (phaseConfigurationDirection z.val)) (fieldDirection force)+
        symbolSecond p (sourceState z.val)
          (phaseAmbientState (orbitMap z.val (phaseConfigurationConnection z.val))) (fieldDirection force)+
        (symbolFirst p (sourceState z.val)
          (phaseAmbientState (variationL (PreparationVacuumFieldConstraintResponse.fieldVector force z.val) (sourcePhaseGaugeLie,0)))+
        symbolFirst p (sourceState z.val) (emGaugeState (complement force z.val))))) := by
  have second:=congrArg
    (fderiv ℝ (fderiv ℝ (sourceSymbol p)) (sourceState z.val) (fieldDirection force))
      (phase_configuration_tangent z)
  rw [map_add] at second
  have contact:=congrArg (fderiv ℝ (sourceSymbol p) (sourceState z.val)) (phase_deviation_field_contact force z.val)
  rw [map_add] at contact
  simpa only [phaseHeldMixed,phaseDirection,phaseDirectionContact,symbolFirst,symbolSecond] using
    congrArg₂ (fun A B : FullMatrix=> -(4:ℂ) • (sourceActionWeight (sourceState z.val)*(A+B))) second contact

/-- The original weighted full504 density is kept inside one quantizer; CAR is not treated as a multiplicative map. -/
def phaseSourceActionFiber (p : PhysicalMomentum) (z : SourceCoordinateSlice) : FockFiber→L[ℂ]FockFiber :=
  quantizer (-(4:ℂ) • (sourceActionWeight (sourceState z)*sourceSymbol p (sourceState z)))

private theorem action_fiber_smooth (p : PhysicalMomentum) (z : physicalChart) :
    ContDiffAt ℝ ∞ (phaseSourceActionFiber p) z.val := by
  have valid : sourceState z.val∈validStates := by
    unfold sourceState
    exact ⟨coframe_nondegenerate z,temporal_noncharacteristic z⟩
  have state:=sourceState_smooth.contDiffAt (x:=z.val)
  have weight:=(sourceActionWeight_smooth (sourceState z.val) valid).comp z.val state
  have symbol:=(sourceSymbol_smooth p (sourceState z.val) valid).comp z.val state
  exact (quantizer.toContinuousLinearMap.restrictScalars ℝ).contDiff.contDiffAt.comp z.val
    ((weight.mul symbol).const_smul (-(4:ℂ)))

def phaseSourceActionMultiplier (p : PhysicalMomentum) : QuantumTest→ₗ[ℂ]QuantumTest :=
  localMultiplier (phaseSourceActionFiber p) (action_fiber_smooth p)

private theorem action_fiber_product_derivative (p : PhysicalMomentum) (f : QuantumTest)
    (z : physicalChart) (h : SourceCoordinateSlice) :
    fderiv ℝ (phaseSourceActionMultiplier p f) z.val h=
      (fderiv ℝ (phaseSourceActionFiber p) z.val h) (f z.val)+
        phaseSourceActionFiber p z.val (fderiv ℝ f z.val h) := by
  let R:=ContinuousLinearMap.restrictScalarsL ℂ FockFiber FockFiber ℝ ℝ
  have D:=(action_fiber_smooth p z).differentiableAt (by simp) |>.hasFDerivAt
  have restricted:=R.hasFDerivAt.comp z.val D
  have input:=(f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt (x:=z.val)
  have product:=restricted.clm_apply input
  change fderiv ℝ (fun w=>((⇑R ∘ phaseSourceActionFiber p) w) (f w)) z.val h=_
  rw [product.fderiv]
  change phaseSourceActionFiber p z.val (fderiv ℝ f z.val h)+
    (fderiv ℝ (phaseSourceActionFiber p) z.val h) (f z.val)=_
  exact add_comm _ _

private theorem quantum_leibniz {V : Type*} [AddCommGroup V] [Module ℂ V]
    (M Q D : V→ₗ[ℂ]V) (v dv : V) :
    (-Complex.I) • (D v+M dv+Q (M v))-M ((-Complex.I) • (dv+Q v))=
      (-Complex.I) • (D v+(Q*M-M*Q) v) := by
  simp only [map_smul,map_add,smul_add,Module.End.mul_apply,LinearMap.sub_apply,smul_sub]
  abel

/-- The genuine quantum configuration Ward differentiates the same original density on the same test profile, retaining its native connection commutator. -/
theorem phase_configuration_quantum_leibniz (p : PhysicalMomentum) (f : QuantumTest) (z : physicalChart) :
    phaseDevAction (phaseSourceActionMultiplier p f) z.val-
      phaseSourceActionFiber p z.val (phaseDevAction f z.val)=
    (-Complex.I) •
      ((fderiv ℝ (phaseSourceActionFiber p) z.val (phaseConfigurationDirection z.val)) (f z.val)+
        (nativeFock (phaseConfigurationConnection z.val)*phaseSourceActionFiber p z.val-
          phaseSourceActionFiber p z.val*nativeFock (phaseConfigurationConnection z.val)) (f z.val)) := by
  rw [phase_dev_action_actual,covariantMomentum_apply,phase_dev_action_actual,covariantMomentum_apply]
  change (-Complex.I) •
      (fderiv ℝ (phaseSourceActionMultiplier p f) z.val (phaseConfigurationDirection z.val)+
        nativeFock (phaseConfigurationConnection z.val) (phaseSourceActionFiber p z.val (f z.val)))-
      phaseSourceActionFiber p z.val ((-Complex.I) •
        (fderiv ℝ f z.val (phaseConfigurationDirection z.val)+nativeFock (phaseConfigurationConnection z.val) (f z.val)))=_
  rw [action_fiber_product_derivative]
  exact quantum_leibniz (phaseSourceActionFiber p z.val).toLinearMap
    (nativeFock (phaseConfigurationConnection z.val)).toLinearMap
    (fderiv ℝ (phaseSourceActionFiber p) z.val (phaseConfigurationDirection z.val)).toLinearMap
    (f z.val) (fderiv ℝ f z.val (phaseConfigurationDirection z.val))

def phaseWeightDerivative (p : PhysicalMomentum) (z : SourceCoordinateSlice) : FullMatrix :=
  -(4:ℂ) • ((fderiv ℝ (fun w : SourceCoordinateSlice=>sourceActionWeight (sourceState w)) z
    (phaseConfigurationDirection z))*sourceSymbol p (sourceState z))

def phaseVerticalAction (p : PhysicalMomentum) (z : SourceCoordinateSlice) : FullMatrix :=
  -(4:ℂ) • (sourceActionWeight (sourceState z)*symbolFirst p (sourceState z)
    (phaseAmbientState (orbitMap z (phaseConfigurationConnection z))))

private theorem density_fderivative (p : PhysicalMomentum) (z : physicalChart) (h : SourceCoordinateSlice) :
    fderiv ℝ (phaseSourceActionFiber p) z.val h=
      quantizer (-(4:ℂ) •
        (sourceActionWeight (sourceState z.val)*
          fderiv ℝ (fun w : SourceCoordinateSlice=>sourceSymbol p (sourceState w)) z.val h+
        (fderiv ℝ (fun w : SourceCoordinateSlice=>sourceActionWeight (sourceState w)) z.val h)*
          sourceSymbol p (sourceState z.val))) := by
  have valid : sourceState z.val∈validStates := by
    unfold sourceState
    exact ⟨coframe_nondegenerate z,temporal_noncharacteristic z⟩
  have state:=sourceState_smooth.contDiffAt (x:=z.val)
  have weight:=((sourceActionWeight_smooth (sourceState z.val) valid).comp z.val state).differentiableAt (by simp)
  have symbol:=((sourceSymbol_smooth p (sourceState z.val) valid).comp z.val state).differentiableAt (by simp)
  have density:=(weight.hasFDerivAt.mul' symbol.hasFDerivAt).const_smul (-(4:ℂ))
  have full:=(quantizer.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp z.val density
  change fderiv ℝ ((quantizer.toContinuousLinearMap.restrictScalars ℝ) ∘
    (-(4:ℂ) • ((sourceActionWeight ∘ sourceState)*(sourceSymbol p ∘ sourceState)))) z.val h=_
  rw [full.fderiv]
  rfl

/-- Holding W in the Noether reader subtracts its real configuration derivative; the original vertical source term is retained separately. -/
theorem phase_deviation_quantized_density (p : PhysicalMomentum) (z : physicalChart) :
    quantizer (phaseHeldAction .deviation p (sourceState z.val) (sourceState z.val))=
      fderiv ℝ (phaseSourceActionFiber p) z.val (phaseConfigurationDirection z.val)-
        quantizer (phaseWeightDerivative p z.val)+quantizer (phaseVerticalAction p z.val) := by
  have noether:=congrArg quantizer (phase_deviation_held_configuration p z)
  have density:=density_fderivative p z (phaseConfigurationDirection z.val)
  simp only [mul_add,smul_add,map_add] at noether density
  rw [noether,density]
  unfold phaseWeightDerivative phaseVerticalAction
  abel

private theorem quantum_ward_return {V : Type*} [AddCommGroup V] [Module ℂ V]
    (J D Q W A C : V) (current : J=D-W+A) (ward : C=(-Complex.I) • (D+Q)) :
    J=Complex.I • C-Q-W+A := by
  rw [ward,smul_smul,mul_neg,Complex.I_mul_I,neg_neg,one_smul,current]
  abel

/-- A true quantum Ward for the actual held deviation: profile derivative, native connection, density-weight derivative and vertical source action remain explicit. -/
theorem phase_deviation_quantum_ward (p : PhysicalMomentum) (f : QuantumTest) (z : physicalChart) :
    quantizer (phaseHeldAction .deviation p (sourceState z.val) (sourceState z.val)) (f z.val)=
      Complex.I • (phaseDevAction (phaseSourceActionMultiplier p f) z.val-
        phaseSourceActionFiber p z.val (phaseDevAction f z.val))-
      (nativeFock (phaseConfigurationConnection z.val)*phaseSourceActionFiber p z.val-
        phaseSourceActionFiber p z.val*nativeFock (phaseConfigurationConnection z.val)) (f z.val)-
      quantizer (phaseWeightDerivative p z.val) (f z.val)+quantizer (phaseVerticalAction p z.val) (f z.val) := by
  have current:=congrArg (fun A : FockFiber→L[ℂ]FockFiber=>A (f z.val)) (phase_deviation_quantized_density p z)
  simp only [sub_apply,add_apply] at current
  exact quantum_ward_return _ _ _ _ _ _ current (phase_configuration_quantum_leibniz p f z)

/-- These are the actual native-connection, changing-density and vertical-action terms; none is assigned zero. -/
def phaseConfigurationCompensation (p : PhysicalMomentum) (b : QuantumTest) (z : SourceCoordinateSlice) : FockFiber :=
  (nativeFock (phaseConfigurationConnection z)*phaseSourceActionFiber p z-
    phaseSourceActionFiber p z*nativeFock (phaseConfigurationConnection z)) (b z)+
    quantizer (phaseWeightDerivative p z) (b z)-quantizer (phaseVerticalAction p z) (b z)

def phaseConfigurationCompensationSample (p : PhysicalMomentum) (a b : QuantumTest) (z : SourceCoordinateSlice) : ℂ :=
  (pairRight z (a z)) (phaseConfigurationCompensation p b z)

private theorem source_pair_integral (f g : QuantumTest) :
    (∫z,(pairRight z (f z)) (g z) ∂GaussHistoryHilbert.configurationMeasure)=sourcePair f g := by
  rw [sourcePair_integral]
  exact integral_congr_ae (Eventually.of_forall (fun z=>pairSample_source f g z))

private theorem source_pair_integrable (f g : QuantumTest) :
    Integrable (fun z=>(pairRight z (f z)) (g z)) GaussHistoryHilbert.configurationMeasure :=
  (densityPair_integrable f g).congr (Eventually.of_forall (fun z=>(pairSample_source f g z).symm))

private theorem source_pair_ward {V : Type*} [AddCommGroup V] [Module ℂ V]
    (L : V→ₗ[ℂ]ℂ) (J C D Q W A : V) (paid : J=Complex.I • (C-D)-Q-W+A) :
    L J=Complex.I*(L C-L D)-L (Q+W-A) := by
  rw [paid]
  simp only [map_add,map_sub,map_smul,smul_eq_mul]
  ring

private theorem deviation_sample_ward (p : PhysicalMomentum) (a b : QuantumTest) (z : SourceCoordinateSlice) :
    phaseSample .deviation p a b (0,z)=
      Complex.I*((pairRight z (a z)) (phaseDevAction (phaseSourceActionMultiplier p b) z)-
        (pairRight z (a z)) (phaseSourceActionMultiplier p (phaseDevAction b) z))-
      phaseConfigurationCompensationSample p a b z := by
  by_cases inside : z∈tsupport a
  · let point : physicalChart:=⟨z,a.tsupport_subset inside⟩
    have generated:=source_pair_ward (pairRight z (a z)).toLinearMap _ _ _ _ _ _
      (phase_deviation_quantum_ward p b point)
    simp only [phaseSample,ambientState_zero,phaseConfigurationCompensationSample,phaseConfigurationCompensation]
    change (pairRight z (a z)) (quantizer (phaseHeldAction .deviation p (sourceState z) (sourceState z)) (b z))=
      Complex.I*((pairRight z (a z)) (phaseDevAction (phaseSourceActionMultiplier p b) z)-
        (pairRight z (a z)) (phaseSourceActionFiber p z (phaseDevAction b z)))-
      (pairRight z (a z)) (phaseConfigurationCompensation p b z)
    exact generated
  · simp only [phaseSample,image_eq_zero_of_notMem_tsupport inside,pairSample_zero_left,
      phaseConfigurationCompensationSample]
    change 0=Complex.I*(pairSample z 0 _-pairSample z 0 _)-pairSample z 0 _
    simp only [pairSample_zero_left,sub_self,mul_zero]

/-- Original weighted integration by parts converts the held deviation into the actual profile action plus the generated source corrections. -/
theorem phase_deviation_configuration_form (p : PhysicalMomentum) (a b : QuantumTest) :
    phaseForm .deviation p a b 0=
      Complex.I*(sourcePair (phaseDevAdjoint a) (phaseSourceActionMultiplier p b)-
        sourcePair a (phaseSourceActionMultiplier p (phaseDevAction b)))-
      ∫z,phaseConfigurationCompensationSample p a b z ∂GaussHistoryHilbert.configurationMeasure := by
  have first:=source_pair_integrable a (phaseDevAction (phaseSourceActionMultiplier p b))
  have second:=source_pair_integrable a (phaseSourceActionMultiplier p (phaseDevAction b))
  have original:=phase_forms_integrable .deviation p a b 0 (by simpa using ambientRadius_positive a)
  have correction : Integrable (phaseConfigurationCompensationSample p a b) GaussHistoryHilbert.configurationMeasure := by
    apply (((first.sub second).const_mul Complex.I).sub original).congr
    exact Eventually.of_forall (fun z=>by
      have generated:=deviation_sample_ward p a b z
      simp only [Pi.sub_apply] at generated ⊢
      linear_combination -generated)
  unfold phaseForm
  calc
    _=∫z,Complex.I*((pairRight z (a z)) (phaseDevAction (phaseSourceActionMultiplier p b) z)-
        (pairRight z (a z)) (phaseSourceActionMultiplier p (phaseDevAction b) z))-
      phaseConfigurationCompensationSample p a b z ∂GaussHistoryHilbert.configurationMeasure :=
      integral_congr_ae (Eventually.of_forall (deviation_sample_ward p a b))
    _=_ := by
      have separated:=integral_sub ((first.sub second).const_mul Complex.I) correction
      simp only [Pi.sub_apply] at separated
      rw [separated,integral_const_mul]
      have subtract:=integral_sub first second
      rw [subtract,source_pair_integral,source_pair_integral,phase_dev_weighted_pair]

/-- Same-F finite completion is now a true weighted configuration/profile Ward for the original held Noether reader. -/
theorem phase_deviation_configuration_reader (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    phaseReader .deviation p F 0=finiteRiesz F (fun i j=>
      Complex.I*(sourcePair (phaseDevAdjoint (frameTest F i)) (phaseSourceActionMultiplier p (frameTest F j))-
        sourcePair (frameTest F i) (phaseSourceActionMultiplier p (phaseDevAction (frameTest F j))))-
      ∫z,phaseConfigurationCompensationSample p (frameTest F i) (frameTest F j) z ∂GaussHistoryHilbert.configurationMeasure) := by
  unfold phaseReader
  exact congrArg (finiteRiesz F) (funext (fun i=>funext (fun j=>phase_deviation_configuration_form p (frameTest F i) (frameTest F j))))

/-- Actual dense prepared tests retain both configuration terms; neither is presumed to have an individual completed domain. -/
def phaseConfigurationRead (F : GaussUnitaryHistory.Index) (x y : H) : ℂ :=
  sourcePair (sourceTestApprox F x)
    (phaseDevAction (sourceTestApprox F y)+covariantMomentum phaseAmbientReference (sourceTestApprox F y))

def phaseConfigurationTransposeRead (F : GaussUnitaryHistory.Index) (x y : H) : ℂ :=
  sourcePair (phaseDevAdjoint (sourceTestApprox F x)+
    GaussMomentumAdjoint.adjoint phaseAmbientReference (sourceTestApprox F x)) (sourceTestApprox F y)

theorem phase_configuration_actual_transpose (F : GaussUnitaryHistory.Index) (x y : H) :
    phaseConfigurationRead F x y=phaseConfigurationTransposeRead F x y := by
  have left:=phase_dev_weighted_pair (sourceTestApprox F x) (sourceTestApprox F y)
  have right:=GaussMomentumAdjoint.momentum_pair phaseAmbientReference (sourceTestApprox F x) (sourceTestApprox F y)
  simpa only [phaseConfigurationRead,phaseConfigurationTransposeRead,sourcePair,map_add,inner_add_left,inner_add_right]
    using congrArg₂ (fun a b : ℂ=>a+b) left right

private theorem complete_phase_core (f : QuantumTest) :
    embed (phaseDevAction f+covariantMomentum phaseAmbientReference f)=
      (-chargeReader sourcePhaseGaugeLie) (embed f) := by
  have original:=congrArg (fun A : QuantumTest→ₗ[ℂ]QuantumTest=>embed (A f)) phase_dev_gauss_return
  simpa only [LinearMap.add_apply,LinearMap.neg_apply,map_neg,chargeReader_core,neg_apply] using original

/-- The original source approximation generates the complete joint configuration observation on the same two Hilbert vectors. -/
theorem phase_configuration_source_limit (x y : H) :
    Tendsto (fun F : GaussUnitaryHistory.Index=>phaseConfigurationRead F x y) GaussUnitaryHistory.sourceFilter
      (𝓝 (inner ℂ x ((-chargeReader sourcePhaseGaugeLie) y))) := by
  have left:=same_source_approximation x
  have right:=(-chargeReader sourcePhaseGaugeLie).continuous.tendsto y |>.comp (same_source_approximation y)
  simpa only [phaseConfigurationRead,sourcePair,complete_phase_core,Function.comp_apply] using left.inner right

/-- Original full action and actual profile torque are retained on the complete deviation/reference generator. -/
theorem phase_configuration_original_action (p k : PhysicalMomentum) (f : QuantumTest) :
    (GaussNativeForm.nativeAction+GaussCoframeForm.coframeAction+actualCore (p+k)-retainedCore)
      (phaseDevAction f+covariantMomentum phaseAmbientReference f)-
      (phaseDevAction+covariantMomentum phaseAmbientReference)
        ((GaussNativeForm.nativeAction+GaussCoframeForm.coframeAction+actualCore p-retainedCore) f)=
    -(configurationTorque sourcePhaseGaugeLie f+CanonicalPhysicalWardCore.currentAction k sourcePhaseGaugeLie f+
      pairCurrent k sourcePhaseGaugeLie f+yukawaTorque sourcePhaseGaugeLie f) := by
  have input:=LinearMap.congr_fun phase_dev_gauss_return f
  change phaseDevAction f+covariantMomentum phaseAmbientReference f= -chargeAction sourcePhaseGaugeLie f at input
  rw [input,phase_dev_gauss_return,LinearMap.neg_apply,map_neg]
  have original:=original_action_components p k sourcePhaseGaugeLie f
  have negative:=congrArg Neg.neg original
  simp only [wardCore,LinearMap.add_apply] at negative
  convert negative using 1
  abel

/-- The same actual unit/background and the original uncut two resolvents supply both dense-test legs. -/
def phaseDressedConfigurationRead (event : DressedEvent) (transfer : PhysicalMomentum)
    (readFrame : GaussUnitaryHistory.Index) : ℂ :=
  -phaseConfigurationRead readFrame
    ((jointResolvent (event.momentum-transfer) event.frame event.energy 0).adjoint
      (sourceDressedUnit event.epsilon event.precision))
    (jointResolvent event.momentum event.frame event.energy 0 (sourceDressedUnit event.epsilon event.precision))+
  phaseConfigurationRead readFrame
    ((jointResolvent (event.momentum-transfer) event.frame event.energy 0).adjoint
      (prepared (sourceProfile event.epsilon event.precision)))
    (jointResolvent event.momentum event.frame event.energy 0 (prepared (sourceProfile event.epsilon event.precision)))

private theorem two_leg_pair (L Q R : H→L[ℂ]H) (x : H) :
    inner ℂ (L.adjoint x) (Q (R x))=inner ℂ x ((L*Q*R) x) := by
  rw [ContinuousLinearMap.adjoint_inner_left]
  rfl

attribute [local irreducible] phaseDressedConfigurationRead

/-- The complete configuration generator reaches the actual Noether observer; separate deviation/reference completion is not assumed. -/
theorem phase_dressed_configuration_limit (event : DressedEvent) (transfer : PhysicalMomentum) :
    Tendsto (phaseDressedConfigurationRead event transfer) GaussUnitaryHistory.sourceFilter
      (𝓝 (dressedEulerObserver event
        ((jointResolvent (event.momentum-transfer) event.frame event.energy 0 : H→L[ℂ]H)*
          (-chargeReader sourcePhaseGaugeLie : H→L[ℂ]H)*
          (jointResolvent event.momentum event.frame event.energy 0 : H→L[ℂ]H)))) := by
  have unit:=phase_configuration_source_limit
    ((jointResolvent (event.momentum-transfer) event.frame event.energy 0).adjoint
      (sourceDressedUnit event.epsilon event.precision))
    (jointResolvent event.momentum event.frame event.energy 0 (sourceDressedUnit event.epsilon event.precision))
  have background:=phase_configuration_source_limit
    ((jointResolvent (event.momentum-transfer) event.frame event.energy 0).adjoint
      (prepared (sourceProfile event.epsilon event.precision)))
    (jointResolvent event.momentum event.frame event.energy 0 (prepared (sourceProfile event.epsilon event.precision)))
  have generated:=unit.neg.add background
  have unitPair:=two_leg_pair
    (jointResolvent (event.momentum-transfer) event.frame event.energy 0)
    (-chargeReader sourcePhaseGaugeLie) (jointResolvent event.momentum event.frame event.energy 0)
    (sourceDressedUnit event.epsilon event.precision)
  have backgroundPair:=two_leg_pair
    (jointResolvent (event.momentum-transfer) event.frame event.energy 0)
    (-chargeReader sourcePhaseGaugeLie) (jointResolvent event.momentum event.frame event.energy 0)
    (prepared (sourceProfile event.epsilon event.precision))
  have pairSame:=congrArg₂ (fun a b : ℂ=> -a+b) unitPair backgroundPair
  have observerSame:=pairSame.trans (dressed_euler_observer_original event
    (jointResolvent (event.momentum-transfer) event.frame event.energy 0*
      (-chargeReader sourcePhaseGaugeLie)*jointResolvent event.momentum event.frame event.energy 0)).symm
  have dense : Tendsto (phaseDressedConfigurationRead event transfer) GaussUnitaryHistory.sourceFilter
      (𝓝 (-inner ℂ
        ((jointResolvent (event.momentum-transfer) event.frame event.energy 0).adjoint
          (sourceDressedUnit event.epsilon event.precision))
        ((-chargeReader sourcePhaseGaugeLie)
          (jointResolvent event.momentum event.frame event.energy 0 (sourceDressedUnit event.epsilon event.precision)))+
      inner ℂ ((jointResolvent (event.momentum-transfer) event.frame event.energy 0).adjoint
          (prepared (sourceProfile event.epsilon event.precision)))
        ((-chargeReader sourcePhaseGaugeLie)
          (jointResolvent event.momentum event.frame event.energy 0 (prepared (sourceProfile event.epsilon event.precision)))))) := by
    unfold phaseDressedConfigurationRead
    exact generated
  exact Eq.mp (congrArg (fun value : ℂ=>Tendsto (phaseDressedConfigurationRead event transfer)
    GaussUnitaryHistory.sourceFilter (𝓝 value)) observerSame) dense

end LowEnergy.GaussComposite.ActualDressedPhaseConfiguration
