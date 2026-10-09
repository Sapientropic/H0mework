import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceFirstHarmonicGaugeProfile

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalFirstPoleGaugeRemainder
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

open PreparationVacuumPhysicalChargedFieldFactor
open SourcePropagationNativeActionHessian StageNineLorentzConnectionVariation
open StageNineP286BracketCalculus StageNineP286InfinitesimalGaugeTransformation
open SU7MotherGaugeTheory StageNineP286GaugeConnectionVariation
local instance : Fintype P286CoordinateIndex:=StageNineP286InfinitesimalGaugeTransformation.p286CoordinateIndexFintype

open Lean Elab Term in
elab "paidFirstChannelLinear%" : term => do
  let wanted:=`LowEnergy.PreparationVacuumChargedLongRangeRead.linear_matrix
  let all:=(←getEnv).constants.toList
  let found:=all.filter fun (name,_)=>name.toString.startsWith "_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceChargedStaticLaurent." && privateToUserName name==wanted
  match found with
  | [(name,_)]=>logInfo m!"Original private payer: {name}";return mkConst name
  | _=>throwError "Expected unique original SourceChargedStaticLaurent.linear_matrix, actual candidates {all.filterMap (fun (name,_)=>if privateToUserName name==wanted then some name else none)}"

private theorem channel_degree : ∀t∈sourceEnergyChannelTerms,t.powers.total=1 := by decide +kernel

private def channelLinear : (Fin 4→ℂ)→ₗ[ℂ]Matrix (Fin 289) (Fin 289) ℂ where
  toFun:=sourceMatrix sourceEnergyChannelTerms
  map_add' v w:=by
    simpa only [one_smul] using paidFirstChannelLinear% sourceEnergyChannelTerms channel_degree v w 1
  map_smul' z v:=by
    have H:=paidFirstChannelLinear% sourceEnergyChannelTerms channel_degree 0 v z
    have zero : sourceMatrix sourceEnergyChannelTerms 0=0 := by
      have H:=paidFirstChannelLinear% sourceEnergyChannelTerms channel_degree 0 0 1
      simp only [smul_zero,zero_add,one_smul] at H
      exact (add_eq_left.mp H.symm)
    simpa only [zero_add,zero,RingHom.id_apply] using H

/-- Every original row of the actual first-frame column is retained in the generated coordinate expansion. -/
theorem sourceFirstLiteralField_generated (v : Fin 4→ℂ) (row : Fin 289) :
    sourceChargedNativeFrameJet v row 1=
      ∑mu : Fin 4,v mu*(sourceEnergyAxisField 1 mu row:ℂ) := by
  have coordinates : v=∑mu : Fin 4,v mu • Pi.single mu 1 := by
    ext j
    simp [Finset.sum_apply,Pi.single_apply]
  have generated:=congrArg channelLinear coordinates
  simp only [map_sum,map_smul] at generated
  have entry:=congrArg (fun M : Matrix (Fin 289) (Fin 289) ℂ=>M row 1) generated
  change sourceMatrix sourceEnergyChannelTerms v row 1=_ at entry
  have column : (⟨(1:Fin 3).val,by decide⟩:Fin 289)=(1:Fin 289) := by decide
  have actual:=sourceEnergyChannelMatrix_entry v row (1:Fin 3)
  rw [column] at actual
  rw [actual] at entry
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul] at entry
  convert entry using 1
  apply Finset.sum_congr rfl
  intro mu _
  have axis:=congrFun (sourceEnergyAxisField_cast 1 mu) row
  exact congrArg (fun z : ℂ=>v mu*z) axis

/-- Two quadratures of one actual emitted mode; no complex scalar acts on a real configuration. -/
def sourceFirstModeField (imaginary : Bool) (omega : ℝ) (k : PhysicalMomentum) (x : BasePoint) : Field289 :=
  ∑mu : Fin 4,(-sourceFirstGaugeQuadratureDerivative imaginary omega k x mu) • sourceEnergyAxisField 1 mu

theorem sourceFirstModeField_complex (omega : ℝ) (k : PhysicalMomentum) (x : BasePoint) (row : Fin 289) :
    (sourceFirstModeField false omega k x row:ℂ)+Complex.I*(sourceFirstModeField true omega k x row:ℂ)=
      sourceFirstHarmonicPhase omega k x*sourceChargedNativeFrameJet (physicalFrequencyMomentum omega k) row 1 := by
  rw [sourceFirstLiteralField_generated,Finset.mul_sum]
  simp only [sourceFirstModeField,Finset.sum_apply,Pi.smul_apply,sourceFirstGaugeQuadratureDerivative,
    Bool.false_eq_true,ite_false,ite_true,neg_neg,smul_eq_mul,Complex.ofReal_sum,Complex.ofReal_mul,
    Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro mu _
  calc
    _=((sourceFirstHarmonicPhase omega k x*physicalFrequencyMomentum omega k mu).re+
      (sourceFirstHarmonicPhase omega k x*physicalFrequencyMomentum omega k mu).im*Complex.I)*
        (sourceEnergyAxisField 1 mu row:ℂ) := by ring
    _=_ := by rw [Complex.re_add_im];ring

/-- The full source-field tangent uses precisely the original nativeConfiguration insertions. -/
def sourceFirstModeTangent (imaginary : Bool) (omega : ℝ) (k : PhysicalMomentum) : StageNineHolonomicConfiguration where
  coframe x:=fieldCoframe (sourceFirstModeField imaginary omega k x)
  gravityConnection x:=lorentzSkewConnectionOfBivectorOneForm (fieldLorentz (sourceFirstModeField imaginary omega k x))
  gravityAuxiliary x:=fieldGravityB (sourceFirstModeField imaginary omega k x)
  gravitySimplicityMultiplier x:=fieldMultiplier (sourceFirstModeField imaginary omega k x)
  gaugeConnection x mu:=p286CoordinateEquiv.symm (fieldGauge (sourceFirstModeField imaginary omega k x) mu)
  gaugeAuxiliary x pair:=gaugeBInsertion (sourceFirstModeField imaginary omega k x) pair
  scalar x:=fieldScalar (sourceFirstModeField imaginary omega k x)
  matter x:=diracMatrixMatterAction (ActiveGauge.rotation x) (primalInsertion (sourceFirstModeField imaginary omega k x))
  conjugateMatter x:=(dualInsertion (sourceFirstModeField imaginary omega k x)).comp (diracMatrixMatterAction (ActiveGauge.rotation x))

/-- The actual gauge parameter is generated from the same real quadrature. -/
def sourceFirstModeParameter (imaginary : Bool) (omega : ℝ) (k : PhysicalMomentum) : BasePoint→P286CoordinateCarrier :=
  fun x=>sourceFirstGaugeQuadrature imaginary omega k x • sourceFirstTemporalLie

/-- Full nine-field gauge variation, with the parameter derivative generated by the physical mode. -/
def sourceFirstModeGauge (imaginary : Bool) (omega : ℝ) (k : PhysicalMomentum)
    (c : StageNineHolonomicConfiguration) : StageNineHolonomicConfiguration where
  coframe:=0
  gravityConnection:=0
  gravityAuxiliary:=0
  gravitySimplicityMultiplier:=0
  gaugeConnection x mu:=sourceFirstGaugeQuadrature imaginary omega k x • (sourceFirstGaugePrimitive c).gaugeConnection x mu-
    sourceFirstGaugeQuadratureDerivative imaginary omega k x mu • p286CoordinateEquiv.symm sourceFirstTemporalLie
  gaugeAuxiliary x pair:=sourceFirstGaugeQuadrature imaginary omega k x • (sourceFirstGaugePrimitive c).gaugeAuxiliary x pair
  scalar x:=sourceFirstGaugeQuadrature imaginary omega k x • (sourceFirstGaugePrimitive c).scalar x
  matter x:=sourceFirstGaugeQuadrature imaginary omega k x • (sourceFirstGaugePrimitive c).matter x
  conjugateMatter x:=sourceFirstGaugeQuadrature imaginary omega k x • (sourceFirstGaugePrimitive c).conjugateMatter x

/-- Every configuration field has its computed difference; matter, dual and auxiliary components are not projected away. -/
def sourceFirstModeRemainder (imaginary : Bool) (omega : ℝ) (k : PhysicalMomentum)
    (c : StageNineHolonomicConfiguration) : StageNineHolonomicConfiguration where
  coframe x:=(sourceFirstModeTangent imaginary omega k).coframe x
  gravityConnection x:=(sourceFirstModeTangent imaginary omega k).gravityConnection x
  gravityAuxiliary x:=(sourceFirstModeTangent imaginary omega k).gravityAuxiliary x
  gravitySimplicityMultiplier x:=(sourceFirstModeTangent imaginary omega k).gravitySimplicityMultiplier x
  gaugeConnection x mu:=(sourceFirstModeTangent imaginary omega k).gaugeConnection x mu-(sourceFirstModeGauge imaginary omega k c).gaugeConnection x mu
  gaugeAuxiliary x pair:=(sourceFirstModeTangent imaginary omega k).gaugeAuxiliary x pair-(sourceFirstModeGauge imaginary omega k c).gaugeAuxiliary x pair
  scalar x:=(sourceFirstModeTangent imaginary omega k).scalar x-(sourceFirstModeGauge imaginary omega k c).scalar x
  matter x:=(sourceFirstModeTangent imaginary omega k).matter x-(sourceFirstModeGauge imaginary omega k c).matter x
  conjugateMatter x:=(sourceFirstModeTangent imaginary omega k).conjugateMatter x-(sourceFirstModeGauge imaginary omega k c).conjugateMatter x

/-- The original configuration, including its rotated primal and independent dual insertions, is the same shared occurrence. -/
theorem sourceFirstModeTangent_original (imaginary : Bool) (omega : ℝ) (k : PhysicalMomentum) :
    nativeConfiguration (sourceFirstModeField imaginary omega k)=
      configurationRay actual (sourceFirstModeTangent imaginary omega k) 1 := by
  apply StageNineHolonomicConfiguration.ext <;> funext x
  all_goals simp only [nativeConfiguration,configurationRay,sourceFirstModeTangent,one_smul]

/-- The parameter derivative is proved from the common harmonic, not supplied by the caller. -/
theorem sourceFirstModeParameter_derivative (imaginary : Bool) (omega : ℝ) (k : PhysicalMomentum)
    (x : BasePoint) (mu : Fin 4) :
    p286GaugeParameterDerivative (sourceFirstModeParameter imaginary omega k) x mu=
      sourceFirstGaugeQuadratureDerivative imaginary omega k x mu • sourceFirstTemporalLie := by
  have smooth : DifferentiableAt ℝ (sourceFirstGaugeQuadrature imaginary omega k) x := by
    have H:=(sourceFirstPhaseLinear omega k).toContinuousLinearMap.hasFDerivAt (x:=x) |>.cexp
    cases imaginary
    · exact (Complex.reCLM.hasFDerivAt.comp x H).neg.differentiableAt
    · exact (Complex.imCLM.hasFDerivAt.comp x H).neg.differentiableAt
  have H:=smooth.hasFDerivAt.smul_const (show P286CoordinateCarrier from sourceFirstTemporalLie)
  change (fderiv ℝ (fun y=>sourceFirstGaugeQuadrature imaginary omega k y •
    (show P286CoordinateCarrier from sourceFirstTemporalLie)) x) (coordinateDirection mu)=_
  rw [H.fderiv]
  simpa using congrArg (fun a : ℝ=>a • sourceFirstTemporalLie)
    (sourceFirstGaugeQuadrature_generated imaginary omega k x mu)

/-- The generated quadrature derivative is consumed by the original connection gauge mouth. -/
theorem sourceFirstModeGauge_connection (imaginary : Bool) (omega : ℝ) (k : PhysicalMomentum)
    (c : StageNineHolonomicConfiguration) (x : BasePoint) (mu : Fin 4) :
    p286CoordinateEquiv ((sourceFirstModeGauge imaginary omega k c).gaugeConnection x mu)=
      p286InfinitesimalGaugeConnectionDirection c (sourceFirstModeParameter imaginary omega k) x mu := by
  rw [p286InfinitesimalGaugeConnectionDirection,sourceFirstModeParameter_derivative]
  simp only [sourceFirstModeGauge,sourceFirstGaugePrimitive,map_sub,map_smul,
    LinearEquiv.apply_symm_apply,nativeGaugeDirection,Pi.zero_apply,sub_zero]
  change _=coordinateBracket (sourceFirstGaugeQuadrature imaginary omega k x • sourceFirstTemporalLie)
    (actualConnection c x mu)-_
  rw [coordinateBracket_smul_left]
  rfl

/-- Recombining gauge variation and its complete remainder returns the original nine-field perturbation. -/
theorem sourceFirstModeRemainder_original (imaginary : Bool) (omega : ℝ) (k : PhysicalMomentum)
    (c : StageNineHolonomicConfiguration) :
    configurationRay (sourceFirstModeGauge imaginary omega k c)
      (sourceFirstModeRemainder imaginary omega k c) 1=sourceFirstModeTangent imaginary omega k := by
  apply StageNineHolonomicConfiguration.ext <;> funext x
  all_goals simp only [configurationRay,sourceFirstModeRemainder,sourceFirstModeGauge,
    one_smul,Pi.zero_apply,zero_add]
  all_goals abel

private theorem mode_gauge (imaginary : Bool) (omega : ℝ) (k : PhysicalMomentum) (x : BasePoint) (mu : Fin 4) :
    fieldGauge (sourceFirstModeField imaginary omega k x) mu=
      ∑a : Fin 4,(-sourceFirstGaugeQuadratureDerivative imaginary omega k x a) • sourceFirstGaugeConnection a mu := by
  simp only [sourceFirstModeField,fieldGauge,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
    Finset.sum_smul,mul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [←Finset.smul_sum,←sourceFirstGauge_generated a mu]
  rfl

/-- The remaining connection is computed: all spatial/transverse differences plus the actual background bracket. -/
theorem sourceFirstModeRemainder_connection (imaginary : Bool) (omega : ℝ) (k : PhysicalMomentum)
    (c : StageNineHolonomicConfiguration) (x : BasePoint) (mu : Fin 4) :
    p286CoordinateEquiv ((sourceFirstModeRemainder imaginary omega k c).gaugeConnection x mu)=
      (∑a : Fin 4,(-sourceFirstGaugeQuadratureDerivative imaginary omega k x a) • sourceFirstGaugeRemainderConnection a mu)-
      sourceFirstGaugeQuadrature imaginary omega k x • lie sourceFirstTemporalLie (actualConnection c x mu) := by
  simp only [sourceFirstModeRemainder,sourceFirstModeTangent,sourceFirstModeGauge,
    sourceFirstGaugePrimitive,map_sub,map_smul,LinearEquiv.apply_symm_apply,
    nativeGaugeDirection,Pi.zero_apply,sub_zero]
  rw [mode_gauge]
  have split (a : Fin 4) : sourceFirstGaugeConnection a mu=
      (if a=mu then sourceFirstTemporalLie else 0)+sourceFirstGaugeRemainderConnection a mu := by
    rw [←sourceFirstGauge_generated]
    exact sourceFirstGaugeConnection_split a mu
  simp_rw [split,smul_add]
  rw [Finset.sum_add_distrib]
  simp only [smul_ite,smul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  module

/-- The scalar supplement is the actual nonzero orbit at the original background. -/
theorem sourceFirstModeRemainder_scalar (imaginary : Bool) (omega : ℝ) (k : PhysicalMomentum) (x : BasePoint) :
    (sourceFirstModeRemainder imaginary omega k actual).scalar x=
      -sourceFirstGaugeQuadrature imaginary omega k x • fieldScalar sourceFirstScalarField := by
  have scalarZero : fieldScalar (sourceFirstModeField imaginary omega k x)=0 := by
    simp only [sourceFirstModeField,fieldScalar,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
      Finset.sum_smul,mul_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro a _
    rw [←Finset.smul_sum]
    change _ • fieldScalar (sourceEnergyAxisField 1 a)=0
    rw [(sourceFirstGauge_sectors a).2.1,smul_zero]
  change fieldScalar (sourceFirstModeField imaginary omega k x)-
    sourceFirstGaugeQuadrature imaginary omega k x • (sourceFirstGaugePrimitive actual).scalar x=_
  rw [scalarZero,sourceFirstGaugePrimitive_scalar,zero_sub,neg_smul]

/-- The actual action-state restriction keeps the background commutator and the physical gauge-parameter gradient separately. -/
theorem sourceFirstModeGauge_state (imaginary : Bool) (omega : ℝ) (k : PhysicalMomentum)
    (c : StageNineHolonomicConfiguration) (x : BasePoint) :
    configurationState (sourceFirstModeGauge imaginary omega k c) x=
      sourceFirstGaugeQuadrature imaginary omega k x • sourceFirstGaugeState (configurationState c x)-
        (0,(fun mu=>sourceFirstGaugeQuadratureDerivative imaginary omega k x mu • nativePrimal sourceFirstTemporalLie),0) := by
  rw [←sourceFirstGaugePrimitive_state]
  apply Prod.ext
  · change 0=_ • (0 : LorentzianCoframe)-0
    simp
  apply Prod.ext
  · funext mu
    change Quantum.operatorMatrix (FullQuantum.connection (sourceFirstModeGauge imaginary omega k c) x mu)=
      sourceFirstGaugeQuadrature imaginary omega k x •
        Quantum.operatorMatrix (FullQuantum.connection (sourceFirstGaugePrimitive c) x mu)-_
    rw [originalConnection_source,originalConnection_source]
    have zeroSpin : PointwiseDiracSpinConnectionLift.diracSpinConnectionLift 0 mu=0 :=
      (PointwiseDiracSpinConnectionLift.diracSpinConnectionLiftLinear mu).map_zero
    simp only [sourceFirstModeGauge,sourceFirstGaugePrimitive,Pi.zero_apply,zeroSpin,map_zero,zero_add,
      map_sub,map_smul,LinearEquiv.apply_symm_apply]
  · change PreparationVacuumGaugeSourceInjection.scalarLinear (_ • (sourceFirstGaugePrimitive c).scalar x)=
      _ • PreparationVacuumGaugeSourceInjection.scalarLinear ((sourceFirstGaugePrimitive c).scalar x)-0
    rw [sub_zero]
    exact (PreparationVacuumGaugeSourceInjection.scalarLinear.restrictScalars ℝ).map_smul _ _

/-- Both original curvature legs consume the actual generated parameter and its derivative. -/
theorem sourceFirstModeGauge_curvature (imaginary : Bool) (omega : ℝ) (k : PhysicalMomentum)
    (c : StageNineHolonomicConfiguration) (f : BasePoint→P286GaugeOneForm) (x : BasePoint) (pair : Fin 6) :
    curvatureSecond (actualForce f x)
      (fun mu=>p286CoordinateEquiv ((sourceFirstModeGauge imaginary omega k c).gaugeConnection x mu)) pair+
      curvatureFirst (actualConnection c x)
        (nativeGaugeContact (sourceFirstGaugeQuadrature imaginary omega k x • sourceFirstTemporalLie) (actualForce f x))
        (nativeGaugeContactDerivative (sourceFirstGaugeQuadrature imaginary omega k x • sourceFirstTemporalLie)
          (fun mu=>sourceFirstGaugeQuadratureDerivative imaginary omega k x mu • sourceFirstTemporalLie)
          (actualForce f x) (actualForceDerivative f x)) pair=
      lie (sourceFirstGaugeQuadrature imaginary omega k x • sourceFirstTemporalLie)
        (curvatureFirst (actualConnection c x) (actualForce f x) (actualForceDerivative f x) pair) := by
  simp_rw [sourceFirstModeGauge_connection,p286InfinitesimalGaugeConnectionDirection,
    sourceFirstModeParameter_derivative]
  exact nativeCurvature_mixed _ _ _ _ _ _

end LowEnergy.PreparationPhysicalFirstPoleGaugeRemainder
