import H0mework.Physics.ConnectionJets.CurrentP286CompleteActionResponseFirstJet
import H0mework.Physics.IdentityHessian.CartanECNormalFixedGlobalMatterDualAdjointAcceptance

/-!
# Fixed KIN-16 matter-dual complete-P286 successor

The fixed P506/L0 matter-dual/full-EC actual has a live identity coframe at
the common contact and zero coframe first jet there, but its global coframe is
not constant.  This module lets the existing current-state P286 action
operator read that actual and generate the complete temporal-plus-radial
auxiliary germ:

```text
fixed matter-dual/full-EC actual
  -> current P286 full action dual
  -> unique BF-Legendre velocity and Gauss charge
  -> complete P286 auxiliary write
  -> one same-lineage successor.
```

The fixed-principal theorem is extended only across the actual zero coframe
first jet.  A proof-only identity-coframe comparison has the same action
target and generated auxiliary germ; a local point--coframe calculation then
shows that both BF momenta have the same origin derivative.  No residual,
target response, coefficient, branch, equation, nondegeneracy receipt, or
stationarity certificate enters the physical constructor.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualP286CompleteActual

open ProofFreeRicherAnholonomicSource
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization
open StageNineBlockwiseConstitutive
open StageNineCoframeFirstJet
open StageNineCoframeLocalDifferentiability
open StageNineCoframeVariation
open StageNineCurrentP286CompleteActionResponseOperator
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualAdjointAcceptance
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicIdentityCoframeConjugateMatterActionAcceptance
open StageNineP286ActionCauchySplit
open StageNineP286GaugeAuxiliaryEquation
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionMomentumRegularity
open StageNineP286GaugeConnectionPointwiseEquation
open StageNineP286GaugeConnectionVariation
open SU7MotherGaugeTheory
open SU7MotherLieAlgebra

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

local instance fixedP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance fixedP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance fixedP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

private abbrev FixedMatterDualCurrent : StageNineHolonomicConfiguration :=
  positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual

/-- The current-action complete P286 write on the fixed matter-dual/EC
successor.  Its only inputs are the proof-free source and that generated
current actual. -/
def positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualP286CompleteActual :
    StageNineHolonomicConfiguration :=
  currentP286CompleteActionResponseOperator positiveSmoothUnifiedSource
    FixedMatterDualCurrent

private def fixedMatterDualIdentityCoframeCurrent :
    StageNineHolonomicConfiguration :=
  identityCoframeComparison FixedMatterDualCurrent

private abbrev FixedMatterDualIdentityCoframeP286Output :
    StageNineHolonomicConfiguration :=
  currentP286CompleteActionResponseOperator positiveSmoothUnifiedSource
    fixedMatterDualIdentityCoframeCurrent

/-! ## Proof-only fixed-principal comparison -/

private theorem fixedMatterDualIdentityCoframe_fullActionTarget :
    currentP286FullActionTarget positiveSmoothUnifiedSource
        fixedMatterDualIdentityCoframeCurrent =
      currentP286FullActionTarget positiveSmoothUnifiedSource
        FixedMatterDualCurrent := by
  apply LinearMap.ext
  intro direction
  change
    p286GaugeConnectionAlgebraicCurrentCoefficient
        positiveSmoothUnifiedSource fixedMatterDualIdentityCoframeCurrent
          direction 0 =
      p286GaugeConnectionAlgebraicCurrentCoefficient
        positiveSmoothUnifiedSource FixedMatterDualCurrent direction 0
  apply
    p286GaugeConnectionAlgebraicCurrentCoefficient_eq_of_contact
      positiveSmoothUnifiedSource
      fixedMatterDualIdentityCoframeCurrent FixedMatterDualCurrent 0
  · change (1 : LorentzianCoframe) = FixedMatterDualCurrent.coframe 0
    exact fixedGlobalMatterDualFullCauchy_coframe_origin.symm
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

private theorem fixedMatterDualIdentityCoframe_spatialActionTarget :
    currentP286SpatialActionTarget positiveSmoothUnifiedSource
        fixedMatterDualIdentityCoframeCurrent =
      currentP286SpatialActionTarget positiveSmoothUnifiedSource
        FixedMatterDualCurrent := by
  unfold currentP286SpatialActionTarget
  rw [fixedMatterDualIdentityCoframe_fullActionTarget]

private theorem fixedMatterDualIdentityCoframe_temporalActionTarget :
    currentP286TemporalActionTarget positiveSmoothUnifiedSource
        fixedMatterDualIdentityCoframeCurrent =
      currentP286TemporalActionTarget positiveSmoothUnifiedSource
        FixedMatterDualCurrent := by
  unfold currentP286TemporalActionTarget
  rw [fixedMatterDualIdentityCoframe_fullActionTarget]

private theorem fixedMatterDualIdentityCoframe_spatialVelocity :
    currentP286SpatialAuxiliaryVelocity positiveSmoothUnifiedSource
        fixedMatterDualIdentityCoframeCurrent =
      currentP286SpatialAuxiliaryVelocity positiveSmoothUnifiedSource
        FixedMatterDualCurrent := by
  unfold currentP286SpatialAuxiliaryVelocity
  rw [fixedMatterDualIdentityCoframe_spatialActionTarget]

private theorem fixedMatterDualIdentityCoframe_gaussCharge :
    currentP286GaussCharge positiveSmoothUnifiedSource
        fixedMatterDualIdentityCoframeCurrent =
      currentP286GaussCharge positiveSmoothUnifiedSource
        FixedMatterDualCurrent := by
  unfold currentP286GaussCharge
  rw [fixedMatterDualIdentityCoframe_temporalActionTarget]

private theorem
    fixedMatterDualIdentityCoframe_completeAuxiliaryCoordinate :
    currentP286CompleteResponseAuxiliaryCoordinate
        positiveSmoothUnifiedSource fixedMatterDualIdentityCoframeCurrent =
      currentP286CompleteResponseAuxiliaryCoordinate
        positiveSmoothUnifiedSource FixedMatterDualCurrent := by
  funext point
  unfold currentP286CompleteResponseAuxiliaryCoordinate
    currentP286OriginAuxiliaryCoordinate
  rw [fixedMatterDualIdentityCoframe_spatialVelocity,
    fixedMatterDualIdentityCoframe_gaussCharge]
  rfl

private theorem fixedMatterDualIdentityCoframe_operator_commutes :
    FixedMatterDualIdentityCoframeP286Output =
      identityCoframeComparison
        positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualP286CompleteActual := by
  apply StageNineHolonomicConfiguration.ext
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · funext point pair
    change
      p286CoordinateEquiv.symm
          (currentP286CompleteResponseAuxiliaryCoordinate
            positiveSmoothUnifiedSource
            fixedMatterDualIdentityCoframeCurrent point pair) =
        p286CoordinateEquiv.symm
          (currentP286CompleteResponseAuxiliaryCoordinate
            positiveSmoothUnifiedSource FixedMatterDualCurrent point pair)
    rw [fixedMatterDualIdentityCoframe_completeAuxiliaryCoordinate]
  · rfl
  · rfl
  · rfl

/-! ## Local coframe--auxiliary momentum calculus -/

def fixedP286BFMomentumCoframeAuxiliary
    (direction : P286GaugeTwoForm)
    (joint : LorentzianCoframe × P286GaugeTwoForm) : ℝ :=
  abs (Matrix.det joint.1) *
    p286GaugeAuxiliaryHodgePairingPolynomial joint.1 joint.2 direction

private theorem liftCoframeTwoFormLinear_joint_contDiff
    (form :
      LorentzianCoframe × P286GaugeTwoForm → P286GaugeTwoForm)
    (formSmooth : ContDiff ℝ ∞ form) :
    ContDiff ℝ ∞ fun joint =>
      liftGaugeTwoFormOperator
        (coframeTwoFormLinear joint.1) (form joint) := by
  apply contDiff_pi'
  intro output
  unfold liftGaugeTwoFormOperator
  apply ContDiff.sum
  intro input _
  have coefficientSmooth :
      ContDiff ℝ ∞ fun joint :
        LorentzianCoframe × P286GaugeTwoForm =>
          gaugeOperatorCoefficient
            (coframeTwoFormLinear joint.1) output input := by
    have wedgeSmooth :
        ContDiff ℝ ∞ fun joint :
          LorentzianCoframe × P286GaugeTwoForm =>
            coframeWedge joint.1 output input := by
      unfold coframeWedge
      fun_prop
    simpa [gaugeOperatorCoefficient, coframeTwoFormLinear] using
      wedgeSmooth
  exact coefficientSmooth.smul (contDiff_pi.mp formSmooth input)

private theorem liftFixedGaugeTwoFormOperator_joint_contDiff
    (operator : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm)
    (form :
      LorentzianCoframe × P286GaugeTwoForm → P286GaugeTwoForm)
    (formSmooth : ContDiff ℝ ∞ form) :
    ContDiff ℝ ∞ fun joint =>
      liftGaugeTwoFormOperator operator (form joint) := by
  apply contDiff_pi'
  intro output
  unfold liftGaugeTwoFormOperator
  apply ContDiff.sum
  intro input _
  exact
    (contDiff_const :
      ContDiff ℝ ∞ fun _ :
        LorentzianCoframe × P286GaugeTwoForm =>
          gaugeOperatorCoefficient operator output input).smul
      (contDiff_pi.mp formSmooth input)

private theorem fixedP286BFMomentumCoframeAuxiliary_contDiffAt
    (direction initialAuxiliary : P286GaugeTwoForm) :
    ContDiffAt ℝ ∞
      (fixedP286BFMomentumCoframeAuxiliary direction)
      ((1 : LorentzianCoframe), initialAuxiliary) := by
  have auxiliaryTransformSmooth :
      ContDiff ℝ ∞ fun joint :
        LorentzianCoframe × P286GaugeTwoForm =>
          liftGaugeTwoFormOperator
            (coframeTwoFormLinear joint.1) joint.2 :=
    liftCoframeTwoFormLinear_joint_contDiff
      (fun joint : LorentzianCoframe × P286GaugeTwoForm => joint.2)
      contDiff_snd
  have directionTransformSmooth :
      ContDiff ℝ ∞ fun joint :
        LorentzianCoframe × P286GaugeTwoForm =>
          liftGaugeTwoFormOperator
            (coframeTwoFormLinear joint.1) direction :=
    liftCoframeTwoFormLinear_joint_contDiff
      (fun _ : LorentzianCoframe × P286GaugeTwoForm => direction)
      contDiff_const
  have hodgeDirectionTransformSmooth :
      ContDiff ℝ ∞ fun joint :
        LorentzianCoframe × P286GaugeTwoForm =>
          liftGaugeTwoFormOperator lorentzianCoframeHodge
            (liftGaugeTwoFormOperator
              (coframeTwoFormLinear joint.1) direction) :=
    liftFixedGaugeTwoFormOperator_joint_contDiff lorentzianCoframeHodge
      (fun joint : LorentzianCoframe × P286GaugeTwoForm =>
        liftGaugeTwoFormOperator
          (coframeTwoFormLinear joint.1) direction)
      directionTransformSmooth
  have pairingSmooth :
      ContDiff ℝ ∞ fun joint :
        LorentzianCoframe × P286GaugeTwoForm =>
          p286GaugeAuxiliaryHodgePairingPolynomial joint.1 joint.2
            direction := by
    unfold p286GaugeAuxiliaryHodgePairingPolynomial
    apply ContDiff.sum
    intro pair _
    apply contDiff_const.mul
    exact
      (p286CoordinateLiePairingBilinear.toContinuousBilinearMap.contDiff.comp
        (contDiff_pi.mp auxiliaryTransformSmooth pair)).clm_apply
        (contDiff_pi.mp hodgeDirectionTransformSmooth pair)
  have volumeSmooth :
      ContDiffAt ℝ ∞
        (fun joint : LorentzianCoframe × P286GaugeTwoForm =>
          abs (Matrix.det joint.1))
        ((1 : LorentzianCoframe), initialAuxiliary) :=
    (coframe_volume_contDiffAt (1 : LorentzianCoframe) (by norm_num)).comp
      ((1 : LorentzianCoframe), initialAuxiliary) contDiffAt_fst
  exact volumeSmooth.mul pairingSmooth.contDiffAt

/-! ## Same-actual BF-momentum first jet -/

private abbrev FixedP286Output : StageNineHolonomicConfiguration :=
  positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualP286CompleteActual

theorem fixedGlobalMatterDualP286Complete_smooth :
    FixedP286Output.Smooth :=
  currentP286CompleteActionResponseOperator_smooth
    positiveSmoothUnifiedSource FixedMatterDualCurrent
    fixedGlobalMatterDualFullCauchy_smooth

@[simp] theorem fixedGlobalMatterDualP286Complete_coframe :
    FixedP286Output.coframe = FixedMatterDualCurrent.coframe :=
  currentP286CompleteActionResponseOperator_coframe
    positiveSmoothUnifiedSource FixedMatterDualCurrent

theorem fixedGlobalMatterDualP286Complete_coframe_origin :
    FixedP286Output.coframe 0 = 1 := by
  rw [fixedGlobalMatterDualP286Complete_coframe,
    fixedGlobalMatterDualFullCauchy_coframe_origin]

theorem
    fixedGlobalMatterDualP286Complete_coframeCoordinateAxis_hasDerivAt_zero
    (direction : LorentzianIndex) :
    HasDerivAt
      (fun parameter : ℝ =>
        FixedP286Output.coframe
          (parameter • coordinateDirection direction))
      0 0 := by
  simpa only [fixedGlobalMatterDualP286Complete_coframe] using
    fixedGlobalMatterDualFullCauchy_coframeCoordinateAxis_hasDerivAt_zero
      direction

private def fixedGlobalMatterDualP286CoordinateAxis
    (direction : LorentzianIndex) : ℝ → BasePoint :=
  fun parameter => parameter • coordinateDirection direction

private theorem fixedGlobalMatterDualP286CoordinateAxis_hasDerivAt
    (direction : LorentzianIndex) :
    HasDerivAt (fixedGlobalMatterDualP286CoordinateAxis direction)
      (coordinateDirection direction) 0 := by
  let line :=
    fun parameter : ℝ =>
      parameter • coordinateDirection direction
  change HasDerivAt line (coordinateDirection direction) 0
  simpa [line] using
    (hasDerivAt_id (𝕜 := ℝ) 0).smul_const
      (coordinateDirection direction)

private def fixedGlobalMatterDualP286AuxiliaryCoordinate :
    BasePoint → P286GaugeTwoForm :=
  holonomicP286GaugeAuxiliaryCoordinate FixedP286Output

private theorem fixedGlobalMatterDualP286AuxiliaryCoordinate_contDiff :
    ContDiff ℝ ∞ fixedGlobalMatterDualP286AuxiliaryCoordinate :=
  holonomicP286GaugeAuxiliaryCoordinate_contDiff FixedP286Output
    fixedGlobalMatterDualP286Complete_smooth

private theorem
    fixedGlobalMatterDualP286AuxiliaryCoordinateAxis_hasDerivAt
    (direction : LorentzianIndex) :
    HasDerivAt
      (fun parameter =>
        fixedGlobalMatterDualP286AuxiliaryCoordinate
          (fixedGlobalMatterDualP286CoordinateAxis direction parameter))
      ((fderiv ℝ fixedGlobalMatterDualP286AuxiliaryCoordinate 0)
        (coordinateDirection direction))
      0 := by
  have auxiliaryDifferentiable :
      DifferentiableAt ℝ fixedGlobalMatterDualP286AuxiliaryCoordinate 0 :=
    (fixedGlobalMatterDualP286AuxiliaryCoordinate_contDiff.differentiable
      (by simp)).differentiableAt
  have auxiliaryOuter :
      HasFDerivAt fixedGlobalMatterDualP286AuxiliaryCoordinate
        (fderiv ℝ fixedGlobalMatterDualP286AuxiliaryCoordinate 0)
        (fixedGlobalMatterDualP286CoordinateAxis direction 0) := by
    simpa [fixedGlobalMatterDualP286CoordinateAxis] using
      auxiliaryDifferentiable.hasFDerivAt
  exact
    auxiliaryOuter.comp_hasDerivAt 0
      (fixedGlobalMatterDualP286CoordinateAxis_hasDerivAt direction)

private def fixedGlobalMatterDualP286ActualCoframeAuxiliaryAxis
    (direction : LorentzianIndex) :
    ℝ → LorentzianCoframe × P286GaugeTwoForm :=
  fun parameter =>
    let point :=
      fixedGlobalMatterDualP286CoordinateAxis direction parameter
    (FixedP286Output.coframe point,
      fixedGlobalMatterDualP286AuxiliaryCoordinate point)

private def fixedGlobalMatterDualP286FrozenCoframeAuxiliaryAxis
    (direction : LorentzianIndex) :
    ℝ → LorentzianCoframe × P286GaugeTwoForm :=
  fun parameter =>
    let point :=
      fixedGlobalMatterDualP286CoordinateAxis direction parameter
    ((1 : LorentzianCoframe),
      fixedGlobalMatterDualP286AuxiliaryCoordinate point)

private theorem
    fixedGlobalMatterDualP286ActualCoframeAuxiliaryAxis_hasDerivAt
    (direction : LorentzianIndex) :
    HasDerivAt
      (fixedGlobalMatterDualP286ActualCoframeAuxiliaryAxis direction)
      (0,
        (fderiv ℝ fixedGlobalMatterDualP286AuxiliaryCoordinate 0)
          (coordinateDirection direction))
      0 := by
  exact
    (fixedGlobalMatterDualP286Complete_coframeCoordinateAxis_hasDerivAt_zero
      direction).prodMk
      (fixedGlobalMatterDualP286AuxiliaryCoordinateAxis_hasDerivAt direction)

private theorem
    fixedGlobalMatterDualP286FrozenCoframeAuxiliaryAxis_hasDerivAt
    (direction : LorentzianIndex) :
    HasDerivAt
      (fixedGlobalMatterDualP286FrozenCoframeAuxiliaryAxis direction)
      (0,
        (fderiv ℝ fixedGlobalMatterDualP286AuxiliaryCoordinate 0)
          (coordinateDirection direction))
      0 := by
  exact
    (hasDerivAt_const (x := (0 : ℝ))
      (c := (1 : LorentzianCoframe))).prodMk
      (fixedGlobalMatterDualP286AuxiliaryCoordinateAxis_hasDerivAt direction)

private theorem fixedGlobalMatterDualP286_momentum_eq_actualSection
    (direction : P286GaugeTwoForm) :
    p286GaugeConnectionBFDifferentialMomentum FixedP286Output direction =
      fixedP286BFMomentumCoframeAuxiliary direction ∘
        fun point =>
          (FixedP286Output.coframe point,
            fixedGlobalMatterDualP286AuxiliaryCoordinate point) := by
  funext point
  rfl

private theorem fixedGlobalMatterDualP286_momentum_eq_frozenSection
    (direction : P286GaugeTwoForm) :
    p286GaugeConnectionBFDifferentialMomentum
        (identityCoframeComparison FixedP286Output) direction =
      fixedP286BFMomentumCoframeAuxiliary direction ∘
        fun point =>
          ((1 : LorentzianCoframe),
            fixedGlobalMatterDualP286AuxiliaryCoordinate point) := by
  funext point
  rfl

theorem
    fixedGlobalMatterDualP286Complete_bfMomentumDerivative_eq_identityComparison
    (direction : P286GaugeTwoForm)
    (derivativeDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (p286GaugeConnectionBFDifferentialMomentum FixedP286Output direction)
        0 derivativeDirection =
      fieldDirectionalDerivative
        (p286GaugeConnectionBFDifferentialMomentum
          (identityCoframeComparison FixedP286Output) direction)
        0 derivativeDirection := by
  let outer :=
    fixedP286BFMomentumCoframeAuxiliary direction
  let auxiliaryOrigin :=
    fixedGlobalMatterDualP286AuxiliaryCoordinate 0
  have outerDifferentiable :
      DifferentiableAt ℝ outer ((1 : LorentzianCoframe), auxiliaryOrigin) :=
    (fixedP286BFMomentumCoframeAuxiliary_contDiffAt direction auxiliaryOrigin)
      |>.differentiableAt (by simp)
  have outerDerivative :=
    outerDifferentiable.hasFDerivAt
  have actualAxisOrigin :
      fixedGlobalMatterDualP286ActualCoframeAuxiliaryAxis
          derivativeDirection 0 =
        ((1 : LorentzianCoframe), auxiliaryOrigin) := by
    simp [fixedGlobalMatterDualP286ActualCoframeAuxiliaryAxis,
      fixedGlobalMatterDualP286CoordinateAxis, auxiliaryOrigin,
      fixedGlobalMatterDualP286Complete_coframe_origin]
  have outerAtActual :
      HasFDerivAt outer
        (fderiv ℝ outer ((1 : LorentzianCoframe), auxiliaryOrigin))
        (fixedGlobalMatterDualP286ActualCoframeAuxiliaryAxis
          derivativeDirection 0) := by
    simpa only [actualAxisOrigin] using outerDerivative
  have generatedActualAxis :=
    outerAtActual.comp_hasDerivAt 0
      (fixedGlobalMatterDualP286ActualCoframeAuxiliaryAxis_hasDerivAt
        derivativeDirection)
  have frozenAxisOrigin :
      fixedGlobalMatterDualP286FrozenCoframeAuxiliaryAxis
          derivativeDirection 0 =
        ((1 : LorentzianCoframe), auxiliaryOrigin) := by
    simp [fixedGlobalMatterDualP286FrozenCoframeAuxiliaryAxis,
      fixedGlobalMatterDualP286CoordinateAxis, auxiliaryOrigin]
  have outerAtFrozen :
      HasFDerivAt outer
        (fderiv ℝ outer ((1 : LorentzianCoframe), auxiliaryOrigin))
        (fixedGlobalMatterDualP286FrozenCoframeAuxiliaryAxis
          derivativeDirection 0) := by
    simpa only [frozenAxisOrigin] using outerDerivative
  have generatedFrozenAxis :=
    outerAtFrozen.comp_hasDerivAt 0
      (fixedGlobalMatterDualP286FrozenCoframeAuxiliaryAxis_hasDerivAt
        derivativeDirection)
  have coframeDifferentiable :
      DifferentiableAt ℝ FixedP286Output.coframe 0 :=
    ((holonomicCoframe_contDiff FixedP286Output
      fixedGlobalMatterDualP286Complete_smooth).differentiable (by simp))
      |>.differentiableAt
  have auxiliaryDifferentiable :
      DifferentiableAt ℝ fixedGlobalMatterDualP286AuxiliaryCoordinate 0 :=
    (fixedGlobalMatterDualP286AuxiliaryCoordinate_contDiff.differentiable
      (by simp)).differentiableAt
  have actualSectionDifferentiable :
      DifferentiableAt ℝ
        (fun point =>
          (FixedP286Output.coframe point,
            fixedGlobalMatterDualP286AuxiliaryCoordinate point))
        0 :=
    coframeDifferentiable.prodMk auxiliaryDifferentiable
  have frozenSectionDifferentiable :
      DifferentiableAt ℝ
        (fun point =>
          ((1 : LorentzianCoframe),
            fixedGlobalMatterDualP286AuxiliaryCoordinate point))
        0 :=
    (differentiableAt_const (c := (1 : LorentzianCoframe))).prodMk
      auxiliaryDifferentiable
  have actualMomentumDifferentiable :
      DifferentiableAt ℝ
        (p286GaugeConnectionBFDifferentialMomentum FixedP286Output direction)
        0 := by
    rw [fixedGlobalMatterDualP286_momentum_eq_actualSection]
    have outerAtSection :
        DifferentiableAt ℝ outer
          (FixedP286Output.coframe 0,
            fixedGlobalMatterDualP286AuxiliaryCoordinate 0) := by
      simpa only [fixedGlobalMatterDualP286Complete_coframe_origin,
        auxiliaryOrigin] using outerDifferentiable
    exact outerAtSection.comp 0 actualSectionDifferentiable
  have frozenMomentumDifferentiable :
      DifferentiableAt ℝ
        (p286GaugeConnectionBFDifferentialMomentum
          (identityCoframeComparison FixedP286Output) direction)
        0 := by
    rw [fixedGlobalMatterDualP286_momentum_eq_frozenSection]
    exact outerDifferentiable.comp 0 frozenSectionDifferentiable
  have actualMomentumOuter :
      HasFDerivAt
        (p286GaugeConnectionBFDifferentialMomentum FixedP286Output direction)
        (fderiv ℝ
          (p286GaugeConnectionBFDifferentialMomentum FixedP286Output direction)
          0)
        (fixedGlobalMatterDualP286CoordinateAxis derivativeDirection 0) := by
    simpa [fixedGlobalMatterDualP286CoordinateAxis] using
      actualMomentumDifferentiable.hasFDerivAt
  have actualCoordinateDerivative :=
    actualMomentumOuter.comp_hasDerivAt 0
      (fixedGlobalMatterDualP286CoordinateAxis_hasDerivAt
        derivativeDirection)
  have frozenMomentumOuter :
      HasFDerivAt
        (p286GaugeConnectionBFDifferentialMomentum
          (identityCoframeComparison FixedP286Output) direction)
        (fderiv ℝ
          (p286GaugeConnectionBFDifferentialMomentum
            (identityCoframeComparison FixedP286Output) direction) 0)
        (fixedGlobalMatterDualP286CoordinateAxis derivativeDirection 0) := by
    simpa [fixedGlobalMatterDualP286CoordinateAxis] using
      frozenMomentumDifferentiable.hasFDerivAt
  have frozenCoordinateDerivative :=
    frozenMomentumOuter.comp_hasDerivAt 0
      (fixedGlobalMatterDualP286CoordinateAxis_hasDerivAt
        derivativeDirection)
  have actualAxisFunctionEquality :
      (p286GaugeConnectionBFDifferentialMomentum FixedP286Output direction) ∘
          fixedGlobalMatterDualP286CoordinateAxis derivativeDirection =
        outer ∘
          fixedGlobalMatterDualP286ActualCoframeAuxiliaryAxis
            derivativeDirection := by
    funext parameter
    have read :=
      congrFun
        (fixedGlobalMatterDualP286_momentum_eq_actualSection direction)
        (fixedGlobalMatterDualP286CoordinateAxis
          derivativeDirection parameter)
    simpa only [Function.comp_apply, outer,
      fixedGlobalMatterDualP286ActualCoframeAuxiliaryAxis] using read
  have frozenAxisFunctionEquality :
      (p286GaugeConnectionBFDifferentialMomentum
          (identityCoframeComparison FixedP286Output) direction) ∘
          fixedGlobalMatterDualP286CoordinateAxis derivativeDirection =
        outer ∘
          fixedGlobalMatterDualP286FrozenCoframeAuxiliaryAxis
            derivativeDirection := by
    funext parameter
    have read :=
      congrFun
        (fixedGlobalMatterDualP286_momentum_eq_frozenSection direction)
        (fixedGlobalMatterDualP286CoordinateAxis
          derivativeDirection parameter)
    simpa only [Function.comp_apply, outer,
      fixedGlobalMatterDualP286FrozenCoframeAuxiliaryAxis] using read
  have actualCoordinateDerivative' :
      HasDerivAt
        (outer ∘
          fixedGlobalMatterDualP286ActualCoframeAuxiliaryAxis
            derivativeDirection)
        (fieldDirectionalDerivative
          (p286GaugeConnectionBFDifferentialMomentum
            FixedP286Output direction)
          0 derivativeDirection)
        0 := by
    rw [← actualAxisFunctionEquality]
    exact actualCoordinateDerivative
  have frozenCoordinateDerivative' :
      HasDerivAt
        (outer ∘
          fixedGlobalMatterDualP286FrozenCoframeAuxiliaryAxis
            derivativeDirection)
        (fieldDirectionalDerivative
          (p286GaugeConnectionBFDifferentialMomentum
            (identityCoframeComparison FixedP286Output) direction)
          0 derivativeDirection)
        0 := by
    rw [← frozenAxisFunctionEquality]
    exact frozenCoordinateDerivative
  exact
    (actualCoordinateDerivative'.unique generatedActualAxis).trans
      (frozenCoordinateDerivative'.unique generatedFrozenAxis).symm

theorem
    fixedGlobalMatterDualP286Complete_temporalBFMomentumResponse
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionTemporalBFMomentumDerivative FixedP286Output
        direction 0 =
      currentP286SpatialActionTarget positiveSmoothUnifiedSource
        FixedMatterDualCurrent (fun index => direction index.succ) := by
  calc
    _ =
        p286GaugeConnectionTemporalBFMomentumDerivative
          (identityCoframeComparison FixedP286Output) direction 0 := by
      unfold p286GaugeConnectionTemporalBFMomentumDerivative
      exact
        fixedGlobalMatterDualP286Complete_bfMomentumDerivative_eq_identityComparison
          (p286GaugeExteriorDerivativeDirection
            canonicalLorentzianTimeDirection direction)
          canonicalLorentzianTimeDirection
    _ =
        p286GaugeConnectionTemporalBFMomentumDerivative
          FixedMatterDualIdentityCoframeP286Output direction 0 := by
      rw [fixedMatterDualIdentityCoframe_operator_commutes]
    _ = _ := by
      simpa only [fixedMatterDualIdentityCoframe_spatialActionTarget] using
        currentP286CompleteActionResponseOperator_temporalBFMomentumResponse
          positiveSmoothUnifiedSource fixedMatterDualIdentityCoframeCurrent
          (by
            intro point
            rfl)
          direction

theorem
    fixedGlobalMatterDualP286Complete_spatialBFMomentumResponse
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionSpatialBFMomentumDivergence FixedP286Output
        direction 0 =
      currentP286TemporalActionTarget positiveSmoothUnifiedSource
        FixedMatterDualCurrent
          (direction canonicalLorentzianTimeDirection) := by
  calc
    _ =
        p286GaugeConnectionSpatialBFMomentumDivergence
          (identityCoframeComparison FixedP286Output) direction 0 := by
      unfold p286GaugeConnectionSpatialBFMomentumDivergence
      rw [
        fixedGlobalMatterDualP286Complete_bfMomentumDerivative_eq_identityComparison,
        fixedGlobalMatterDualP286Complete_bfMomentumDerivative_eq_identityComparison,
        fixedGlobalMatterDualP286Complete_bfMomentumDerivative_eq_identityComparison]
    _ =
        p286GaugeConnectionSpatialBFMomentumDivergence
          FixedMatterDualIdentityCoframeP286Output direction 0 := by
      rw [fixedMatterDualIdentityCoframe_operator_commutes]
    _ = _ := by
      simpa only [fixedMatterDualIdentityCoframe_temporalActionTarget] using
        currentP286CompleteActionResponseOperator_spatialBFMomentumResponse
          positiveSmoothUnifiedSource fixedMatterDualIdentityCoframeCurrent
          (by
            intro point
            rfl)
          direction

/-- The action-generated complete P286 auxiliary first jet closes the
connection equation on the new fixed successor.  This is substitution into
the same current action dual that generated the velocity and charge, hence
producer soundness rather than an independent constraint. -/
theorem fixedGlobalMatterDualP286Complete_connectionEquation_origin
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionEulerLagrangeCoefficient
        positiveSmoothUnifiedSource FixedP286Output direction 0 =
      0 := by
  have temporalResponse :=
    fixedGlobalMatterDualP286Complete_temporalBFMomentumResponse direction
  change
    p286GaugeConnectionTemporalBFMomentumDerivative
        (currentP286CompleteActionResponseOperator
          positiveSmoothUnifiedSource FixedMatterDualCurrent)
        direction 0 =
      currentP286SpatialActionTarget positiveSmoothUnifiedSource
        FixedMatterDualCurrent (fun index => direction index.succ)
    at temporalResponse
  have spatialResponse :=
    fixedGlobalMatterDualP286Complete_spatialBFMomentumResponse direction
  change
    p286GaugeConnectionSpatialBFMomentumDivergence
        (currentP286CompleteActionResponseOperator
          positiveSmoothUnifiedSource FixedMatterDualCurrent)
        direction 0 =
      currentP286TemporalActionTarget positiveSmoothUnifiedSource
        FixedMatterDualCurrent
          (direction canonicalLorentzianTimeDirection)
    at spatialResponse
  unfold p286GaugeConnectionEulerLagrangeCoefficient
  change
    p286GaugeConnectionAlgebraicCurrentCoefficient
          positiveSmoothUnifiedSource
          (currentP286CompleteActionResponseOperator
            positiveSmoothUnifiedSource FixedMatterDualCurrent)
          direction 0 -
        p286GaugeConnectionBFDifferentialMomentumDivergence
          (currentP286CompleteActionResponseOperator
            positiveSmoothUnifiedSource FixedMatterDualCurrent)
          direction 0 =
      0
  rw [
    currentP286CompleteActionResponseOperator_actionCurrent_origin,
    p286GaugeConnectionBFDifferentialMomentumDivergence_eq_temporal_add_spatial,
    temporalResponse,
    spatialResponse,
    currentP286FullActionTarget_decomposition]
  ring

theorem fixedGlobalMatterDualP286Complete_coframeFirstJet_origin :
    holonomicCoframeFirstJetAt FixedP286Output.coframe 0 =
      ({ coframe := 1, derivative := 0 } :
        PointwiseLorentzianCoframeJet) := by
  rw [fixedGlobalMatterDualP286Complete_coframe]
  exact fixedGlobalMatterDualFullCauchy_coframeFirstJet_origin

/-- Fixed no-premise synchronization checkpoint for the next action-owned
successor.  The exact source lineage is unchanged, the current-state P286
write is smooth and origin faithful, and its complete connection equation is
read on that same generated output. -/
theorem fixedGlobalMatterDualP286Complete_realizes :
    positiveSmoothUnifiedSource.stageEight.generatedP506L0Lineage =
        canonicalP506SourceAffineL0ObservableLineageReference ∧
      FixedP286Output.Smooth ∧
      holonomicCoframeFirstJetAt FixedP286Output.coframe 0 =
        ({ coframe := 1, derivative := 0 } :
          PointwiseLorentzianCoframeJet) ∧
      toContinuumPointField FixedP286Output 0 =
        toContinuumPointField FixedMatterDualCurrent 0 ∧
      ∀ direction : P286GaugeOneForm,
        p286GaugeConnectionEulerLagrangeCoefficient
            positiveSmoothUnifiedSource FixedP286Output direction 0 =
          0 := by
  exact
    ⟨positiveSmoothUnifiedSource_generates_exactP506L0Lineage,
      fixedGlobalMatterDualP286Complete_smooth,
      fixedGlobalMatterDualP286Complete_coframeFirstJet_origin,
      currentP286CompleteActionResponseOperator_pointField_origin
        positiveSmoothUnifiedSource FixedMatterDualCurrent,
      fixedGlobalMatterDualP286Complete_connectionEquation_origin⟩

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualP286CompleteActual
