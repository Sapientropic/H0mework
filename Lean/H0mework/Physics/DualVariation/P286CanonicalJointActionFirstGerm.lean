import H0mework.Physics.DualVariation.P286CanonicalJointActionProducerSoundness
import H0mework.Physics.Coframe.CoframeLocalDifferentiability
import H0mework.Physics.Coframe.CoframeScalarMatterRegularity
import H0mework.Physics.Coframe.CoframeVariation
import H0mework.Physics.DualVariation.ScalarVariation
import H0mework.Physics.Matter.MatterPointwiseEquation
import H0mework.Physics.GaugeAction.P286GaugeConnectionActionVariation
import H0mework.Physics.GaugeAction.P286GaugeConnectionVariationDensity
import H0mework.Physics.Geometry.ScalarPointwiseEquation
import H0mework.Physics.Coframe.ScalarMomentumCoframeReadout

/-!
# Canonical P286 joint-action first-germ transport

A canonical P286 principal changes a connection by a homogeneous quadratic
field and then recomputes the live constitutive auxiliary.  For every smooth
identity-coframe current, this preserves the scalar differential-momentum
first germ at the contact.  Matter differential momentum is preserved as a
whole field because its primitive coframe and adjoint-matter inputs are
unchanged.

The statements are uniform in the incoming current and in the action write.
They are transport theorems for an already supplied write; they neither
select that write nor consume a residual, support coordinate, target jet, or
equation receipt.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeP286CanonicalJointActionFirstGerm

open ProofFreeRicherAnholonomicSource
open StageNineCoframeHolonomicRegularity
open StageNineCoframeLocalDifferentiability
open StageNineCoframeVariation
open StageNineDiracDualFormNativeP286CanonicalJointActionProducerCore
open StageNineDynamicBreakingVacuum
open StageNineDiracDualFormNativeScalarVariation
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineMatterPointwiseEquation
open StageNineP286CanonicalDiagonalActionPrincipal
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineP286HolonomicSecondJetCarrier
open StageNineScalarPointwiseEquation
open StageNineScalarMomentumCoframeReadout
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000

open scoped ContDiff Matrix.Norms.Elementwise

local instance canonicalFirstGermP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance canonicalFirstGermP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance canonicalFirstGermP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

private abbrev Candidate
    (current : StageNineHolonomicConfiguration)
    (write : P286GaugeOneForm) : StageNineHolonomicConfiguration :=
  diracDualFormNativeP286CanonicalJointCandidate positiveSmoothUnifiedSource
    current write

@[simp] private theorem candidate_coframe
    (current : StageNineHolonomicConfiguration)
    (write : P286GaugeOneForm) :
    (Candidate current write).coframe = current.coframe :=
  rfl

@[simp] private theorem candidate_scalar
    (current : StageNineHolonomicConfiguration)
    (write : P286GaugeOneForm) :
    (Candidate current write).scalar = current.scalar :=
  rfl

@[simp] private theorem candidate_conjugateMatter
    (current : StageNineHolonomicConfiguration)
    (write : P286GaugeOneForm) :
    (Candidate current write).conjugateMatter = current.conjugateMatter :=
  rfl

/-! ## Local derivative calculus -/

private theorem fieldDirectionalDerivative_const_mul
    (field : BasePoint → ℝ)
    (fieldDifferentiable : DifferentiableAt ℝ field 0)
    (scalar : ℝ) (direction : LorentzianIndex) :
    fieldDirectionalDerivative (fun point => scalar * field point) 0 direction =
      scalar * fieldDirectionalDerivative field 0 direction := by
  unfold fieldDirectionalDerivative
  rw [fderiv_const_mul fieldDifferentiable scalar]
  rfl

private theorem fieldDirectionalDerivative_add
    (first second : BasePoint → ℝ)
    (firstDifferentiable : DifferentiableAt ℝ first 0)
    (secondDifferentiable : DifferentiableAt ℝ second 0)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative (fun point => first point + second point)
        0 direction =
      fieldDirectionalDerivative first 0 direction +
        fieldDirectionalDerivative second 0 direction := by
  unfold fieldDirectionalDerivative
  rw [fderiv_fun_add firstDifferentiable secondDifferentiable]
  rfl

private theorem fieldDirectionalDerivative_sum
    {Index : Type*} [Fintype Index]
    (field : Index → BasePoint → ℝ)
    (fieldDifferentiable : ∀ index, DifferentiableAt ℝ (field index) 0)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative (fun point => ∑ index, field index point)
        0 direction =
      ∑ index, fieldDirectionalDerivative (field index) 0 direction := by
  have sumDerivative :
      HasFDerivAt
        (∑ index, field index)
        (∑ index, fderiv ℝ (field index) 0) 0 :=
    HasFDerivAt.sum (u := Finset.univ) fun index _ =>
      (fieldDifferentiable index).hasFDerivAt
  have sumDerivativePointwise :
      HasFDerivAt
        (fun point => ∑ index, field index point)
        (∑ index, fderiv ℝ (field index) 0) 0 := by
    convert sumDerivative using 1
    funext point
    simp
  unfold fieldDirectionalDerivative
  rw [sumDerivativePointwise.fderiv]
  simp

private theorem fieldDirectionalDerivative_mul_right_zero
    (left right : BasePoint → ℝ)
    (leftDifferentiable : DifferentiableAt ℝ left 0)
    (rightDifferentiable : DifferentiableAt ℝ right 0)
    (rightZero : right 0 = 0)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative (fun point => left point * right point)
        0 direction =
      left 0 * fieldDirectionalDerivative right 0 direction := by
  unfold fieldDirectionalDerivative
  rw [fderiv_fun_mul leftDifferentiable rightDifferentiable]
  simp [rightZero]

private theorem scalarPairingLeft_derivative
    (field : BasePoint → ScalarCoordinateCarrier)
    (fieldDifferentiable : DifferentiableAt ℝ field 0)
    (fixed : ScalarCoordinateCarrier)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point => scalarCoordinatePairingRe fixed (field point))
        0 direction =
      scalarCoordinatePairingRe fixed
        (fieldDirectionalDerivative field 0 direction) := by
  let pairing :=
    scalarCoordinatePairingReBilinear.toContinuousBilinearMap fixed
  have derivative :=
    pairing.hasFDerivAt.comp 0 fieldDifferentiable.hasFDerivAt
  change
    fieldDirectionalDerivative (fun point => pairing (field point)) 0
        direction =
      pairing (fieldDirectionalDerivative field 0 direction)
  unfold fieldDirectionalDerivative
  rw [show (fun point => pairing (field point)) = pairing ∘ field by rfl,
    derivative.fderiv]
  rfl

private theorem scalarPairingRight_derivative
    (field : BasePoint → ScalarCoordinateCarrier)
    (fieldDifferentiable : DifferentiableAt ℝ field 0)
    (fixed : ScalarCoordinateCarrier)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point => scalarCoordinatePairingRe (field point) fixed)
        0 direction =
      scalarCoordinatePairingRe
        (fieldDirectionalDerivative field 0 direction) fixed := by
  let pairing :=
    scalarCoordinatePairingReBilinear.toContinuousBilinearMap.flip fixed
  have derivative :=
    pairing.hasFDerivAt.comp 0 fieldDifferentiable.hasFDerivAt
  change
    fieldDirectionalDerivative (fun point => pairing (field point)) 0
        direction =
      pairing (fieldDirectionalDerivative field 0 direction)
  unfold fieldDirectionalDerivative
  rw [show (fun point => pairing (field point)) = pairing ∘ field by rfl,
    derivative.fderiv]
  rfl

/-! ## Matter momentum -/

private theorem candidate_matterDifferentialMomentum_eq
    (current : StageNineHolonomicConfiguration)
    (write : P286GaugeOneForm)
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    matterDifferentialMomentum positiveSmoothUnifiedSource
        (Candidate current write) direction derivativeDirection =
      matterDifferentialMomentum positiveSmoothUnifiedSource current direction
        derivativeDirection := by
  funext point
  unfold matterDifferentialMomentum matterDifferentialVariationVector
    generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [candidate_coframe, candidate_conjugateMatter]

/-- A canonical P286 quadratic write preserves matter differential momentum
and hence its divergence as a whole field. -/
theorem canonicalJointCandidate_matterDifferentialMomentumDivergence_eq
    (current : StageNineHolonomicConfiguration)
    (write : P286GaugeOneForm)
    (direction : MatterCoordinateCarrier) :
    matterDifferentialMomentumDivergence positiveSmoothUnifiedSource
        (Candidate current write) direction =
      matterDifferentialMomentumDivergence positiveSmoothUnifiedSource current
        direction := by
  funext point
  unfold matterDifferentialMomentumDivergence
  simp_rw [candidate_matterDifferentialMomentum_eq]

/-! ## Scalar momentum -/

private abbrev canonicalQuadraticVariation
    (write : P286GaugeOneForm) : BasePoint → P286GaugeOneForm :=
  p286HolonomicSecondJetQuadraticRealization
    (p286CanonicalDiagonalResponseSecondJet write)

def canonicalScalarCovariantIncrement
    (current : StageNineHolonomicConfiguration)
    (write : P286GaugeOneForm)
    (point : BasePoint) (formDirection : LorentzianIndex) :
    ScalarCoordinateCarrier :=
  holonomicScalarGaugeConnectionVariation current
    (canonicalQuadraticVariation write) point formDirection

theorem canonicalScalarCovariantIncrement_contDiff
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (write : P286GaugeOneForm)
    (formDirection : LorentzianIndex) :
    ContDiff ℝ ∞ (fun point =>
      canonicalScalarCovariantIncrement current write point formDirection) := by
  have variationSmooth :
      ContDiff ℝ ∞ (canonicalQuadraticVariation write) :=
    p286HolonomicSecondJetQuadraticRealization_contDiff
      (p286CanonicalDiagonalResponseSecondJet write)
  have coordinateSmooth : ContDiff ℝ ∞ (fun point =>
      canonicalQuadraticVariation write point formDirection) :=
    contDiff_pi.mp variationSmooth formDirection
  have scalarSmooth : ContDiff ℝ ∞ current.scalar :=
    smooth.2.2.2.2.2.2.1
  have outerSmooth : ContDiff ℝ ∞ (fun point =>
      scalarP286ActionBilinear.toContinuousBilinearMap
        (canonicalQuadraticVariation write point formDirection)) :=
    contDiff_const.clm_apply coordinateSmooth
  rw [show (fun point =>
      canonicalScalarCovariantIncrement current write point formDirection) =
      fun point =>
        scalarP286ActionBilinear
          (canonicalQuadraticVariation write point formDirection)
          (current.scalar point) by
    funext point
    rfl]
  exact outerSmooth.clm_apply scalarSmooth

private theorem canonicalScalarCovariantIncrement_origin
    (current : StageNineHolonomicConfiguration)
    (write : P286GaugeOneForm)
    (formDirection : LorentzianIndex) :
    canonicalScalarCovariantIncrement current write 0 formDirection = 0 := by
  unfold canonicalScalarCovariantIncrement
    holonomicScalarGaugeConnectionVariation
    p286GaugeConnectionMotherVariation canonicalQuadraticVariation
  rw [p286HolonomicSecondJetQuadraticRealization_origin]
  simp

private theorem canonicalScalarCovariantIncrement_derivative_origin
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (write : P286GaugeOneForm)
    (derivativeDirection formDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          canonicalScalarCovariantIncrement current write point formDirection)
        0 derivativeDirection = 0 := by
  have variationSmooth :
      ContDiff ℝ ∞ (canonicalQuadraticVariation write) :=
    p286HolonomicSecondJetQuadraticRealization_contDiff
      (p286CanonicalDiagonalResponseSecondJet write)
  have parameterDifferentiable : DifferentiableAt ℝ
      (fun point => canonicalQuadraticVariation write point formDirection) 0 :=
    ((contDiff_pi.mp variationSmooth formDirection).differentiable
      (by simp)).differentiableAt
  have scalarDifferentiable : DifferentiableAt ℝ current.scalar 0 :=
    ((smooth.2.2.2.2.2.2.1.differentiable (by simp))).differentiableAt
  let action := scalarP286ActionBilinear.toContinuousBilinearMap
  have totalDerivative :
      fderiv ℝ
          (fun point =>
            action (canonicalQuadraticVariation write point formDirection)
              (current.scalar point)) 0 =
        action.precompR BasePoint
              (canonicalQuadraticVariation write 0 formDirection)
              (fderiv ℝ current.scalar 0) +
          action.precompL BasePoint
              (fderiv ℝ
                (fun point =>
                  canonicalQuadraticVariation write point formDirection) 0)
              (current.scalar 0) :=
    (action.hasFDerivAt_of_bilinear parameterDifferentiable.hasFDerivAt
      scalarDifferentiable.hasFDerivAt).fderiv
  have functionEquality :
      (fun point =>
        canonicalScalarCovariantIncrement current write point formDirection) =
      fun point =>
        action (canonicalQuadraticVariation write point formDirection)
          (current.scalar point) := by
    funext point
    rfl
  rw [functionEquality]
  unfold fieldDirectionalDerivative
  rw [totalDerivative]
  simp only [add_apply, ContinuousLinearMap.precompR_apply,
    ContinuousLinearMap.precompL_apply]
  change
    scalarP286ActionBilinear
          (canonicalQuadraticVariation write 0 formDirection)
          (fieldDirectionalDerivative current.scalar 0 derivativeDirection) +
        scalarP286ActionBilinear
          (fieldDirectionalDerivative
            (fun point =>
              canonicalQuadraticVariation write point formDirection)
            0 derivativeDirection)
          (current.scalar 0) = 0
  rw [show canonicalQuadraticVariation write 0 formDirection = 0 by
      simp [canonicalQuadraticVariation],
    show fieldDirectionalDerivative
        (fun point => canonicalQuadraticVariation write point formDirection)
        0 derivativeDirection = 0 by
      have wholeDerivative :=
        p286HolonomicSecondJetQuadraticRealization_firstJet_origin
          (p286CanonicalDiagonalResponseSecondJet write) derivativeDirection
      rw [← fieldDirectionalDerivative_pi_apply
        (canonicalQuadraticVariation write) variationSmooth 0
        derivativeDirection formDirection]
      exact congrFun wholeDerivative formDirection]
  simp [scalarP286ActionBilinear]

/-- The quadratic P286 connection write has zero complete scalar-covariant
first germ at the origin.  Only differentiability of the supplied scalar is
needed; no global smooth configuration is required. -/
theorem
    canonicalScalarCovariantIncrement_hasFDerivAt_origin_of_scalarDifferentiable
    (current : StageNineHolonomicConfiguration)
    (scalarDifferentiable : DifferentiableAt ℝ current.scalar 0)
    (write : P286GaugeOneForm) :
    HasFDerivAt
      (fun point => canonicalScalarCovariantIncrement current write point)
      (0 : BasePoint →L[ℝ]
        (LorentzianIndex → ScalarCoordinateCarrier)) 0 := by
  rw [show
    (0 : BasePoint →L[ℝ]
      (LorentzianIndex → ScalarCoordinateCarrier)) =
      ContinuousLinearMap.pi
        (fun _ : LorentzianIndex =>
          (0 : BasePoint →L[ℝ] ScalarCoordinateCarrier)) by
    ext point formDirection
    simp]
  apply hasFDerivAt_pi.mpr
  intro formDirection
  let parameter := fun point =>
    canonicalQuadraticVariation write point formDirection
  let projection : P286GaugeOneForm →L[ℝ] P286CoordinateCarrier :=
    ContinuousLinearMap.proj formDirection
  have wholeDerivative : HasFDerivAt (canonicalQuadraticVariation write)
      (0 : BasePoint →L[ℝ] P286GaugeOneForm) 0 := by
    simpa [canonicalQuadraticVariation] using
      p286HolonomicSecondJetQuadraticRealization_hasFDerivAt
        (p286CanonicalDiagonalResponseSecondJet write) 0
  have parameterDerivative : HasFDerivAt parameter
      (0 : BasePoint →L[ℝ] P286CoordinateCarrier) 0 := by
    change HasFDerivAt
      (projection ∘ canonicalQuadraticVariation write)
      (0 : BasePoint →L[ℝ] P286CoordinateCarrier) 0
    exact projection.hasFDerivAt.comp 0 wholeDerivative
  have actual :=
    scalarP286ActionBilinear.toContinuousBilinearMap.hasFDerivAt_of_bilinear
      parameterDerivative scalarDifferentiable.hasFDerivAt
  change HasFDerivAt
    (fun point =>
      scalarP286ActionBilinear (parameter point) (current.scalar point))
    0 0
  simpa [parameter, canonicalQuadraticVariation] using actual

theorem canonicalJointCandidate_scalarCovariantDerivative_expansion
    (current : StageNineHolonomicConfiguration)
    (write : P286GaugeOneForm)
    (point : BasePoint) :
    holonomicScalarCovariantDerivative (Candidate current write) point =
      holonomicScalarCovariantDerivative current point +
        canonicalScalarCovariantIncrement current write point := by
  funext formDirection
  change
    holonomicScalarCovariantDerivative
        (diracDualFormNativeP286CanonicalConnectionCandidate current write)
        point formDirection = _
  unfold diracDualFormNativeP286CanonicalConnectionCandidate
    installP286HolonomicConnectionSecondJet
  rw [holonomicScalarCovariantDerivative_gaugeConnection_expansion]
  simp [canonicalScalarCovariantIncrement, canonicalQuadraticVariation]

def canonicalScalarMomentumIncrement
    (current : StageNineHolonomicConfiguration)
    (write : P286GaugeOneForm)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex)
    (point : BasePoint) : ℝ :=
  let variation :=
    scalarVariationDifferentialDirection direction derivativeDirection
  generatedVolumeDensity (toContinuumPointField current point) *
    ((1 / 2 : ℝ) *
      ∑ first : LorentzianIndex,
        ∑ second : LorentzianIndex,
          ((lorentzianMetricOfCoframe (current.coframe point))⁻¹
              first second) *
            (scalarCoordinatePairingRe
                (variation first)
                (canonicalScalarCovariantIncrement current write point second) +
              scalarCoordinatePairingRe
                (canonicalScalarCovariantIncrement current write point first)
                (variation second)))

theorem canonicalJointCandidate_scalarDifferentialMomentum_eq
    (current : StageNineHolonomicConfiguration)
    (write : P286GaugeOneForm)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    scalarDifferentialMomentum positiveSmoothUnifiedSource
        (Candidate current write) direction derivativeDirection =
      scalarDifferentialMomentum positiveSmoothUnifiedSource current direction
          derivativeDirection +
        canonicalScalarMomentumIncrement current write direction
          derivativeDirection := by
  funext point
  unfold scalarDifferentialMomentum
    scalarGaugeConnectionKineticFirstVariationDensity
    scalarFrameRelativeCovariantDerivative
    canonicalScalarMomentumIncrement generatedVolumeDensity
  simp only [toContinuumPointField,
    scalarFrameRelativeCoordinates_zeroChart]
  rw [candidate_coframe,
    canonicalJointCandidate_scalarCovariantDerivative_expansion]
  simp only [Pi.add_apply, scalarCoordinatePairingRe_add_left,
    scalarCoordinatePairingRe_add_right]
  exact scalarWeightedDoubleSum_add_linear_scaled _ _ _ _ _ _ _

private theorem canonicalScalarMomentumIncrement_firstGerm_origin
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (coframeNondegenerate : Matrix.det (current.coframe 0) ≠ 0)
    (write : P286GaugeOneForm)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    ContDiffAt ℝ ∞
        (canonicalScalarMomentumIncrement current write direction
          derivativeDirection) 0 ∧
      fieldDirectionalDerivative
          (canonicalScalarMomentumIncrement current write direction
            derivativeDirection)
          0 derivativeDirection = 0 := by
  let variation :=
    scalarVariationDifferentialDirection direction derivativeDirection
  let increment := canonicalScalarCovariantIncrement current write
  let volume := fun point => |Matrix.det (current.coframe point)|
  let metric := fun point first second =>
    (lorentzianMetricOfCoframe (current.coframe point))⁻¹ first second
  let pairingTerm := fun first second point =>
    scalarCoordinatePairingRe (variation first) (increment point second) +
      scalarCoordinatePairingRe (increment point first) (variation second)
  let weightedTerm := fun first second point =>
    metric point first second * pairingTerm first second point
  let doubleSum := fun point =>
    ∑ first : LorentzianIndex,
      ∑ second : LorentzianIndex, weightedTerm first second point
  let kinetic := fun point => (1 / 2 : ℝ) * doubleSum point
  have coframeSmooth : ContDiff ℝ ∞ current.coframe :=
    holonomicCoframe_contDiff current smooth
  have volumeSmooth : ContDiffAt ℝ ∞ volume 0 := by
    change ContDiffAt ℝ ∞
      (fun point => |Matrix.det (current.coframe point)|) 0
    exact
      (coframe_volume_contDiffAt
        (current.coframe 0) coframeNondegenerate).comp
          0 coframeSmooth.contDiffAt
  have metricSmooth : ContDiffAt ℝ ∞
      (fun point =>
        (lorentzianMetricOfCoframe (current.coframe point))⁻¹) 0 := by
    exact
      (lorentzianMetric_inv_contDiffAt
        (current.coframe 0) coframeNondegenerate).comp
          0 coframeSmooth.contDiffAt
  have metricEntrySmooth (first second : LorentzianIndex) :
      ContDiffAt ℝ ∞ (fun point => metric point first second) 0 :=
    contDiffAt_pi.mp (contDiffAt_pi.mp metricSmooth first) second
  have incrementSmooth (formDirection : LorentzianIndex) :
      ContDiff ℝ ∞ (fun point => increment point formDirection) := by
    simpa only [increment] using
      canonicalScalarCovariantIncrement_contDiff current smooth write
        formDirection
  have incrementOrigin (formDirection : LorentzianIndex) :
      increment 0 formDirection = 0 := by
    simpa only [increment] using
      canonicalScalarCovariantIncrement_origin current write formDirection
  have incrementDerivative (formDirection : LorentzianIndex) :
      fieldDirectionalDerivative (fun point => increment point formDirection)
          0 derivativeDirection = 0 := by
    simpa only [increment] using
      canonicalScalarCovariantIncrement_derivative_origin current smooth write
        derivativeDirection formDirection
  have pairingTermSmooth (first second : LorentzianIndex) :
      ContDiff ℝ ∞ (pairingTerm first second) := by
    unfold pairingTerm
    exact
      (scalarCoordinatePairingRe_apply_contDiff _ _
        contDiff_const (incrementSmooth second)).add
      (scalarCoordinatePairingRe_apply_contDiff _ _
        (incrementSmooth first) contDiff_const)
  have pairingTermOrigin (first second : LorentzianIndex) :
      pairingTerm first second 0 = 0 := by
    simp [pairingTerm, incrementOrigin, scalarCoordinatePairingRe]
  have pairingTermDerivative (first second : LorentzianIndex) :
      fieldDirectionalDerivative (pairingTerm first second)
          0 derivativeDirection = 0 := by
    have incrementSecondDifferentiable : DifferentiableAt ℝ
        (fun point => increment point second) 0 :=
      ((incrementSmooth second).differentiable (by simp)).differentiableAt
    have incrementFirstDifferentiable : DifferentiableAt ℝ
        (fun point => increment point first) 0 :=
      ((incrementSmooth first).differentiable (by simp)).differentiableAt
    have leftPairingDifferentiable : DifferentiableAt ℝ
        (fun point =>
          scalarCoordinatePairingRe (variation first)
            (increment point second)) 0 :=
      ((scalarCoordinatePairingRe_apply_contDiff _ _ contDiff_const
        (incrementSmooth second)).differentiable (by simp)).differentiableAt
    have rightPairingDifferentiable : DifferentiableAt ℝ
        (fun point =>
          scalarCoordinatePairingRe (increment point first)
            (variation second)) 0 :=
      ((scalarCoordinatePairingRe_apply_contDiff _ _
        (incrementSmooth first) contDiff_const).differentiable
          (by simp)).differentiableAt
    unfold pairingTerm
    rw [fieldDirectionalDerivative_add _ _ leftPairingDifferentiable
      rightPairingDifferentiable derivativeDirection,
      scalarPairingLeft_derivative _ incrementSecondDifferentiable _
        derivativeDirection,
      scalarPairingRight_derivative _ incrementFirstDifferentiable _
        derivativeDirection,
      incrementDerivative second, incrementDerivative first]
    simp [scalarCoordinatePairingRe]
  have weightedTermSmooth (first second : LorentzianIndex) :
      ContDiffAt ℝ ∞ (weightedTerm first second) 0 :=
    (metricEntrySmooth first second).mul
      (pairingTermSmooth first second).contDiffAt
  have weightedTermDerivative (first second : LorentzianIndex) :
      fieldDirectionalDerivative (weightedTerm first second)
          0 derivativeDirection = 0 := by
    unfold weightedTerm
    rw [fieldDirectionalDerivative_mul_right_zero
      (fun point => metric point first second)
      (pairingTerm first second)
      ((metricEntrySmooth first second).differentiableAt (by simp))
      ((pairingTermSmooth first second).differentiable
        (by simp)).differentiableAt
      (pairingTermOrigin first second) derivativeDirection,
      pairingTermDerivative first second]
    simp
  have doubleSumSmooth : ContDiffAt ℝ ∞ doubleSum 0 := by
    unfold doubleSum
    apply ContDiffAt.sum
    intro first _
    apply ContDiffAt.sum
    intro second _
    exact weightedTermSmooth first second
  have doubleSumDerivative :
      fieldDirectionalDerivative doubleSum 0 derivativeDirection = 0 := by
    unfold doubleSum
    rw [fieldDirectionalDerivative_sum
      (fun first point =>
        ∑ second : LorentzianIndex, weightedTerm first second point)
      (fun first =>
        (ContDiffAt.sum fun second _ => weightedTermSmooth first second
          ).differentiableAt (by simp)) derivativeDirection]
    apply Finset.sum_eq_zero
    intro first _
    rw [fieldDirectionalDerivative_sum
      (fun second => weightedTerm first second)
      (fun second =>
        (weightedTermSmooth first second).differentiableAt (by simp))
      derivativeDirection]
    exact Finset.sum_eq_zero fun second _ =>
      weightedTermDerivative first second
  have kineticSmooth : ContDiffAt ℝ ∞ kinetic 0 :=
    contDiffAt_const.mul doubleSumSmooth
  have kineticOrigin : kinetic 0 = 0 := by
    simp [kinetic, doubleSum, weightedTerm, pairingTermOrigin]
  have kineticDerivative :
      fieldDirectionalDerivative kinetic 0 derivativeDirection = 0 := by
    unfold kinetic
    rw [fieldDirectionalDerivative_const_mul doubleSum
      (doubleSumSmooth.differentiableAt (by simp)) (1 / 2 : ℝ)
      derivativeDirection, doubleSumDerivative]
    simp
  have momentumEquality :
      canonicalScalarMomentumIncrement current write direction
          derivativeDirection =
        fun point => volume point * kinetic point := by
    funext point
    unfold canonicalScalarMomentumIncrement volume kinetic doubleSum
      weightedTerm pairingTerm metric variation increment
      generatedVolumeDensity
    simp only [toContinuumPointField]
  constructor
  · rw [momentumEquality]
    exact volumeSmooth.mul kineticSmooth
  · rw [momentumEquality,
      fieldDirectionalDerivative_mul_right_zero volume kinetic
        (volumeSmooth.differentiableAt (by simp))
        (kineticSmooth.differentiableAt (by simp)) kineticOrigin
        derivativeDirection,
      kineticDerivative]
    simp

private theorem current_scalarDifferentialMomentum_contDiffAt_origin
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (coframeNondegenerate : Matrix.det (current.coframe 0) ≠ 0)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    ContDiffAt ℝ ∞
      (scalarDifferentialMomentum positiveSmoothUnifiedSource current
        direction derivativeDirection) 0 := by
  have coframeSmooth : ContDiff ℝ ∞ current.coframe :=
    holonomicCoframe_contDiff current smooth
  have volumeSmooth : ContDiffAt ℝ ∞
      (fun point => |Matrix.det (current.coframe point)|) 0 :=
    (coframe_volume_contDiffAt
      (current.coframe 0) coframeNondegenerate).comp
        0 coframeSmooth.contDiffAt
  have metricSmooth : ContDiffAt ℝ ∞
      (fun point =>
        (lorentzianMetricOfCoframe (current.coframe point))⁻¹) 0 :=
    (lorentzianMetric_inv_contDiffAt
      (current.coframe 0) coframeNondegenerate).comp
        0 coframeSmooth.contDiffAt
  have covariantSmooth (formDirection : LorentzianIndex) :
      ContDiff ℝ ∞ (fun point =>
        holonomicScalarCovariantDerivative current point formDirection) :=
    holonomicScalarCovariantDerivative_contDiff current smooth formDirection
  have variationSmooth (formDirection : LorentzianIndex) :
      ContDiff ℝ ∞ (fun _ : BasePoint =>
        scalarVariationDifferentialDirection direction derivativeDirection
          formDirection) :=
    contDiff_const
  unfold scalarDifferentialMomentum
    scalarGaugeConnectionKineticFirstVariationDensity
    scalarFrameRelativeCovariantDerivative generatedVolumeDensity
  simp only [toContinuumPointField,
    scalarFrameRelativeCoordinates_zeroChart]
  apply volumeSmooth.mul
  apply contDiffAt_const.mul
  apply ContDiffAt.sum
  intro first _
  apply ContDiffAt.sum
  intro second _
  apply (contDiffAt_pi.mp (contDiffAt_pi.mp metricSmooth first) second).mul
  exact
    ((StageNineCoframeScalarMatterRegularity.scalarCoordinatePairingRe_joint_contDiff_local
      _ _ (variationSmooth first) (covariantSmooth second)).add
      (StageNineCoframeScalarMatterRegularity.scalarCoordinatePairingRe_joint_contDiff_local
        _ _ (covariantSmooth first) (variationSmooth second))).contDiffAt

private theorem candidate_scalarMomentum_diagonalDerivative_origin_eq
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (coframeNondegenerate : Matrix.det (current.coframe 0) ≠ 0)
    (write : P286GaugeOneForm)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (scalarDifferentialMomentum positiveSmoothUnifiedSource
          (Candidate current write) direction derivativeDirection)
        0 derivativeDirection =
      fieldDirectionalDerivative
        (scalarDifferentialMomentum positiveSmoothUnifiedSource current
          direction derivativeDirection)
        0 derivativeDirection := by
  rw [canonicalJointCandidate_scalarDifferentialMomentum_eq]
  change
    fieldDirectionalDerivative
        (fun point =>
          scalarDifferentialMomentum positiveSmoothUnifiedSource current
              direction derivativeDirection point +
            canonicalScalarMomentumIncrement current write direction
              derivativeDirection point)
        0 derivativeDirection = _
  rw [fieldDirectionalDerivative_add]
  · rw [(canonicalScalarMomentumIncrement_firstGerm_origin current smooth
      coframeNondegenerate write direction derivativeDirection).2]
    simp
  · exact
      (current_scalarDifferentialMomentum_contDiffAt_origin current smooth
        coframeNondegenerate direction derivativeDirection).differentiableAt
        (by simp)
  · exact
      (canonicalScalarMomentumIncrement_firstGerm_origin current smooth
        coframeNondegenerate write direction derivativeDirection
        ).1.differentiableAt
        (by simp)

/-- A homogeneous-quadratic canonical P286 write preserves the complete
scalar differential-momentum divergence at every nondegenerate contact. -/
theorem
    canonicalJointCandidate_scalarDifferentialMomentumDivergence_origin_eq_of_nondegenerate
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (coframeNondegenerate : Matrix.det (current.coframe 0) ≠ 0)
    (write : P286GaugeOneForm) :
    (fun direction =>
      scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource
        (Candidate current write) direction 0) =
      fun direction =>
        scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource
          current direction 0 := by
  funext direction
  unfold scalarDifferentialMomentumDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  exact candidate_scalarMomentum_diagonalDerivative_origin_eq current smooth
    coframeNondegenerate write direction derivativeDirection

/-- Compatibility wrapper for the historical identity-coframe mouth. -/
theorem canonicalJointCandidate_scalarDifferentialMomentumDivergence_origin_eq
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (coframeOrigin : current.coframe 0 = 1)
    (write : P286GaugeOneForm) :
    (fun direction =>
      scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource
        (Candidate current write) direction 0) =
      fun direction =>
        scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource
          current direction 0 := by
  apply
    canonicalJointCandidate_scalarDifferentialMomentumDivergence_origin_eq_of_nondegenerate
      current smooth
  rw [coframeOrigin]
  norm_num

private def scalarMomentumInner
    (configuration : StageNineHolonomicConfiguration) :
    BasePoint →
      LorentzianCoframe ×
        (LorentzianIndex → ScalarCoordinateCarrier) :=
  fun point =>
    (configuration.coframe point,
      holonomicScalarCovariantDerivative configuration point)

/-- Local finite-germ form of P286 scalar-momentum preservation.  It records
exactly the fields read by the scalar momentum and therefore applies to
finite-regularity Cauchy developments without promoting them to globally
smooth configurations. -/
theorem
    canonicalJointCandidate_scalarDifferentialMomentumDivergence_origin_eq_of_local
    (current : StageNineHolonomicConfiguration)
    (coframeDifferentiable : DifferentiableAt ℝ current.coframe 0)
    (scalarDifferentiable : DifferentiableAt ℝ current.scalar 0)
    (scalarCovariantDifferentiable : DifferentiableAt ℝ
      (holonomicScalarCovariantDerivative current) 0)
    (coframeNondegenerate : Matrix.det (current.coframe 0) ≠ 0)
    (write : P286GaugeOneForm) :
    (fun direction =>
      scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource
        (Candidate current write) direction 0) =
      fun direction =>
        scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource
          current direction 0 := by
  have covariantEquality :
      holonomicScalarCovariantDerivative (Candidate current write) =
        fun point =>
          holonomicScalarCovariantDerivative current point +
            canonicalScalarCovariantIncrement current write point := by
    funext point
    exact canonicalJointCandidate_scalarCovariantDerivative_expansion
      current write point
  let covariantDerivative :=
    fderiv ℝ (holonomicScalarCovariantDerivative current) 0
  have incrementDerivative : HasFDerivAt
      (fun point => canonicalScalarCovariantIncrement current write point)
      (0 : BasePoint →L[ℝ]
        (LorentzianIndex → ScalarCoordinateCarrier)) 0 :=
    canonicalScalarCovariantIncrement_hasFDerivAt_origin_of_scalarDifferentiable
      current scalarDifferentiable write
  have candidateCovariantDerivative : HasFDerivAt
      (holonomicScalarCovariantDerivative (Candidate current write))
      covariantDerivative 0 := by
    have generated :=
      scalarCovariantDifferentiable.hasFDerivAt.add incrementDerivative
    rw [covariantEquality]
    simpa [covariantDerivative] using generated
  let coframeDerivative := fderiv ℝ current.coframe 0
  have candidateCoframeDerivative : HasFDerivAt
      (Candidate current write).coframe coframeDerivative 0 := by
    exact
      (congrArg
        (fun field => HasFDerivAt field coframeDerivative 0)
        (candidate_coframe current write)).symm.mp
          coframeDifferentiable.hasFDerivAt
  let innerDerivative : BasePoint →L[ℝ]
      (LorentzianCoframe ×
        (LorentzianIndex → ScalarCoordinateCarrier)) :=
    coframeDerivative.prod covariantDerivative
  have currentInnerDerivative : HasFDerivAt (scalarMomentumInner current)
      innerDerivative 0 := by
    exact HasFDerivAt.prodMk coframeDifferentiable.hasFDerivAt
      scalarCovariantDifferentiable.hasFDerivAt
  have candidateInnerDerivative : HasFDerivAt
      (scalarMomentumInner (Candidate current write)) innerDerivative 0 := by
    exact HasFDerivAt.prodMk candidateCoframeDerivative
      candidateCovariantDerivative
  have innerOriginEquality :
      scalarMomentumInner (Candidate current write) 0 =
        scalarMomentumInner current 0 := by
    apply Prod.ext
    · exact congrFun (candidate_coframe current write) 0
    · change
        holonomicScalarCovariantDerivative (Candidate current write) 0 =
          holonomicScalarCovariantDerivative current 0
      rw [covariantEquality]
      change
        holonomicScalarCovariantDerivative current 0 +
            canonicalScalarCovariantIncrement current write 0 =
          holonomicScalarCovariantDerivative current 0
      have incrementOrigin : canonicalScalarCovariantIncrement current write 0 = 0 := by
        funext formDirection
        exact canonicalScalarCovariantIncrement_origin current write formDirection
      rw [incrementOrigin, add_zero]
  have diagonalDerivativeEquality
      (direction : ScalarCoordinateCarrier)
      (derivativeDirection : LorentzianIndex) :
      fieldDirectionalDerivative
          (scalarDifferentialMomentum positiveSmoothUnifiedSource
            (Candidate current write) direction derivativeDirection)
          0 derivativeDirection =
        fieldDirectionalDerivative
          (scalarDifferentialMomentum positiveSmoothUnifiedSource current
            direction derivativeDirection)
          0 derivativeDirection := by
    let outer :=
      scalarMomentumCoframeCovariantReadout direction derivativeDirection
    have outerAtCurrent : DifferentiableAt ℝ outer
        (scalarMomentumInner current 0) := by
      change DifferentiableAt ℝ outer
        (current.coframe 0,
          holonomicScalarCovariantDerivative current 0)
      exact
        (scalarMomentumCoframeCovariantReadout_contDiffAt direction
          derivativeDirection (current.coframe 0) coframeNondegenerate
          (holonomicScalarCovariantDerivative current 0)).differentiableAt
          (by norm_num)
    have outerAtCandidate : DifferentiableAt ℝ outer
        (scalarMomentumInner (Candidate current write) 0) := by
      rw [innerOriginEquality]
      exact outerAtCurrent
    have compositionDerivativeEquality :
        fderiv ℝ
            (outer ∘ scalarMomentumInner (Candidate current write)) 0 =
          fderiv ℝ (outer ∘ scalarMomentumInner current) 0 := by
      have outerCandidateDerivative : HasFDerivAt outer
          (fderiv ℝ outer (scalarMomentumInner current 0))
          (scalarMomentumInner (Candidate current write) 0) := by
        rw [innerOriginEquality]
        exact outerAtCurrent.hasFDerivAt
      have candidateComposition :=
        outerCandidateDerivative.comp 0 candidateInnerDerivative
      have currentComposition :=
        outerAtCurrent.hasFDerivAt.comp 0 currentInnerDerivative
      exact candidateComposition.fderiv.trans currentComposition.fderiv.symm
    rw [scalarDifferentialMomentum_eq_readout,
      scalarDifferentialMomentum_eq_readout]
    unfold fieldDirectionalDerivative
    exact congrArg
      (fun derivative : BasePoint →L[ℝ] ℝ =>
        derivative (coordinateDirection derivativeDirection))
      compositionDerivativeEquality
  funext direction
  unfold scalarDifferentialMomentumDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  exact diagonalDerivativeEquality direction derivativeDirection

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeP286CanonicalJointActionFirstGerm
