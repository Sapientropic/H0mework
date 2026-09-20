import H0mework.Physics.GaugeAction.CurrentP286CompleteActionResponseOperator

/-!
# Stage-9 current P286 complete action-response first jet

This companion module proves the actual BF-momentum first jet of the
parameter-free current P286 response operator.  Its jurisdiction is the
explicit fixed identity-coframe principal.  It supplies temporal and spatial
response laws, their full one-form decomposition, and the resulting
producer-consistency theorem.  The latter checks the same action dual that
generated the unique velocity and charge; it is not an independent
constraint and no equation certificate enters the producer mouth.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineCurrentP286CompleteActionResponseOperator

open ProofFreeRicherAnholonomicSource
open StageNineBlockwiseConstitutive
open StageNineCanonicalCauchyState
open StageNineCoframeTwoFormPairing
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286ActionCanonicalPairUpdate
open StageNineP286ActionCauchySplit
open StageNineP286ActionVelocityLocalActualLift
open StageNineP286GaugeAuxiliaryEquation
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionMomentumRegularity
open StageNineP286GaugeConnectionPointwiseEquation
open StageNineP286GaugeConnectionVariation
open StageNineSourceActionGeneratedP286GaussJointLocalActualLift
open StageNineSourceActionGeneratedP286MomentumJointLocalActualLift
open SU7MotherGaugeTheory
open SU7MotherLieAlgebra
open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 200000

local instance firstJetP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance firstJetP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance firstJetP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

/-! ## Canonical-slice auxiliary first jet -/

private theorem firstJet_hasDerivAt_const_add_time_smul
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (initial velocity : F)
    (time : ℝ) :
    HasDerivAt (fun candidate : ℝ => initial + candidate • velocity)
      velocity time := by
  have derivative :=
    (hasDerivAt_const time initial).add
      ((hasDerivAt_id time).smul_const velocity)
  convert derivative using 1
  · funext candidate
    rfl
  · simp

/-- The generated Gauss profile depends only on the three spatial
coordinates.  Canonical Cauchy restriction therefore retains the full
spatial profile instead of collapsing it to the origin. -/
theorem currentP286CanonicalGaussRadialAuxiliaryProfile_canonicalSlice
    (charge : P286CoordinateCarrier)
    (time : ℝ)
    (space : StageNineSpatialPoint) :
    currentP286CanonicalGaussRadialAuxiliaryProfile charge
        (canonicalCauchySlicePoint time space) =
      ∑ axis : Fin 3,
        (canonicalP286EqualAxisCoefficient * space axis) •
          p286GaussAuxiliaryAxisEmbedding charge axis := by
  unfold currentP286CanonicalGaussRadialAuxiliaryProfile
    symmetricP286GaussRadialAuxiliaryProfile
  apply Finset.sum_congr rfl
  intro axis _
  rw [canonicalCauchySlicePoint_spatial]

/-- On every canonical spatial contact, the complete auxiliary coordinate is
an affine physical-time path with the generated velocity, while the
generated spatial Gauss profile remains present as a time-independent
summand. -/
theorem currentP286CompleteResponseAuxiliaryCoordinate_canonicalSlice
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (time : ℝ)
    (space : StageNineSpatialPoint) :
    currentP286CompleteResponseAuxiliaryCoordinate source current
        (canonicalCauchySlicePoint time space) =
      currentP286OriginAuxiliaryCoordinate current +
        time •
          p286SpatialAuxiliaryVelocityEmbedding
            (currentP286SpatialAuxiliaryVelocity source current) +
        ∑ axis : Fin 3,
          (canonicalP286EqualAxisCoefficient * space axis) •
            p286GaussAuxiliaryAxisEmbedding
              (currentP286GaussCharge source current) axis := by
  rw [currentP286CompleteResponseAuxiliaryCoordinate,
    canonicalCauchySlicePoint_time,
    currentP286CanonicalGaussRadialAuxiliaryProfile_canonicalSlice]

/-- The pairwise temporal first jet of the generated auxiliary coordinate is
exactly the BF-Legendre velocity generated from the same current action
dual.  This holds at every spatial contact; the radial Gauss profile is
retained in the path but contributes no physical-time derivative. -/
theorem
    currentP286CompleteResponseAuxiliaryCoordinate_canonicalSlice_hasDerivAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint)
    (pair : Fin 6)
    (time : ℝ) :
    HasDerivAt
      (fun candidate : ℝ =>
        currentP286CompleteResponseAuxiliaryCoordinate source current
          (canonicalCauchySlicePoint candidate space) pair)
      (p286SpatialAuxiliaryVelocityEmbedding
        (currentP286SpatialAuxiliaryVelocity source current) pair)
      time := by
  rw [show
    (fun candidate : ℝ =>
      currentP286CompleteResponseAuxiliaryCoordinate source current
        (canonicalCauchySlicePoint candidate space) pair) =
      (fun candidate : ℝ =>
        (currentP286OriginAuxiliaryCoordinate current +
          ∑ axis : Fin 3,
            (canonicalP286EqualAxisCoefficient * space axis) •
              p286GaussAuxiliaryAxisEmbedding
                (currentP286GaussCharge source current) axis) pair +
          candidate •
            p286SpatialAuxiliaryVelocityEmbedding
              (currentP286SpatialAuxiliaryVelocity source current) pair) by
    funext candidate
    rw [currentP286CompleteResponseAuxiliaryCoordinate_canonicalSlice]
    simp only [Pi.add_apply, Pi.smul_apply]
    abel]
  exact
    firstJet_hasDerivAt_const_add_time_smul
      ((currentP286OriginAuxiliaryCoordinate current +
        ∑ axis : Fin 3,
          (canonicalP286EqualAxisCoefficient * space axis) •
            p286GaussAuxiliaryAxisEmbedding
              (currentP286GaussCharge source current) axis) pair)
      (p286SpatialAuxiliaryVelocityEmbedding
        (currentP286SpatialAuxiliaryVelocity source current) pair)
      time

/-! ## Identity-coframe BF-momentum first jet -/

private theorem hodgePairing_add_left
    (first second test : P286GaugeTwoForm) :
    p286GaugeAuxiliaryHodgePairingPolynomial 1 (first + second) test =
      p286GaugeAuxiliaryHodgePairingPolynomial 1 first test +
        p286GaugeAuxiliaryHodgePairingPolynomial 1 second test := by
  unfold p286GaugeAuxiliaryHodgePairingPolynomial
  rw [liftGaugeTwoFormOperator_add_p286]
  simp_rw [Pi.add_apply, p286CoordinateLiePairing_add_left]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]

private theorem hodgePairing_smul_left
    (parameter : ℝ) (first test : P286GaugeTwoForm) :
    p286GaugeAuxiliaryHodgePairingPolynomial 1 (parameter • first) test =
      parameter *
        p286GaugeAuxiliaryHodgePairingPolynomial 1 first test := by
  unfold p286GaugeAuxiliaryHodgePairingPolynomial
  rw [liftGaugeTwoFormOperator_smul_p286]
  simp_rw [Pi.smul_apply, p286CoordinateLiePairing_smul_left]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro pair _
  ring

private def hodgePairingLinear (test : P286GaugeTwoForm) :
    P286GaugeTwoForm →ₗ[ℝ] ℝ where
  toFun first := p286GaugeAuxiliaryHodgePairingPolynomial 1 first test
  map_add' := fun first second => hodgePairing_add_left first second test
  map_smul' := by
    intro parameter first
    simpa [smul_eq_mul] using
      hodgePairing_smul_left parameter first test

@[simp] private theorem hodgePairingLinear_apply
    (test first : P286GaugeTwoForm) :
    hodgePairingLinear test first =
      p286GaugeAuxiliaryHodgePairingPolynomial 1 first test :=
  rfl

theorem currentP286CompleteActionResponseOperator_bfMomentum_normalForm
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (coframeOne : ∀ point, current.coframe point = 1)
    (direction : P286GaugeTwoForm)
    (point : BasePoint) :
    p286GaugeConnectionBFDifferentialMomentum
        (currentP286CompleteActionResponseOperator source current)
        direction point =
      p286GaugeAuxiliaryHodgePairingPolynomial 1
        (currentP286CompleteResponseAuxiliaryCoordinate source current point)
        direction := by
  unfold p286GaugeConnectionBFDifferentialMomentum generatedVolumeDensity
  rw [show
    (toContinuumPointField
      (currentP286CompleteActionResponseOperator source current) point).coframe =
        1 by
      exact coframeOne point]
  rw [show
    (currentP286CompleteActionResponseOperator source current).coframe point =
        1 by
      exact coframeOne point]
  rw [currentP286CompleteActionResponseOperator_auxiliaryCoordinate]
  simp

theorem currentP286CompleteActionResponseOperator_bfMomentum_affineNormalForm
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (coframeOne : ∀ point, current.coframe point = 1)
    (direction : P286GaugeTwoForm)
    (point : BasePoint) :
    p286GaugeConnectionBFDifferentialMomentum
        (currentP286CompleteActionResponseOperator source current)
        direction point =
      p286GaugeAuxiliaryHodgePairingPolynomial 1
          (currentP286OriginAuxiliaryCoordinate current) direction +
        point canonicalLorentzianTimeDirection *
          p286GaugeAuxiliaryHodgePairingPolynomial 1
            (p286SpatialAuxiliaryVelocityEmbedding
              (currentP286SpatialAuxiliaryVelocity source current))
            direction +
        ∑ axis : Fin 3,
          (canonicalP286EqualAxisCoefficient * point axis.succ) *
            p286GaugeAuxiliaryHodgePairingPolynomial 1
              (p286GaussAuxiliaryAxisEmbedding
                (currentP286GaussCharge source current) axis)
              direction := by
  rw [currentP286CompleteActionResponseOperator_bfMomentum_normalForm
    source current coframeOne]
  change hodgePairingLinear direction
      (currentP286CompleteResponseAuxiliaryCoordinate source current point) = _
  rw [currentP286CompleteResponseAuxiliaryCoordinate, map_add, map_add,
    map_smul, currentP286CanonicalGaussRadialAuxiliaryProfile,
    symmetricP286GaussRadialAuxiliaryProfile, map_sum]
  simp only [map_smul, smul_eq_mul, hodgePairingLinear_apply]

private theorem fieldDirectionalDerivative_add_real
    (first second : BasePoint → ℝ)
    (firstSmooth : ContDiff ℝ ∞ first)
    (secondSmooth : ContDiff ℝ ∞ second)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative (first + second) 0 direction =
      fieldDirectionalDerivative first 0 direction +
        fieldDirectionalDerivative second 0 direction := by
  change
    fieldDirectionalDerivative (fun point => first point + second point)
        0 direction = _
  unfold fieldDirectionalDerivative
  rw [fderiv_fun_add
    (firstSmooth.differentiable (by simp) 0)
    (secondSmooth.differentiable (by simp) 0)]
  rfl

private theorem fieldDirectionalDerivative_finset_sum_real
    {Index : Type*} [Fintype Index]
    (field : Index → BasePoint → ℝ)
    (fieldSmooth : ∀ index, ContDiff ℝ ∞ (field index))
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative (fun point => ∑ index, field index point)
        0 direction =
      ∑ index, fieldDirectionalDerivative (field index) 0 direction := by
  have sumDerivative :
      HasFDerivAt
        (∑ index, field index)
        (∑ index, fderiv ℝ (field index) 0) 0 :=
    HasFDerivAt.sum (u := Finset.univ) fun index _ =>
      ((fieldSmooth index).differentiable (by simp)).differentiableAt
        |>.hasFDerivAt
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

private theorem fieldDirectionalDerivative_coordinate_mul_constant
    (coordinate direction : LorentzianIndex) (coefficient : ℝ) :
    fieldDirectionalDerivative
        (fun point : BasePoint => point coordinate * coefficient)
        0 direction =
      if coordinate = direction then coefficient else 0 := by
  let coordinateField := localBaseCoordinate coordinate
  have coordinateDifferentiable :
      DifferentiableAt ℝ coordinateField 0 :=
    coordinateField.differentiable.differentiableAt
  have coefficientDifferentiable :
      DifferentiableAt ℝ (fun _ : BasePoint => coefficient) 0 :=
    differentiableAt_const coefficient
  unfold fieldDirectionalDerivative
  change
    fderiv ℝ (fun point => coordinateField point * coefficient) 0
        (coordinateDirection direction) = _
  rw [fderiv_fun_mul coordinateDifferentiable coefficientDifferentiable,
    coordinateField.hasFDerivAt.fderiv]
  by_cases sameDirection : coordinate = direction
  · subst direction
    simp [coordinateField, localBaseCoordinate, coordinateDirection]
  · simp [coordinateField, localBaseCoordinate, coordinateDirection,
      sameDirection]

private theorem fieldDirectionalDerivative_scaledSpatialCoordinate_mul_constant
    (weight coefficient : ℝ)
    (axis : Fin 3)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point : BasePoint =>
          (weight * point axis.succ) * coefficient)
        0 direction =
      if axis.succ = direction then weight * coefficient else 0 := by
  rw [show
    (fun point : BasePoint =>
      (weight * point axis.succ) * coefficient) =
      (fun point : BasePoint =>
        point axis.succ * (weight * coefficient)) by
    funext point
    ring]
  exact fieldDirectionalDerivative_coordinate_mul_constant
    axis.succ direction (weight * coefficient)

/-- Actual-first master derivative.  It differentiates the BF momentum of
the generated auxiliary germ; no residual or equation certificate occurs in
its mouth. -/
theorem currentP286CompleteActionResponseOperator_bfMomentum_derivative
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (coframeOne : ∀ point, current.coframe point = 1)
    (direction : P286GaugeTwoForm)
    (derivativeDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (p286GaugeConnectionBFDifferentialMomentum
          (currentP286CompleteActionResponseOperator source current)
          direction)
        0 derivativeDirection =
      (if canonicalLorentzianTimeDirection = derivativeDirection then
        p286GaugeAuxiliaryHodgePairingPolynomial 1
          (p286SpatialAuxiliaryVelocityEmbedding
            (currentP286SpatialAuxiliaryVelocity source current))
          direction
      else 0) +
        ∑ axis : Fin 3,
          if axis.succ = derivativeDirection then
            canonicalP286EqualAxisCoefficient *
              p286GaugeAuxiliaryHodgePairingPolynomial 1
                (p286GaussAuxiliaryAxisEmbedding
                  (currentP286GaussCharge source current) axis)
                direction
          else 0 := by
  let baseField : BasePoint → ℝ := fun point =>
    p286GaugeAuxiliaryHodgePairingPolynomial 1
          (currentP286OriginAuxiliaryCoordinate current) direction +
      point canonicalLorentzianTimeDirection *
        p286GaugeAuxiliaryHodgePairingPolynomial 1
          (p286SpatialAuxiliaryVelocityEmbedding
            (currentP286SpatialAuxiliaryVelocity source current))
          direction
  let radialField : BasePoint → ℝ := fun point =>
    ∑ axis : Fin 3,
      (canonicalP286EqualAxisCoefficient * point axis.succ) *
        p286GaugeAuxiliaryHodgePairingPolynomial 1
          (p286GaussAuxiliaryAxisEmbedding
            (currentP286GaussCharge source current) axis)
          direction
  have momentumEquality :
      p286GaugeConnectionBFDifferentialMomentum
          (currentP286CompleteActionResponseOperator source current)
          direction =
        baseField + radialField := by
    funext point
    exact
      currentP286CompleteActionResponseOperator_bfMomentum_affineNormalForm
        source current coframeOne direction point
  have baseSmooth : ContDiff ℝ ∞ baseField := by
    dsimp [baseField]
    fun_prop
  have radialSummandSmooth (axis : Fin 3) :
      ContDiff ℝ ∞ fun point : BasePoint =>
        (canonicalP286EqualAxisCoefficient * point axis.succ) *
          p286GaugeAuxiliaryHodgePairingPolynomial 1
            (p286GaussAuxiliaryAxisEmbedding
              (currentP286GaussCharge source current) axis)
            direction := by
    fun_prop
  have radialSmooth : ContDiff ℝ ∞ radialField := by
    dsimp [radialField]
    apply ContDiff.sum
    intro axis _
    exact radialSummandSmooth axis
  rw [momentumEquality,
    fieldDirectionalDerivative_add_real baseField radialField baseSmooth
      radialSmooth derivativeDirection]
  have baseDerivative :
      fieldDirectionalDerivative baseField 0 derivativeDirection =
        if canonicalLorentzianTimeDirection = derivativeDirection then
          p286GaugeAuxiliaryHodgePairingPolynomial 1
            (p286SpatialAuxiliaryVelocityEmbedding
              (currentP286SpatialAuxiliaryVelocity source current))
            direction
        else 0 := by
    dsimp [baseField]
    rw [show
      (fun point : BasePoint =>
        p286GaugeAuxiliaryHodgePairingPolynomial 1
            (currentP286OriginAuxiliaryCoordinate current) direction +
          point canonicalLorentzianTimeDirection *
            p286GaugeAuxiliaryHodgePairingPolynomial 1
              (p286SpatialAuxiliaryVelocityEmbedding
                (currentP286SpatialAuxiliaryVelocity source current))
              direction) =
        (fun _ : BasePoint =>
          p286GaugeAuxiliaryHodgePairingPolynomial 1
            (currentP286OriginAuxiliaryCoordinate current) direction) +
        (fun point : BasePoint =>
          point canonicalLorentzianTimeDirection *
            p286GaugeAuxiliaryHodgePairingPolynomial 1
              (p286SpatialAuxiliaryVelocityEmbedding
                (currentP286SpatialAuxiliaryVelocity source current))
              direction) by
      rfl]
    rw [fieldDirectionalDerivative_add_real _ _ contDiff_const (by fun_prop)]
    rw [show
      fieldDirectionalDerivative
        (fun _ : BasePoint =>
          p286GaugeAuxiliaryHodgePairingPolynomial 1
            (currentP286OriginAuxiliaryCoordinate current) direction)
        0 derivativeDirection = 0 by
      simp [fieldDirectionalDerivative]]
    rw [fieldDirectionalDerivative_coordinate_mul_constant]
    simp
  rw [baseDerivative]
  apply congrArg₂ (fun first second : ℝ => first + second) rfl
  dsimp [radialField]
  rw [fieldDirectionalDerivative_finset_sum_real _ radialSummandSmooth]
  apply Finset.sum_congr rfl
  intro axis _
  exact
    fieldDirectionalDerivative_scaledSpatialCoordinate_mul_constant
      canonicalP286EqualAxisCoefficient _ axis derivativeDirection

/-! ## Fixed-principal response laws -/

private theorem liftGaugeTwoFormOperator_id_p286
    (form : P286GaugeTwoForm) :
    liftGaugeTwoFormOperator
        (LinearMap.id : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm) form = form := by
  funext pair
  rw [WithLp.ext_iff]
  funext internal
  rw [liftGaugeTwoFormOperator_p286Coordinate_apply]
  fin_cases pair <;> simp

private theorem liftGaugeTwoFormOperator_fixedHodge_apply
    (form : P286GaugeTwoForm)
    (pair : Fin 6) :
    liftGaugeTwoFormOperator lorentzianCoframeHodge form pair =
      ![form 3, form 4, form 5, -form 0, -form 1, -form 2] pair := by
  rw [WithLp.ext_iff]
  funext internal
  rw [liftGaugeTwoFormOperator_p286Coordinate_apply]
  fin_cases pair <;> rfl

theorem p286TimeExterior_fullDirection
    (direction : P286GaugeOneForm) :
    p286GaugeExteriorDerivativeDirection canonicalLorentzianTimeDirection
        direction =
      p286GaugeExteriorDerivativeDirection canonicalLorentzianTimeDirection
        (canonicalP286SpatialGaugeOneForm
          (fun index => direction index.succ)) := by
  funext pair
  fin_cases pair <;>
    simp [p286GaugeExteriorDerivativeDirection,
      canonicalLorentzianTimeDirection, pairFirst, pairSecond]

private theorem p286TimeExteriorSpatialDirection_normalForm
    (direction : P286SpatialGaugeDirection) :
    p286GaugeExteriorDerivativeDirection canonicalLorentzianTimeDirection
        (canonicalP286SpatialGaugeOneForm direction) =
      ![direction 0, direction 1, direction 2, 0, 0, 0] := by
  funext pair
  fin_cases pair <;>
    simp [p286GaugeExteriorDerivativeDirection,
      canonicalLorentzianTimeDirection, pairFirst, pairSecond]

private theorem p286CoordinateLiePairing_neg_right
    (first second : P286CoordinateCarrier) :
    p286CoordinateLiePairing first (-second) =
      -p286CoordinateLiePairing first second := by
  rw [show -second = (-1 : ℝ) • second by simp,
    p286CoordinateLiePairing_smul_right]
  ring

theorem identityP286SpatialBFLegendre_normalForm
    (candidate direction : P286SpatialGaugeDirection) :
    p286GaugeAuxiliaryHodgePairingPolynomial 1
        (p286SpatialAuxiliaryVelocityEmbedding candidate)
        (p286GaugeExteriorDerivativeDirection
          canonicalLorentzianTimeDirection
          (canonicalP286SpatialGaugeOneForm direction)) =
      -(∑ index : Fin 3,
        p286CoordinateLiePairing (candidate index) (direction index)) := by
  unfold p286GaugeAuxiliaryHodgePairingPolynomial
  rw [coframeTwoFormLinear_one]
  simp_rw [liftGaugeTwoFormOperator_id_p286]
  rw [p286TimeExteriorSpatialDirection_normalForm,
    Fin.sum_univ_six, Fin.sum_univ_three]
  simp [p286SpatialAuxiliaryVelocityEmbedding,
    liftGaugeTwoFormOperator_fixedHodge_apply,
    lorentzianTwoFormSign, minkowskiInternalSign,
    pairFirst, pairSecond, p286CoordinateLiePairing_neg_right]
  ring

theorem identityP286GaussAxisMomentum_fullDirection
    (candidate : P286CoordinateCarrier)
    (direction : P286GaugeOneForm)
    (axis : Fin 3) :
    p286GaugeAuxiliaryHodgePairingPolynomial 1
        (p286GaussAuxiliaryAxisEmbedding candidate axis)
        (p286GaugeExteriorDerivativeDirection axis.succ direction) =
      p286CoordinateLiePairing candidate
        (direction canonicalLorentzianTimeDirection) := by
  unfold p286GaugeAuxiliaryHodgePairingPolynomial
  rw [coframeTwoFormLinear_one]
  simp_rw [liftGaugeTwoFormOperator_id_p286]
  rw [Fin.sum_univ_six]
  fin_cases axis <;>
    simp [p286GaussAuxiliaryAxisEmbedding,
      p286SpatialAuxiliaryVelocityEmbedding,
      p286GaugeExteriorDerivativeDirection,
      canonicalLorentzianTimeDirection,
      liftGaugeTwoFormOperator_fixedHodge_apply,
      lorentzianTwoFormSign, minkowskiInternalSign,
      pairFirst, pairSecond]

/-- Full-direction temporal response. -/
theorem
    currentP286CompleteActionResponseOperator_temporalBFMomentumResponse
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (coframeOne : ∀ point, current.coframe point = 1)
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionTemporalBFMomentumDerivative
        (currentP286CompleteActionResponseOperator source current)
        direction 0 =
      currentP286SpatialActionTarget source current
        (fun index => direction index.succ) := by
  unfold p286GaugeConnectionTemporalBFMomentumDerivative
  rw [currentP286CompleteActionResponseOperator_bfMomentum_derivative
    source current coframeOne]
  rw [show
    (∑ axis : Fin 3,
      if axis.succ = canonicalLorentzianTimeDirection then
        canonicalP286EqualAxisCoefficient *
          p286GaugeAuxiliaryHodgePairingPolynomial 1
            (p286GaussAuxiliaryAxisEmbedding
              (currentP286GaussCharge source current) axis)
            (p286GaugeExteriorDerivativeDirection
              canonicalLorentzianTimeDirection direction)
      else 0) = 0 by
    rw [Fin.sum_univ_three]
    simp [canonicalLorentzianTimeDirection]]
  simp only [if_pos, add_zero]
  rw [p286TimeExterior_fullDirection,
    identityP286SpatialBFLegendre_normalForm]
  change
    p286SpatialBFLegendreDualOperator
        (currentP286SpatialAuxiliaryVelocity source current)
        (fun index => direction index.succ) =
      currentP286SpatialActionTarget source current
        (fun index => direction index.succ)
  rw [currentP286SpatialAuxiliaryVelocity_response]

/-- The spatial-direction restriction used by the canonical Cauchy split. -/
theorem
    currentP286CompleteActionResponseOperator_temporalBFMomentumResponse_spatial
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (coframeOne : ∀ point, current.coframe point = 1)
    (direction : P286SpatialGaugeDirection) :
    p286GaugeConnectionTemporalBFMomentumDerivative
        (currentP286CompleteActionResponseOperator source current)
        (canonicalP286SpatialGaugeOneForm direction) 0 =
      currentP286SpatialActionTarget source current direction := by
  simpa only [canonicalP286SpatialGaugeOneForm_spatial] using
    currentP286CompleteActionResponseOperator_temporalBFMomentumResponse
      source current coframeOne
        (canonicalP286SpatialGaugeOneForm direction)

/-- Full-direction spatial Gauss response. -/
theorem
    currentP286CompleteActionResponseOperator_spatialBFMomentumResponse
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (coframeOne : ∀ point, current.coframe point = 1)
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionSpatialBFMomentumDivergence
        (currentP286CompleteActionResponseOperator source current)
        direction 0 =
      currentP286TemporalActionTarget source current
        (direction canonicalLorentzianTimeDirection) := by
  unfold p286GaugeConnectionSpatialBFMomentumDivergence
  rw [
    currentP286CompleteActionResponseOperator_bfMomentum_derivative
      source current coframeOne
      (p286GaugeExteriorDerivativeDirection 1 direction) 1,
    currentP286CompleteActionResponseOperator_bfMomentum_derivative
      source current coframeOne
      (p286GaugeExteriorDerivativeDirection 2 direction) 2,
    currentP286CompleteActionResponseOperator_bfMomentum_derivative
      source current coframeOne
      (p286GaugeExteriorDerivativeDirection 3 direction) 3]
  rw [canonicalP286EqualAxisCoefficient_eq_one_third]
  simp only [canonicalLorentzianTimeDirection, Fin.sum_univ_three]
  simp
  rw [show
      p286GaugeAuxiliaryHodgePairingPolynomial 1
          (p286GaussAuxiliaryAxisEmbedding
            (currentP286GaussCharge source current) 0)
          (p286GaugeExteriorDerivativeDirection 1 direction) =
        p286CoordinateLiePairing
          (currentP286GaussCharge source current) (direction 0) by
      simpa [canonicalLorentzianTimeDirection] using
        identityP286GaussAxisMomentum_fullDirection
          (currentP286GaussCharge source current) direction 0,
    show
      p286GaugeAuxiliaryHodgePairingPolynomial 1
          (p286GaussAuxiliaryAxisEmbedding
            (currentP286GaussCharge source current) 1)
          (p286GaugeExteriorDerivativeDirection 2 direction) =
        p286CoordinateLiePairing
          (currentP286GaussCharge source current) (direction 0) by
      simpa [canonicalLorentzianTimeDirection] using
        identityP286GaussAxisMomentum_fullDirection
          (currentP286GaussCharge source current) direction 1,
    show
      p286GaugeAuxiliaryHodgePairingPolynomial 1
          (p286GaussAuxiliaryAxisEmbedding
            (currentP286GaussCharge source current) 2)
          (p286GaugeExteriorDerivativeDirection 3 direction) =
        p286CoordinateLiePairing
          (currentP286GaussCharge source current) (direction 0) by
      simpa [canonicalLorentzianTimeDirection] using
        identityP286GaussAxisMomentum_fullDirection
          (currentP286GaussCharge source current) direction 2]
  calc
    _ = p286CoordinateLiePairing
          (currentP286GaussCharge source current) (direction 0) := by
      ring
    _ = currentP286TemporalActionTarget source current (direction 0) :=
      currentP286GaussCharge_response source current (direction 0)

/-- The temporal-direction restriction used by the canonical Gauss split. -/
theorem
    currentP286CompleteActionResponseOperator_spatialBFMomentumResponse_temporal
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (coframeOne : ∀ point, current.coframe point = 1)
    (component : P286CoordinateCarrier) :
    p286GaugeConnectionSpatialBFMomentumDivergence
        (currentP286CompleteActionResponseOperator source current)
        (p286TemporalGaugeOneForm component) 0 =
      currentP286TemporalActionTarget source current component := by
  simpa only [p286TemporalGaugeOneForm_time] using
    currentP286CompleteActionResponseOperator_spatialBFMomentumResponse
      source current coframeOne (p286TemporalGaugeOneForm component)

theorem p286GaugeOneForm_eq_temporal_add_canonicalSpatial
    (direction : P286GaugeOneForm) :
    direction =
      p286TemporalGaugeOneForm
          (direction canonicalLorentzianTimeDirection) +
        canonicalP286SpatialGaugeOneForm
          (fun index => direction index.succ) := by
  funext formDirection
  refine Fin.cases ?_ (fun index => ?_) formDirection
  · simp [p286TemporalGaugeOneForm,
      canonicalP286SpatialGaugeOneForm,
      canonicalLorentzianTimeDirection]
  · simp [p286TemporalGaugeOneForm,
      canonicalP286SpatialGaugeOneForm_spatial,
      canonicalLorentzianTimeDirection]

theorem currentP286FullActionTarget_decomposition
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (direction : P286GaugeOneForm) :
    currentP286FullActionTarget source current direction =
      currentP286TemporalActionTarget source current
          (direction canonicalLorentzianTimeDirection) +
        currentP286SpatialActionTarget source current
          (fun index => direction index.succ) := by
  calc
    currentP286FullActionTarget source current direction =
        currentP286FullActionTarget source current
          (p286TemporalGaugeOneForm
              (direction canonicalLorentzianTimeDirection) +
            canonicalP286SpatialGaugeOneForm
              (fun index => direction index.succ)) :=
      congrArg (currentP286FullActionTarget source current)
        (p286GaugeOneForm_eq_temporal_add_canonicalSpatial direction)
    _ =
        currentP286FullActionTarget source current
            (p286TemporalGaugeOneForm
              (direction canonicalLorentzianTimeDirection)) +
          currentP286FullActionTarget source current
            (canonicalP286SpatialGaugeOneForm
              (fun index => direction index.succ)) := by
      rw [map_add]
    _ = _ := by
      rw [currentP286TemporalActionTarget_apply,
        currentP286SpatialActionTarget_apply]

/-- Producer consistency: the same current action dual that uniquely
generated the velocity and charge closes the connection equation after its
actual first jet is installed.  It is not an independent constraint. -/
theorem
    currentP286CompleteActionResponseOperator_connectionEquation_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (coframeOne : ∀ point, current.coframe point = 1)
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionEulerLagrangeCoefficient source
        (currentP286CompleteActionResponseOperator source current)
        direction 0 =
      0 := by
  unfold p286GaugeConnectionEulerLagrangeCoefficient
  rw [currentP286CompleteActionResponseOperator_actionCurrent_origin,
    p286GaugeConnectionBFDifferentialMomentumDivergence_eq_temporal_add_spatial,
    currentP286CompleteActionResponseOperator_temporalBFMomentumResponse
      source current coframeOne,
    currentP286CompleteActionResponseOperator_spatialBFMomentumResponse
      source current coframeOne,
    currentP286FullActionTarget_decomposition]
  ring

end

end
  SaturationMonoid.PhysicsCore.StageNineCurrentP286CompleteActionResponseOperator
