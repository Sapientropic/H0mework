import H0mework.Physics.ActionGeneration.P286MomentumJointLocalActualLift
import H0mework.Physics.ActionGeneration.CartanConnectionLocalActualLift

/-!
# S9-C3h118: C3h117 action-generated P286 Gauss actual update

C3h117 lets the C3h116-based actual P286 connection action uniquely generate the
physical-time velocity of the three spatial auxiliary components.  That
closes every spatial connection direction, but a temporal connection
variation is a Gauss constraint: its temporal BF-momentum derivative
vanishes structurally and its charge must be carried by a spatial momentum
divergence.

This module continues the same path-first/action-first construction:

```text
C3h110 complete actual germ
→ actual temporal P286 charge functional
→ unique P286 charge coordinate through the nondegenerate Lie pairing
→ canonical three-axis radial spatial auxiliary profile
→ one actual germ U with both time velocity and spatial Gauss gradient
→ full P286 connection equation at the origin.
```

The radial coefficient is fixed by the three spatial axes.  The constructor
does not import or inspect a residual carrier, zero fiber, quotient, range
certificate, endpoint, supplied charge coordinate, or branch receipt.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP286GaussJointLocalActualLift

open ProofFreeRicherAnholonomicSource
open StageNineBlockwiseConstitutive
open StageNineCanonicalCauchyState
open StageNineCoframeTwoFormPairing
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286ActionCauchySplit
open StageNineP286GaugeAuxiliaryEquation
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionMomentumRegularity
open StageNineP286GaugeConnectionPointwiseEquation
open StageNineP286GaugeConnectionVariation
open StageNineP286ActionVelocityLocalActualLift
open StageNineSourceActionGeneratedCartanConnectionLocalActualLift
open StageNineSourceActionGeneratedP286MomentumJointLocalActualLift
open StageNineSourceGeneratedMatterSpinActionUpdate
open SU7MotherGaugeTheory
open SU7MotherLieAlgebra
open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 200000

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

/-! ## Actual temporal charge and its unique Lie-pairing coordinate -/

private theorem p286TemporalGaugeOneForm_add
    (first second : P286CoordinateCarrier) :
    p286TemporalGaugeOneForm (first + second) =
      p286TemporalGaugeOneForm first +
        p286TemporalGaugeOneForm second := by
  funext direction
  by_cases isTime : direction = canonicalLorentzianTimeDirection
  · simp [p286TemporalGaugeOneForm, isTime]
  · simp [p286TemporalGaugeOneForm, isTime]

private theorem p286TemporalGaugeOneForm_smul
    (parameter : ℝ)
    (component : P286CoordinateCarrier) :
    p286TemporalGaugeOneForm (parameter • component) =
      parameter • p286TemporalGaugeOneForm component := by
  funext direction
  simp [p286TemporalGaugeOneForm, Pi.smul_apply]

/-- The temporal P286 charge read from the already generated C3h110 actual
action.  It is a genuine finite dual, not a residual coordinate. -/
def positiveC3h110P286TemporalGaussActionTarget :
    Module.Dual ℝ P286CoordinateCarrier where
  toFun component :=
    p286GaugeConnectionAlgebraicCurrentCoefficient
      positiveSmoothUnifiedSource
      positiveSourceActionGeneratedP286MomentumJointLocalActualLift
      (p286TemporalGaugeOneForm component) 0
  map_add' := by
    intro first second
    rw [p286TemporalGaugeOneForm_add,
      p286GaugeConnectionAlgebraicCurrentCoefficient_add_action]
  map_smul' := by
    intro parameter component
    rw [p286TemporalGaugeOneForm_smul,
      p286GaugeConnectionAlgebraicCurrentCoefficient_smul_action]
    rfl

/-- The positive P286 Lie pairing as a map from one charge coordinate to its
full real dual. -/
def p286CoordinateLiePairingDualOperator :
    P286CoordinateCarrier →ₗ[ℝ]
      Module.Dual ℝ P286CoordinateCarrier where
  toFun charge :=
    { toFun := fun component =>
        p286CoordinateLiePairing charge component
      map_add' := by
        intro first second
        exact p286CoordinateLiePairing_add_right first second charge
      map_smul' := by
        intro parameter component
        rw [p286CoordinateLiePairing_smul_right]
        rfl }
  map_add' := by
    intro first second
    apply LinearMap.ext
    intro component
    exact p286CoordinateLiePairing_add_left first second component
  map_smul' := by
    intro parameter charge
    apply LinearMap.ext
    intro component
    change
      p286CoordinateLiePairing (parameter • charge) component =
        parameter * p286CoordinateLiePairing charge component
    exact p286CoordinateLiePairing_smul_left parameter charge component

@[simp] theorem p286CoordinateLiePairingDualOperator_apply
    (charge component : P286CoordinateCarrier) :
    p286CoordinateLiePairingDualOperator charge component =
      p286CoordinateLiePairing charge component :=
  rfl

theorem p286CoordinateLiePairingDualOperator_injective :
    Function.Injective p286CoordinateLiePairingDualOperator := by
  intro first second equality
  have responseZero :
      p286CoordinateLiePairingDualOperator (first - second) = 0 := by
    rw [map_sub, equality, sub_self]
  have evaluatedZero :=
    congrArg
      (fun response : Module.Dual ℝ P286CoordinateCarrier =>
        response (first - second))
      responseZero
  simp only [p286CoordinateLiePairingDualOperator_apply,
    LinearMap.zero_apply] at evaluatedZero
  have differenceZero : first - second = 0 :=
    (p286CoordinateLiePairing_self_eq_zero_iff _).mp evaluatedZero
  exact sub_eq_zero.mp differenceZero

theorem p286CoordinateLiePairingDualOperator_surjective :
    Function.Surjective p286CoordinateLiePairingDualOperator := by
  have dimensionEquality :
      Module.finrank ℝ P286CoordinateCarrier =
        Module.finrank ℝ
          (Module.Dual ℝ P286CoordinateCarrier) := by
    exact Subspace.dual_finrank_eq.symm
  apply
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      dimensionEquality).mp
  exact p286CoordinateLiePairingDualOperator_injective

/-- The action pairing is an equivalence, so the charge coordinate is unique
and no caller can choose a preimage branch. -/
noncomputable def p286CoordinateLiePairingEquiv :
    P286CoordinateCarrier ≃ₗ[ℝ]
      Module.Dual ℝ P286CoordinateCarrier :=
  LinearEquiv.ofBijective p286CoordinateLiePairingDualOperator
    ⟨p286CoordinateLiePairingDualOperator_injective,
      p286CoordinateLiePairingDualOperator_surjective⟩

@[simp] theorem p286CoordinateLiePairingEquiv_apply
    (charge : P286CoordinateCarrier) :
    p286CoordinateLiePairingEquiv charge =
      p286CoordinateLiePairingDualOperator charge :=
  rfl

/-- The unique P286 coordinate carrying the actual temporal action charge. -/
def positiveSourceActionGeneratedP286GaussCharge :
    P286CoordinateCarrier :=
  p286CoordinateLiePairingEquiv.symm
    positiveC3h110P286TemporalGaussActionTarget

theorem positiveSourceActionGeneratedP286GaussCharge_response
    (component : P286CoordinateCarrier) :
    p286CoordinateLiePairing positiveSourceActionGeneratedP286GaussCharge
        component =
      positiveC3h110P286TemporalGaussActionTarget component := by
  change
    p286CoordinateLiePairingEquiv
        (p286CoordinateLiePairingEquiv.symm
          positiveC3h110P286TemporalGaussActionTarget) component =
      positiveC3h110P286TemporalGaussActionTarget component
  rw [p286CoordinateLiePairingEquiv.apply_symm_apply]

theorem positiveSourceActionGeneratedP286GaussCharge_unique
    (candidate : P286CoordinateCarrier)
    (response :
      ∀ component,
        p286CoordinateLiePairing candidate component =
          positiveC3h110P286TemporalGaussActionTarget component) :
    candidate = positiveSourceActionGeneratedP286GaussCharge := by
  apply p286CoordinateLiePairingDualOperator_injective
  apply LinearMap.ext
  intro component
  rw [p286CoordinateLiePairingDualOperator_apply,
    p286CoordinateLiePairingDualOperator_apply,
    response,
    positiveSourceActionGeneratedP286GaussCharge_response]

/-! ## Canonical radial Gauss profile -/

/-- Put one charge coordinate in exactly one of the three spatial auxiliary
slots `(23,31,12)`. -/
def p286GaussAuxiliaryAxisEmbedding
    (charge : P286CoordinateCarrier)
    (axis : Fin 3) : P286GaugeTwoForm :=
  p286SpatialAuxiliaryVelocityEmbedding
    (fun candidate => if candidate = axis then charge else 0)

/-- The canonical equal-axis affine spatial profile carried by the three
spatial auxiliary slots `(23,31,12)`.  Each axis carries one third of the
same action-generated charge, so their divergence sums to that charge. -/
def p286GaussRadialAuxiliaryProfile
    (charge : P286CoordinateCarrier)
    (point : BasePoint) : P286GaugeTwoForm :=
  ∑ axis : Fin 3,
    ((1 / 3 : ℝ) * point axis.succ) •
      p286GaussAuxiliaryAxisEmbedding charge axis

@[simp] theorem p286GaussRadialAuxiliaryProfile_origin
    (charge : P286CoordinateCarrier) :
    p286GaussRadialAuxiliaryProfile charge 0 = 0 := by
  funext pair
  simp [p286GaussRadialAuxiliaryProfile]

theorem p286GaussRadialAuxiliaryProfile_contDiff
    (charge : P286CoordinateCarrier)
    (pair : Fin 6) :
    ContDiff ℝ ∞
      (fun point => p286GaussRadialAuxiliaryProfile charge point pair) := by
  unfold p286GaussRadialAuxiliaryProfile
  change
    ContDiff ℝ ∞ fun point : BasePoint =>
      ∑ axis : Fin 3,
        (((1 / 3 : ℝ) * point axis.succ) •
          p286GaussAuxiliaryAxisEmbedding charge axis) pair
  apply ContDiff.sum
  intro axis _
  fun_prop

/-- The complete P286 auxiliary coordinate combines C3h110's generated
physical-time velocity with the action-generated spatial Gauss profile. -/
def positiveSourceActionGeneratedP286GaussAuxiliaryCoordinate
    (point : BasePoint) : P286GaugeTwoForm :=
  point canonicalLorentzianTimeDirection •
      p286SpatialAuxiliaryVelocityEmbedding
        positiveSourceActionGeneratedP286SpatialAuxiliaryVelocity +
    p286GaussRadialAuxiliaryProfile
      positiveSourceActionGeneratedP286GaussCharge point

/-- One complete actual germ carrying both the C3h110 momentum evolution and
the source/action-generated Gauss gradient. -/
def positiveSourceActionGeneratedP286GaussJointLocalActualLift :
    StageNineHolonomicConfiguration :=
  { positiveC3h109Actual with
    gaugeAuxiliary := fun point pair =>
      p286CoordinateEquiv.symm
        (positiveSourceActionGeneratedP286GaussAuxiliaryCoordinate point pair) }

theorem positiveSourceActionGeneratedP286GaussJointLocalActualLift_smooth :
    positiveSourceActionGeneratedP286GaussJointLocalActualLift.Smooth := by
  rcases positiveC3h109Actual_smooth with
    ⟨coframe, gravityConnection, gravityAuxiliary, multiplier,
      gaugeConnection, _gaugeAuxiliary, scalar, matter, conjugate⟩
  exact
    ⟨coframe, gravityConnection, gravityAuxiliary, multiplier,
      gaugeConnection, fun pair => by
        have timeSmooth :
            ContDiff ℝ ∞ fun point : BasePoint =>
              point canonicalLorentzianTimeDirection •
                p286SpatialAuxiliaryVelocityEmbedding
                  positiveSourceActionGeneratedP286SpatialAuxiliaryVelocity
                  pair := by
          simpa only [localBaseCoordinate_apply] using
            ((localBaseCoordinate canonicalLorentzianTimeDirection).contDiff
              |>.smul_const
                (p286SpatialAuxiliaryVelocityEmbedding
                  positiveSourceActionGeneratedP286SpatialAuxiliaryVelocity
                  pair))
        have radialSmooth :=
          p286GaussRadialAuxiliaryProfile_contDiff
            positiveSourceActionGeneratedP286GaussCharge pair
        simpa only [
          positiveSourceActionGeneratedP286GaussJointLocalActualLift,
          positiveSourceActionGeneratedP286GaussAuxiliaryCoordinate,
          p286CoordinateEquiv.apply_symm_apply, Pi.add_apply,
          Pi.smul_apply] using
          timeSmooth.add radialSmooth,
      scalar, matter, conjugate⟩

theorem
    positiveSourceActionGeneratedP286GaussJointLocalActualLift_nondegenerate :
    positiveSourceActionGeneratedP286GaussJointLocalActualLift.Nondegenerate :=
  positiveC3h109Actual_nondegenerate

@[simp] theorem
    positiveSourceActionGeneratedP286GaussJointLocalActualLift_gaugeAuxiliary_origin :
    positiveSourceActionGeneratedP286GaussJointLocalActualLift.gaugeAuxiliary
        0 =
      0 := by
  funext pair
  apply p286CoordinateEquiv.injective
  simp [positiveSourceActionGeneratedP286GaussJointLocalActualLift,
    positiveSourceActionGeneratedP286GaussAuxiliaryCoordinate]

/-! ## Forward BF-momentum differentiation -/

private theorem p286GaugeAuxiliaryHodgePairingPolynomial_add_left
    (coframe : LorentzianCoframe)
    (first second residual : P286GaugeTwoForm) :
    p286GaugeAuxiliaryHodgePairingPolynomial coframe
        (first + second) residual =
      p286GaugeAuxiliaryHodgePairingPolynomial coframe first residual +
        p286GaugeAuxiliaryHodgePairingPolynomial coframe second residual := by
  unfold p286GaugeAuxiliaryHodgePairingPolynomial
  rw [liftGaugeTwoFormOperator_add_p286]
  simp_rw [Pi.add_apply, p286CoordinateLiePairing_add_left]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]

private theorem p286GaugeAuxiliaryHodgePairingPolynomial_smul_left
    (coframe : LorentzianCoframe)
    (parameter : ℝ)
    (first residual : P286GaugeTwoForm) :
    p286GaugeAuxiliaryHodgePairingPolynomial coframe
        (parameter • first) residual =
      parameter *
        p286GaugeAuxiliaryHodgePairingPolynomial coframe first residual := by
  unfold p286GaugeAuxiliaryHodgePairingPolynomial
  rw [liftGaugeTwoFormOperator_smul_p286]
  simp_rw [Pi.smul_apply, p286CoordinateLiePairing_smul_left]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro pair _
  ring

private def p286GaugeAuxiliaryHodgePairingLinear
    (coframe : LorentzianCoframe)
    (residual : P286GaugeTwoForm) :
    P286GaugeTwoForm →ₗ[ℝ] ℝ where
  toFun first :=
    p286GaugeAuxiliaryHodgePairingPolynomial coframe first residual
  map_add' := fun first second =>
    p286GaugeAuxiliaryHodgePairingPolynomial_add_left coframe
      first second residual
  map_smul' := by
    intro parameter first
    simpa [smul_eq_mul] using
      p286GaugeAuxiliaryHodgePairingPolynomial_smul_left
        coframe parameter first residual

@[simp] private theorem p286GaugeAuxiliaryHodgePairingLinear_apply
    (coframe : LorentzianCoframe)
    (residual first : P286GaugeTwoForm) :
    p286GaugeAuxiliaryHodgePairingLinear coframe residual first =
      p286GaugeAuxiliaryHodgePairingPolynomial coframe first residual :=
  rfl

/-- Constant-auxiliary proof scaffold.  It is used only as the coefficient of
one affine coordinate in the derivative calculation. -/
private def positiveC3h109ConstantGaussAuxiliaryActual
    (auxiliary : P286GaugeTwoForm) :
    StageNineHolonomicConfiguration :=
  { positiveC3h109Actual with
    gaugeAuxiliary := fun _ pair =>
      p286CoordinateEquiv.symm (auxiliary pair) }

private theorem positiveC3h109ConstantGaussAuxiliaryActual_smooth
    (auxiliary : P286GaugeTwoForm) :
    (positiveC3h109ConstantGaussAuxiliaryActual auxiliary).Smooth := by
  rcases positiveC3h109Actual_smooth with
    ⟨coframe, gravityConnection, gravityAuxiliary, multiplier,
      gaugeConnection, _gaugeAuxiliary, scalar, matter, conjugate⟩
  exact
    ⟨coframe, gravityConnection, gravityAuxiliary, multiplier,
      gaugeConnection, fun pair => by
        simpa only [positiveC3h109ConstantGaussAuxiliaryActual,
          p286CoordinateEquiv.apply_symm_apply] using
          (contDiff_const :
            ContDiff ℝ ∞ fun _ : BasePoint => auxiliary pair),
      scalar, matter, conjugate⟩

private theorem
    positiveC3h109ConstantGaussAuxiliaryActual_nondegenerate
    (auxiliary : P286GaugeTwoForm) :
    (positiveC3h109ConstantGaussAuxiliaryActual auxiliary).Nondegenerate :=
  positiveC3h109Actual_nondegenerate

/-- The generated actual BF momentum is the already generated C3h110 path
plus the three affine spatial Gauss-path contributions. -/
private theorem
    positiveSourceActionGeneratedP286GaussJointLocalActualLift_momentum_factor
    (direction : P286GaugeTwoForm)
    (point : BasePoint) :
    p286GaugeConnectionBFDifferentialMomentum
        positiveSourceActionGeneratedP286GaussJointLocalActualLift
        direction point =
      p286GaugeConnectionBFDifferentialMomentum
          positiveSourceActionGeneratedP286MomentumJointLocalActualLift
          direction point +
        ∑ axis : Fin 3,
          ((1 / 3 : ℝ) * point axis.succ) *
            p286GaugeConnectionBFDifferentialMomentum
              (positiveC3h109ConstantGaussAuxiliaryActual
                (p286GaussAuxiliaryAxisEmbedding
                  positiveSourceActionGeneratedP286GaussCharge axis))
              direction point := by
  unfold p286GaugeConnectionBFDifferentialMomentum generatedVolumeDensity
  unfold holonomicP286GaugeAuxiliaryCoordinate
  simp only [
    positiveSourceActionGeneratedP286GaussJointLocalActualLift,
    positiveSourceActionGeneratedP286MomentumJointLocalActualLift,
    positiveC3h109TimeLinearAuxiliaryActual,
    positiveC3h109ConstantGaussAuxiliaryActual,
    toContinuumPointField, p286CoordinateEquiv.apply_symm_apply]
  change
    abs (Matrix.det (positiveC3h109Actual.coframe point)) *
        p286GaugeAuxiliaryHodgePairingLinear
          (positiveC3h109Actual.coframe point) direction
          (positiveSourceActionGeneratedP286GaussAuxiliaryCoordinate point) =
      _
  rw [positiveSourceActionGeneratedP286GaussAuxiliaryCoordinate,
    map_add, p286GaussRadialAuxiliaryProfile, map_sum]
  simp only [map_smul, smul_eq_mul,
    p286GaugeAuxiliaryHodgePairingLinear_apply]
  rw [mul_add, Finset.mul_sum]
  apply congrArg₂ (fun first second : ℝ => first + second)
  · change
      _ =
        abs (Matrix.det (positiveC3h109Actual.coframe point)) *
          p286GaugeAuxiliaryHodgePairingPolynomial
            (positiveC3h109Actual.coframe point)
            (point canonicalLorentzianTimeDirection •
              p286SpatialAuxiliaryVelocityEmbedding
                positiveSourceActionGeneratedP286SpatialAuxiliaryVelocity)
            direction
    rw [p286GaugeAuxiliaryHodgePairingPolynomial_smul_left]
  · apply Finset.sum_congr rfl
    intro axis _
    ring

private theorem liftGaugeTwoFormOperator_id_p286_local
    (form : P286GaugeTwoForm) :
    liftGaugeTwoFormOperator
        (LinearMap.id : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm) form =
      form := by
  funext pair
  rw [WithLp.ext_iff]
  funext internal
  rw [liftGaugeTwoFormOperator_p286Coordinate_apply]
  fin_cases pair <;> simp

private theorem liftGaugeTwoFormOperator_fixedHodge_apply_local
    (form : P286GaugeTwoForm)
    (pair : Fin 6) :
    liftGaugeTwoFormOperator lorentzianCoframeHodge form pair =
      ![form 3, form 4, form 5, -form 0, -form 1, -form 2] pair := by
  rw [WithLp.ext_iff]
  funext internal
  rw [liftGaugeTwoFormOperator_p286Coordinate_apply]
  fin_cases pair <;> rfl

private theorem identityP286GaussAxisMomentum_normalForm
    (charge component : P286CoordinateCarrier)
    (axis : Fin 3) :
    p286GaugeAuxiliaryHodgePairingPolynomial 1
        (p286GaussAuxiliaryAxisEmbedding charge axis)
        (p286GaugeExteriorDerivativeDirection axis.succ
          (p286TemporalGaugeOneForm component)) =
      p286CoordinateLiePairing charge component := by
  unfold p286GaugeAuxiliaryHodgePairingPolynomial
  rw [coframeTwoFormLinear_one]
  simp_rw [liftGaugeTwoFormOperator_id_p286_local]
  rw [Fin.sum_univ_six]
  fin_cases axis <;>
    simp [p286GaussAuxiliaryAxisEmbedding,
      p286SpatialAuxiliaryVelocityEmbedding,
      p286GaugeExteriorDerivativeDirection,
      p286TemporalGaugeOneForm, canonicalLorentzianTimeDirection,
      liftGaugeTwoFormOperator_fixedHodge_apply_local,
      lorentzianTwoFormSign, minkowskiInternalSign,
      pairFirst, pairSecond]

private theorem positiveC3h109ConstantGaussAuxiliaryMomentum_origin
    (charge component : P286CoordinateCarrier)
    (axis : Fin 3) :
    p286GaugeConnectionBFDifferentialMomentum
        (positiveC3h109ConstantGaussAuxiliaryActual
          (p286GaussAuxiliaryAxisEmbedding charge axis))
        (p286GaugeExteriorDerivativeDirection axis.succ
          (p286TemporalGaugeOneForm component))
        0 =
      p286CoordinateLiePairing charge component := by
  unfold p286GaugeConnectionBFDifferentialMomentum generatedVolumeDensity
  unfold holonomicP286GaugeAuxiliaryCoordinate
  simp only [positiveC3h109ConstantGaussAuxiliaryActual,
    toContinuumPointField, p286CoordinateEquiv.apply_symm_apply]
  rw [show positiveC3h109Actual.coframe 0 = 1 by
    exact
      positiveSourceActionGeneratedCartanConnectionLocalActualLift_coframe 0]
  simp only [Matrix.det_one, abs_one, one_mul]
  exact identityP286GaussAxisMomentum_normalForm charge component axis

private theorem fieldDirectionalDerivative_add_real_local
    (first second : BasePoint → ℝ)
    (firstSmooth : ContDiff ℝ ∞ first)
    (secondSmooth : ContDiff ℝ ∞ second)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative (first + second) 0 direction =
      fieldDirectionalDerivative first 0 direction +
        fieldDirectionalDerivative second 0 direction := by
  change
    fieldDirectionalDerivative
        (fun point => first point + second point) 0 direction =
      _
  unfold fieldDirectionalDerivative
  rw [fderiv_fun_add
    (firstSmooth.differentiable (by simp) 0)
    (secondSmooth.differentiable (by simp) 0)]
  rfl

private theorem fieldDirectionalDerivative_finset_sum_real_local
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

private theorem fieldDirectionalDerivative_spatialCoordinate_mul
    (coefficient : BasePoint → ℝ)
    (coefficientSmooth : ContDiff ℝ ∞ coefficient)
    (axis : Fin 3)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          ((1 / 3 : ℝ) * point axis.succ) * coefficient point)
        0 direction =
      if axis.succ = direction then
        (1 / 3 : ℝ) * coefficient 0
      else
        0 := by
  let spatialCoordinate := localBaseCoordinate axis.succ
  have spatialDifferentiable :
      DifferentiableAt ℝ spatialCoordinate 0 :=
    spatialCoordinate.differentiable.differentiableAt
  have scaledDifferentiable :
      DifferentiableAt ℝ
        (fun point => (1 / 3 : ℝ) * spatialCoordinate point) 0 :=
    by fun_prop
  unfold fieldDirectionalDerivative
  change
    fderiv ℝ
        (fun point =>
          ((1 / 3 : ℝ) * spatialCoordinate point) * coefficient point)
        0 (coordinateDirection direction) =
      _
  rw [fderiv_fun_mul scaledDifferentiable
    ((coefficientSmooth.differentiable (by simp)).differentiableAt),
    fderiv_const_mul spatialDifferentiable (1 / 3 : ℝ),
    spatialCoordinate.hasFDerivAt.fderiv]
  by_cases sameDirection : axis.succ = direction
  · subst direction
    simp [spatialCoordinate, localBaseCoordinate, coordinateDirection]
    ring
  · simp [spatialCoordinate, localBaseCoordinate, coordinateDirection,
      sameDirection]

private def positiveP286GaussAxisConstantMomentum
    (direction : P286GaugeTwoForm)
    (axis : Fin 3) : BasePoint → ℝ :=
  p286GaugeConnectionBFDifferentialMomentum
    (positiveC3h109ConstantGaussAuxiliaryActual
      (p286GaussAuxiliaryAxisEmbedding
        positiveSourceActionGeneratedP286GaussCharge axis))
    direction

private theorem positiveP286GaussAxisConstantMomentum_contDiff
    (direction : P286GaugeTwoForm)
    (axis : Fin 3) :
    ContDiff ℝ ∞
      (positiveP286GaussAxisConstantMomentum direction axis) := by
  exact
    p286GaugeConnectionBFDifferentialMomentum_contDiff
      (positiveC3h109ConstantGaussAuxiliaryActual
        (p286GaussAuxiliaryAxisEmbedding
          positiveSourceActionGeneratedP286GaussCharge axis))
      (positiveC3h109ConstantGaussAuxiliaryActual_smooth _)
      (positiveC3h109ConstantGaussAuxiliaryActual_nondegenerate _)
      direction

/-- Differentiating the actual action momentum along any coordinate first
differentiates the existing C3h110 path and then the three canonical spatial
path factors. -/
private theorem
    positiveSourceActionGeneratedP286GaussJointLocalActualLift_momentumDerivative_origin
    (direction : P286GaugeTwoForm)
    (derivativeDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (p286GaugeConnectionBFDifferentialMomentum
          positiveSourceActionGeneratedP286GaussJointLocalActualLift
          direction)
        0 derivativeDirection =
      fieldDirectionalDerivative
          (p286GaugeConnectionBFDifferentialMomentum
            positiveSourceActionGeneratedP286MomentumJointLocalActualLift
            direction)
          0 derivativeDirection +
        ∑ axis : Fin 3,
          if axis.succ = derivativeDirection then
            (1 / 3 : ℝ) *
              positiveP286GaussAxisConstantMomentum direction axis 0
          else
            0 := by
  let baseMomentum :=
    p286GaugeConnectionBFDifferentialMomentum
      positiveSourceActionGeneratedP286MomentumJointLocalActualLift direction
  let summand : Fin 3 → BasePoint → ℝ := fun axis point =>
    ((1 / 3 : ℝ) * point axis.succ) *
      positiveP286GaussAxisConstantMomentum direction axis point
  have baseSmooth : ContDiff ℝ ∞ baseMomentum :=
    p286GaugeConnectionBFDifferentialMomentum_contDiff
      positiveSourceActionGeneratedP286MomentumJointLocalActualLift
      positiveSourceActionGeneratedP286MomentumJointLocalActualLift_smooth
      positiveSourceActionGeneratedP286MomentumJointLocalActualLift_nondegenerate
      direction
  have summandSmooth (axis : Fin 3) :
      ContDiff ℝ ∞ (summand axis) := by
    exact
      (contDiff_const.mul (localBaseCoordinate axis.succ).contDiff).mul
        (positiveP286GaussAxisConstantMomentum_contDiff direction axis)
  have sumSmooth :
      ContDiff ℝ ∞ (fun point => ∑ axis : Fin 3, summand axis point) := by
    apply ContDiff.sum
    intro axis _
    exact summandSmooth axis
  have momentumEquality :
      p286GaugeConnectionBFDifferentialMomentum
          positiveSourceActionGeneratedP286GaussJointLocalActualLift
          direction =
        baseMomentum + fun point => ∑ axis : Fin 3, summand axis point := by
    funext point
    exact
      positiveSourceActionGeneratedP286GaussJointLocalActualLift_momentum_factor
        direction point
  rw [momentumEquality,
    fieldDirectionalDerivative_add_real_local
      baseMomentum (fun point => ∑ axis : Fin 3, summand axis point)
      baseSmooth sumSmooth derivativeDirection,
    fieldDirectionalDerivative_finset_sum_real_local
      summand summandSmooth derivativeDirection]
  apply congrArg₂ (fun first second : ℝ => first + second) rfl
  apply Finset.sum_congr rfl
  intro axis _
  exact
    fieldDirectionalDerivative_spatialCoordinate_mul
      (positiveP286GaussAxisConstantMomentum direction axis)
      (positiveP286GaussAxisConstantMomentum_contDiff direction axis)
      axis derivativeDirection

/-- The spatial divergence of the new actual is the C3h110 divergence plus
the forward response of the three action-generated Gauss path factors. -/
private theorem
    positiveSourceActionGeneratedP286GaussJointLocalActualLift_spatialDivergence_origin
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionSpatialBFMomentumDivergence
        positiveSourceActionGeneratedP286GaussJointLocalActualLift
        direction 0 =
      p286GaugeConnectionSpatialBFMomentumDivergence
          positiveSourceActionGeneratedP286MomentumJointLocalActualLift
          direction 0 +
        ∑ axis : Fin 3,
          (1 / 3 : ℝ) *
            positiveP286GaussAxisConstantMomentum
              (p286GaugeExteriorDerivativeDirection axis.succ direction)
              axis 0 := by
  unfold p286GaugeConnectionSpatialBFMomentumDivergence
  rw [
    positiveSourceActionGeneratedP286GaussJointLocalActualLift_momentumDerivative_origin
      (p286GaugeExteriorDerivativeDirection 1 direction) 1,
    positiveSourceActionGeneratedP286GaussJointLocalActualLift_momentumDerivative_origin
      (p286GaugeExteriorDerivativeDirection 2 direction) 2,
    positiveSourceActionGeneratedP286GaussJointLocalActualLift_momentumDerivative_origin
      (p286GaugeExteriorDerivativeDirection 3 direction) 3]
  simp_rw [Fin.sum_univ_three]
  simp
  ring

/-- On a temporal connection test, the three spatial action paths sum to the
unique action-generated charge coordinate. -/
theorem
    positiveSourceActionGeneratedP286GaussJointLocalActualLift_spatialDivergence_temporal
    (component : P286CoordinateCarrier) :
    p286GaugeConnectionSpatialBFMomentumDivergence
        positiveSourceActionGeneratedP286GaussJointLocalActualLift
        (p286TemporalGaugeOneForm component) 0 =
      p286CoordinateLiePairing
        positiveSourceActionGeneratedP286GaussCharge component := by
  rw [
    positiveSourceActionGeneratedP286GaussJointLocalActualLift_spatialDivergence_origin,
    positiveSourceActionGeneratedP286MomentumJointLocalActualLift_spatialDivergence_zero_allDirections,
    zero_add]
  unfold positiveP286GaussAxisConstantMomentum
  simp_rw [positiveC3h109ConstantGaussAuxiliaryMomentum_origin]
  rw [Fin.sum_univ_three]
  ring

private theorem
    positiveSourceActionGeneratedP286GaussJointLocalActualLift_pointField_origin :
    toContinuumPointField
        positiveSourceActionGeneratedP286GaussJointLocalActualLift 0 =
      toContinuumPointField
        positiveSourceActionGeneratedP286MomentumJointLocalActualLift 0 := by
  apply StageNineContinuumPointField.ext
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · change
      positiveSourceActionGeneratedP286GaussJointLocalActualLift.gaugeAuxiliary
          0 =
        positiveSourceActionGeneratedP286MomentumJointLocalActualLift.gaugeAuxiliary
          0
    rw [
      positiveSourceActionGeneratedP286GaussJointLocalActualLift_gaugeAuxiliary_origin,
      positiveSourceActionGeneratedP286MomentumJointLocalActualLift_gaugeAuxiliary_origin]
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem
    positiveSourceActionGeneratedP286GaussJointLocalActualLift_actionCurrent_origin
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionAlgebraicCurrentCoefficient
        positiveSmoothUnifiedSource
        positiveSourceActionGeneratedP286GaussJointLocalActualLift
        direction 0 =
      p286GaugeConnectionAlgebraicCurrentCoefficient
        positiveSmoothUnifiedSource
        positiveSourceActionGeneratedP286MomentumJointLocalActualLift
        direction 0 := by
  unfold p286GaugeConnectionAlgebraicCurrentCoefficient
  rw [
    positiveSourceActionGeneratedP286GaussJointLocalActualLift_pointField_origin]
  rfl

/-- The source and actual P286 action generate a complete local germ whose
spatial momentum divergence carries the temporal Gauss current. -/
theorem
    positiveSourceActionGeneratedP286GaussJointLocalActualLift_satisfies_gauss :
    CanonicalP286GaugeGaussConstraintAt
      positiveSmoothUnifiedSource
      positiveSourceActionGeneratedP286GaussJointLocalActualLift
      0 := by
  intro component
  rw [
    positiveSourceActionGeneratedP286GaussJointLocalActualLift_actionCurrent_origin,
    positiveSourceActionGeneratedP286GaussJointLocalActualLift_spatialDivergence_temporal]
  change
    positiveC3h110P286TemporalGaussActionTarget component =
      p286CoordinateLiePairing
        positiveSourceActionGeneratedP286GaussCharge component
  exact
    (positiveSourceActionGeneratedP286GaussCharge_response component).symm

private theorem
    positiveSourceActionGeneratedP286GaussJointLocalActualLift_temporalBFMomentumDerivative_origin_eq
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionTemporalBFMomentumDerivative
        positiveSourceActionGeneratedP286GaussJointLocalActualLift
        direction 0 =
      p286GaugeConnectionTemporalBFMomentumDerivative
        positiveSourceActionGeneratedP286MomentumJointLocalActualLift
        direction 0 := by
  unfold p286GaugeConnectionTemporalBFMomentumDerivative
  rw [
    positiveSourceActionGeneratedP286GaussJointLocalActualLift_momentumDerivative_origin]
  simp [canonicalLorentzianTimeDirection]

private theorem identityP286GaussAxisMomentum_spatial_zero
    (charge : P286CoordinateCarrier)
    (direction : P286GaugeOneForm)
    (directionTimeZero :
      direction canonicalLorentzianTimeDirection = 0)
    (axis : Fin 3) :
    p286GaugeAuxiliaryHodgePairingPolynomial 1
        (p286GaussAuxiliaryAxisEmbedding charge axis)
        (p286GaugeExteriorDerivativeDirection axis.succ direction) =
      0 := by
  have directionZero : direction 0 = 0 := by
    simpa [canonicalLorentzianTimeDirection] using directionTimeZero
  unfold p286GaugeAuxiliaryHodgePairingPolynomial
  rw [coframeTwoFormLinear_one]
  simp_rw [liftGaugeTwoFormOperator_id_p286_local]
  rw [Fin.sum_univ_six]
  fin_cases axis <;>
    simp [p286GaussAuxiliaryAxisEmbedding,
      p286SpatialAuxiliaryVelocityEmbedding,
      p286GaugeExteriorDerivativeDirection,
      directionZero,
      liftGaugeTwoFormOperator_fixedHodge_apply_local,
      lorentzianTwoFormSign, minkowskiInternalSign,
      pairFirst, pairSecond]

private theorem positiveC3h109ConstantGaussAuxiliaryMomentum_spatial_zero
    (charge : P286CoordinateCarrier)
    (direction : P286GaugeOneForm)
    (directionTimeZero :
      direction canonicalLorentzianTimeDirection = 0)
    (axis : Fin 3) :
    p286GaugeConnectionBFDifferentialMomentum
        (positiveC3h109ConstantGaussAuxiliaryActual
          (p286GaussAuxiliaryAxisEmbedding charge axis))
        (p286GaugeExteriorDerivativeDirection axis.succ direction)
        0 =
      0 := by
  unfold p286GaugeConnectionBFDifferentialMomentum generatedVolumeDensity
  unfold holonomicP286GaugeAuxiliaryCoordinate
  simp only [positiveC3h109ConstantGaussAuxiliaryActual,
    toContinuumPointField, p286CoordinateEquiv.apply_symm_apply]
  rw [show positiveC3h109Actual.coframe 0 = 1 by
    exact
      positiveSourceActionGeneratedCartanConnectionLocalActualLift_coframe 0]
  simp only [Matrix.det_one, abs_one, one_mul]
  exact
    identityP286GaussAxisMomentum_spatial_zero
      charge direction directionTimeZero axis

private theorem
    positiveSourceActionGeneratedP286GaussJointLocalActualLift_spatialDivergence_spatial_eq
    (direction : P286GaugeOneForm)
    (directionTimeZero :
      direction canonicalLorentzianTimeDirection = 0) :
    p286GaugeConnectionSpatialBFMomentumDivergence
        positiveSourceActionGeneratedP286GaussJointLocalActualLift
        direction 0 =
      p286GaugeConnectionSpatialBFMomentumDivergence
        positiveSourceActionGeneratedP286MomentumJointLocalActualLift
        direction 0 := by
  rw [
    positiveSourceActionGeneratedP286GaussJointLocalActualLift_spatialDivergence_origin]
  unfold positiveP286GaussAxisConstantMomentum
  simp_rw [
    positiveC3h109ConstantGaussAuxiliaryMomentum_spatial_zero
      positiveSourceActionGeneratedP286GaussCharge direction
      directionTimeZero]
  simp

/-- The spatial P286 momentum evolution generated in C3h117 survives in the
same actual germ after the Gauss path has been installed. -/
theorem
    positiveSourceActionGeneratedP286GaussJointLocalActualLift_satisfies_spatialActionLaw :
    CanonicalP286GaugeSpatialMomentumEvolutionAt
      positiveSmoothUnifiedSource
      positiveSourceActionGeneratedP286GaussJointLocalActualLift
      0 := by
  intro direction directionTimeZero
  rw [
    positiveSourceActionGeneratedP286GaussJointLocalActualLift_temporalBFMomentumDerivative_origin_eq,
    positiveSourceActionGeneratedP286GaussJointLocalActualLift_actionCurrent_origin,
    positiveSourceActionGeneratedP286GaussJointLocalActualLift_spatialDivergence_spatial_eq
      direction directionTimeZero]
  exact
    positiveSourceActionGeneratedP286MomentumJointLocalActualLift_satisfies_actionLaw
      direction directionTimeZero

private theorem p286GaugeExteriorDerivativeDirection_add_local
    (derivativeDirection : LorentzianIndex)
    (first second : P286GaugeOneForm) :
    p286GaugeExteriorDerivativeDirection derivativeDirection
        (first + second) =
      p286GaugeExteriorDerivativeDirection derivativeDirection first +
        p286GaugeExteriorDerivativeDirection derivativeDirection second := by
  funext pair
  unfold p286GaugeExteriorDerivativeDirection
  simp only [Pi.add_apply]
  split_ifs <;> module

private theorem
    positiveSourceActionGeneratedP286GaussJointLocalActualLift_momentum_add
    (first second : P286GaugeTwoForm) :
    p286GaugeConnectionBFDifferentialMomentum
        positiveSourceActionGeneratedP286GaussJointLocalActualLift
        (first + second) =
      p286GaugeConnectionBFDifferentialMomentum
          positiveSourceActionGeneratedP286GaussJointLocalActualLift first +
        p286GaugeConnectionBFDifferentialMomentum
          positiveSourceActionGeneratedP286GaussJointLocalActualLift
          second := by
  funext point
  change
    p286GaugeConnectionBFDifferentialMomentum
        positiveSourceActionGeneratedP286GaussJointLocalActualLift
        (first + second) point =
      p286GaugeConnectionBFDifferentialMomentum
          positiveSourceActionGeneratedP286GaussJointLocalActualLift first
          point +
        p286GaugeConnectionBFDifferentialMomentum
          positiveSourceActionGeneratedP286GaussJointLocalActualLift second
          point
  rw [
    p286GaugeConnectionBFDifferentialMomentum_eq_density
      positiveSourceActionGeneratedP286GaussJointLocalActualLift
      positiveSourceActionGeneratedP286GaussJointLocalActualLift_nondegenerate,
    p286GaugeConnectionBFDifferentialMomentum_eq_density
      positiveSourceActionGeneratedP286GaussJointLocalActualLift
      positiveSourceActionGeneratedP286GaussJointLocalActualLift_nondegenerate,
    p286GaugeConnectionBFDifferentialMomentum_eq_density
      positiveSourceActionGeneratedP286GaussJointLocalActualLift
      positiveSourceActionGeneratedP286GaussJointLocalActualLift_nondegenerate,
    p286GaugeBFCurvatureIncrementDensity_add]
  ring

private theorem
    positiveSourceActionGeneratedP286GaussJointLocalActualLift_divergence_add_origin
    (first second : P286GaugeOneForm) :
    p286GaugeConnectionBFDifferentialMomentumDivergence
        positiveSourceActionGeneratedP286GaussJointLocalActualLift
        (first + second) 0 =
      p286GaugeConnectionBFDifferentialMomentumDivergence
          positiveSourceActionGeneratedP286GaussJointLocalActualLift first 0 +
        p286GaugeConnectionBFDifferentialMomentumDivergence
          positiveSourceActionGeneratedP286GaussJointLocalActualLift
          second 0 := by
  have derivativeAdd (derivativeDirection : LorentzianIndex) :
      fieldDirectionalDerivative
          (p286GaugeConnectionBFDifferentialMomentum
            positiveSourceActionGeneratedP286GaussJointLocalActualLift
            (p286GaugeExteriorDerivativeDirection derivativeDirection
              (first + second)))
          0 derivativeDirection =
        fieldDirectionalDerivative
            (p286GaugeConnectionBFDifferentialMomentum
              positiveSourceActionGeneratedP286GaussJointLocalActualLift
              (p286GaugeExteriorDerivativeDirection derivativeDirection
                first))
            0 derivativeDirection +
          fieldDirectionalDerivative
            (p286GaugeConnectionBFDifferentialMomentum
              positiveSourceActionGeneratedP286GaussJointLocalActualLift
              (p286GaugeExteriorDerivativeDirection derivativeDirection
                second))
            0 derivativeDirection := by
    rw [p286GaugeExteriorDerivativeDirection_add_local,
      positiveSourceActionGeneratedP286GaussJointLocalActualLift_momentum_add]
    exact
      fieldDirectionalDerivative_add_real_local _ _
        (p286GaugeConnectionBFDifferentialMomentum_contDiff
          positiveSourceActionGeneratedP286GaussJointLocalActualLift
          positiveSourceActionGeneratedP286GaussJointLocalActualLift_smooth
          positiveSourceActionGeneratedP286GaussJointLocalActualLift_nondegenerate
          _)
        (p286GaugeConnectionBFDifferentialMomentum_contDiff
          positiveSourceActionGeneratedP286GaussJointLocalActualLift
          positiveSourceActionGeneratedP286GaussJointLocalActualLift_smooth
          positiveSourceActionGeneratedP286GaussJointLocalActualLift_nondegenerate
          _)
        derivativeDirection
  unfold p286GaugeConnectionBFDifferentialMomentumDivergence
  simp_rw [derivativeAdd]
  rw [Finset.sum_add_distrib]

private theorem
    positiveSourceActionGeneratedP286GaussJointLocalActualLift_euler_add_origin
    (first second : P286GaugeOneForm) :
    p286GaugeConnectionEulerLagrangeCoefficient
        positiveSmoothUnifiedSource
        positiveSourceActionGeneratedP286GaussJointLocalActualLift
        (first + second) 0 =
      p286GaugeConnectionEulerLagrangeCoefficient
          positiveSmoothUnifiedSource
          positiveSourceActionGeneratedP286GaussJointLocalActualLift
          first 0 +
        p286GaugeConnectionEulerLagrangeCoefficient
          positiveSmoothUnifiedSource
          positiveSourceActionGeneratedP286GaussJointLocalActualLift
          second 0 := by
  unfold p286GaugeConnectionEulerLagrangeCoefficient
  rw [p286GaugeConnectionAlgebraicCurrentCoefficient_add_action,
    positiveSourceActionGeneratedP286GaussJointLocalActualLift_divergence_add_origin]
  ring

private theorem
    positiveSourceActionGeneratedP286GaussJointLocalActualLift_temporalEuler_origin
    (component : P286CoordinateCarrier) :
    p286GaugeConnectionEulerLagrangeCoefficient
        positiveSmoothUnifiedSource
        positiveSourceActionGeneratedP286GaussJointLocalActualLift
        (p286TemporalGaugeOneForm component) 0 =
      0 := by
  unfold p286GaugeConnectionEulerLagrangeCoefficient
  rw [
    p286GaugeConnectionBFDifferentialMomentumDivergence_eq_temporal_add_spatial,
    p286GaugeConnectionTemporalBFMomentumDerivative_temporal_eq_zero
      positiveSourceActionGeneratedP286GaussJointLocalActualLift
      positiveSourceActionGeneratedP286GaussJointLocalActualLift_nondegenerate]
  rw [zero_add]
  exact
    sub_eq_zero.mpr
      (positiveSourceActionGeneratedP286GaussJointLocalActualLift_satisfies_gauss
        component)

private theorem
    positiveSourceActionGeneratedP286GaussJointLocalActualLift_spatialEuler_origin
    (direction : P286GaugeOneForm)
    (directionTimeZero :
      direction canonicalLorentzianTimeDirection = 0) :
    p286GaugeConnectionEulerLagrangeCoefficient
        positiveSmoothUnifiedSource
        positiveSourceActionGeneratedP286GaussJointLocalActualLift
        direction 0 =
      0 := by
  unfold p286GaugeConnectionEulerLagrangeCoefficient
  rw [
    p286GaugeConnectionBFDifferentialMomentumDivergence_eq_temporal_add_spatial]
  have evolution :=
    positiveSourceActionGeneratedP286GaussJointLocalActualLift_satisfies_spatialActionLaw
      direction directionTimeZero
  linarith

/-- Frontier theorem: the proof-free source and the actual P286 dynamics
first generate one local actual germ `U`; that same `U` then satisfies the
complete P286 connection Euler--Lagrange response at the origin.  No
residual coordinate participates in the constructor. -/
theorem
    positiveSourceActionGeneratedP286GaussJointLocalActualLift_connectionEquation_origin
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionEulerLagrangeCoefficient
        positiveSmoothUnifiedSource
        positiveSourceActionGeneratedP286GaussJointLocalActualLift
        direction 0 =
      0 := by
  rw [p286GaugeOneForm_eq_temporal_add_spatial direction,
    positiveSourceActionGeneratedP286GaussJointLocalActualLift_euler_add_origin,
    show
      p286GaugeConnectionEulerLagrangeCoefficient
          positiveSmoothUnifiedSource
          positiveSourceActionGeneratedP286GaussJointLocalActualLift
          (p286TemporalGaugeOneFormProjection direction) 0 =
        0 by
      exact
        positiveSourceActionGeneratedP286GaussJointLocalActualLift_temporalEuler_origin
          (direction canonicalLorentzianTimeDirection),
    positiveSourceActionGeneratedP286GaussJointLocalActualLift_spatialEuler_origin
      (p286SpatialGaugeOneFormProjection direction)
      (p286SpatialGaugeOneFormProjection_time direction)]
  ring

/-- The complete Gauss update still has the exact C3h116 source-contact
field.  Both P286 auxiliary jets were generated only away from that contact,
so the action is responding to one already generated actual `U`. -/
theorem
    positiveSourceActionGeneratedP286GaussJointLocalActualLift_pointField_origin_eq_C3h116 :
    toContinuumPointField
        positiveSourceActionGeneratedP286GaussJointLocalActualLift 0 =
      toContinuumPointField
        positiveSourceActionGeneratedCartanConnectionLocalActualLift 0 := by
  calc
    _ =
        toContinuumPointField
          positiveSourceActionGeneratedP286MomentumJointLocalActualLift 0 :=
      positiveSourceActionGeneratedP286GaussJointLocalActualLift_pointField_origin
    _ =
        toContinuumPointField
          positiveSourceActionGeneratedCartanConnectionLocalActualLift 0 :=
      positiveSourceActionGeneratedP286MomentumJointLocalActualLift_pointField_origin

/-- C3h118 positive checkpoint.  It records the actual producer chain from
C3h116 through the spatial Legendre update and the Gauss update, followed by
the full P286 Euler--Lagrange readback.  No residual field or endpoint
certificate occurs in the law. -/
structure PositiveSourceActionGeneratedP286GaussUpdateLaw : Prop where
  momentumUpdate :
    PositiveSourceActionGeneratedP286MomentumUpdateLaw
  smooth :
    positiveSourceActionGeneratedP286GaussJointLocalActualLift.Smooth
  nondegenerate :
    positiveSourceActionGeneratedP286GaussJointLocalActualLift.Nondegenerate
  sameSourceContact :
    toContinuumPointField
        positiveSourceActionGeneratedP286GaussJointLocalActualLift 0 =
      toContinuumPointField
        positiveSourceActionGeneratedCartanConnectionLocalActualLift 0
  generatedCharge :
    ∀ component : P286CoordinateCarrier,
      p286CoordinateLiePairing
          positiveSourceActionGeneratedP286GaussCharge component =
        positiveC3h110P286TemporalGaussActionTarget component
  fullP286Equation :
    ∀ direction : P286GaugeOneForm,
      p286GaugeConnectionEulerLagrangeCoefficient
          positiveSmoothUnifiedSource
          positiveSourceActionGeneratedP286GaussJointLocalActualLift
          direction 0 =
        0

theorem
    positiveSourceActionGeneratedP286GaussJointLocalActualLift_realizes_C3h118 :
    PositiveSourceActionGeneratedP286GaussUpdateLaw := by
  exact
    { momentumUpdate :=
        positiveSourceActionGeneratedP286MomentumJointLocalActualLift_realizes_C3h117
      smooth :=
        positiveSourceActionGeneratedP286GaussJointLocalActualLift_smooth
      nondegenerate :=
        positiveSourceActionGeneratedP286GaussJointLocalActualLift_nondegenerate
      sameSourceContact :=
        positiveSourceActionGeneratedP286GaussJointLocalActualLift_pointField_origin_eq_C3h116
      generatedCharge :=
        positiveSourceActionGeneratedP286GaussCharge_response
      fullP286Equation :=
        positiveSourceActionGeneratedP286GaussJointLocalActualLift_connectionEquation_origin }

end

end
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP286GaussJointLocalActualLift
