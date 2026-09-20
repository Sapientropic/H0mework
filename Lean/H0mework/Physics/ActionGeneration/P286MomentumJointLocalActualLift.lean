import H0mework.Physics.ActionGeneration.CartanConnectionLocalActualLift

/-!
# S9-C3h117: C3h116-based action-generated P286 momentum actual update

C3h116 already lets the proof-free source, the actual mother-link path, and
the Lorentz action generate one nonzero Cartan connection actual germ.  Its
primitive P286 auxiliary is still constant in physical time.

This module resumes the earlier path-first/action-first construction:

```text
positive proof-free source
→ actual mother-link/Cauchy path
→ C3h116 Cartan connection actual germ
→ actual P286 connection action functional
→ nondegenerate spatial BF Legendre principal
→ unique spatial auxiliary time velocity
→ one complete actual germ U with that velocity installed
→ actual P286 momentum evolution law.
```

The three installed auxiliary components are the dynamical spatial
`(23,31,12)` components.  The temporal auxiliary components remain zero and
are not filled by a kernel witness.  The constructor does not import or read a
residual carrier, zero fiber, target endpoint, quotient, range certificate,
branch receipt, or supplied stationarity law.  Residual comparison is a later
acceptance step.

The historical internal `positiveC3h109*` names are retained only so the
existing Gauss/action consumers do not acquire a large syntactic migration.
Their producer base in this module is now definitionally C3h116; this file no
longer imports the conditional C3h108/C3h109 response-inverse chain.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP286MomentumJointLocalActualLift

open ProofFreeRicherAnholonomicSource
open StageNineBlockwiseConstitutive
open StageNineCanonicalCauchyState
open StageNineCoframeTwoFormPairing
open StageNineDynamicBreakingVacuum
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
open StageNineP286GaugeConnectionVariationDensity
open StageNineSourceActionGeneratedCartanConnectionLocalActualLift
open StageNineSourceGeneratedMatterSpinActionUpdate
open SU7MotherLieAlgebra
open SU7MotherGaugeTheory
open DiracExteriorMatterAction
open scoped ComplexConjugate ContDiff

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

local instance p286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

/-! ## C3h116 action-owned spatial auxiliary velocity -/

/-- Embed the three dynamical spatial P286 auxiliary velocities in the fixed
two-form order `(01,02,03,23,31,12)`.  The three temporal slots are
definitionally zero. -/
def p286SpatialAuxiliaryVelocityEmbedding
    (velocity : P286SpatialGaugeDirection) : P286GaugeTwoForm :=
  ![0, 0, 0, velocity 0, velocity 1, velocity 2]

/-- Compatibility-named base actual.  Its value is the generated C3h116
Cartan-connection germ, not the conditional historical C3h109 response. -/
def positiveC3h109Actual : StageNineHolonomicConfiguration :=
  positiveSourceActionGeneratedCartanConnectionLocalActualLift

theorem positiveC3h109Actual_eq_C3h116 :
    positiveC3h109Actual =
      positiveSourceActionGeneratedCartanConnectionLocalActualLift :=
  rfl

/-- Proof scaffold with a constant auxiliary value.  It is used only to
differentiate the coefficient multiplying the physical-time coordinate; it
is not the producer output. -/
private def positiveC3h109ConstantAuxiliaryActual
    (velocity : P286SpatialGaugeDirection) :
    StageNineHolonomicConfiguration :=
  { positiveC3h109Actual with
    gaugeAuxiliary := fun _ pair =>
      p286CoordinateEquiv.symm
        (p286SpatialAuxiliaryVelocityEmbedding velocity pair) }

/-- Forward actual installer.  The C3h116 actual germ is retained and the
action-owned P286 spatial auxiliary velocity is installed as a pure
physical-time first jet. -/
def positiveC3h109TimeLinearAuxiliaryActual
    (velocity : P286SpatialGaugeDirection) :
    StageNineHolonomicConfiguration :=
  { positiveC3h109Actual with
    gaugeAuxiliary := fun point pair =>
      p286CoordinateEquiv.symm
        ((point canonicalLorentzianTimeDirection) •
          p286SpatialAuxiliaryVelocityEmbedding velocity pair) }

theorem positiveC3h109Actual_smooth :
    positiveC3h109Actual.Smooth := by
  exact positiveSourceActionGeneratedCartanConnectionLocalActualLift_smooth

private theorem positiveC3h109ConstantAuxiliaryActual_smooth
    (velocity : P286SpatialGaugeDirection) :
    (positiveC3h109ConstantAuxiliaryActual velocity).Smooth := by
  rcases positiveC3h109Actual_smooth with
    ⟨coframe, gravityConnection, gravityAuxiliary, multiplier,
      gaugeConnection, _gaugeAuxiliary, scalar, matter, conjugate⟩
  exact
    ⟨coframe, gravityConnection, gravityAuxiliary, multiplier,
      gaugeConnection, fun pair => by
        simpa only [positiveC3h109ConstantAuxiliaryActual,
          p286CoordinateEquiv.apply_symm_apply] using
          (contDiff_const :
            ContDiff ℝ ∞ fun _ : BasePoint =>
              p286SpatialAuxiliaryVelocityEmbedding velocity pair),
      scalar, matter, conjugate⟩

theorem positiveC3h109TimeLinearAuxiliaryActual_smooth
    (velocity : P286SpatialGaugeDirection) :
    (positiveC3h109TimeLinearAuxiliaryActual velocity).Smooth := by
  rcases positiveC3h109Actual_smooth with
    ⟨coframe, gravityConnection, gravityAuxiliary, multiplier,
      gaugeConnection, _gaugeAuxiliary, scalar, matter, conjugate⟩
  exact
    ⟨coframe, gravityConnection, gravityAuxiliary, multiplier,
      gaugeConnection, fun pair => by
        simpa only [positiveC3h109TimeLinearAuxiliaryActual,
          p286CoordinateEquiv.apply_symm_apply,
          localBaseCoordinate_apply] using
          ((localBaseCoordinate canonicalLorentzianTimeDirection).contDiff
            |>.smul_const
              (p286SpatialAuxiliaryVelocityEmbedding velocity pair)),
      scalar, matter, conjugate⟩

theorem positiveC3h109Actual_nondegenerate :
    positiveC3h109Actual.Nondegenerate :=
  positiveSourceActionGeneratedCartanConnectionLocalActualLift_nondegenerate

private theorem positiveC3h109ConstantAuxiliaryActual_nondegenerate
    (velocity : P286SpatialGaugeDirection) :
    (positiveC3h109ConstantAuxiliaryActual velocity).Nondegenerate :=
  positiveC3h109Actual_nondegenerate

theorem positiveC3h109TimeLinearAuxiliaryActual_nondegenerate
    (velocity : P286SpatialGaugeDirection) :
    (positiveC3h109TimeLinearAuxiliaryActual velocity).Nondegenerate :=
  positiveC3h109Actual_nondegenerate

@[simp] theorem positiveC3h109TimeLinearAuxiliaryActual_origin
    (velocity : P286SpatialGaugeDirection) :
    (positiveC3h109TimeLinearAuxiliaryActual velocity).gaugeAuxiliary 0 =
      0 := by
  funext pair
  apply p286CoordinateEquiv.injective
  simp [positiveC3h109TimeLinearAuxiliaryActual]

/-! ## Identity-origin P286 BF Legendre principal -/

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
  calc
    (∑ pair : Fin 6,
      lorentzianTwoFormSign pair *
        (parameter *
          p286CoordinateLiePairing
            (liftGaugeTwoFormOperator
              (coframeTwoFormLinear coframe) first pair)
            (liftGaugeTwoFormOperator lorentzianCoframeHodge
              (liftGaugeTwoFormOperator
                (coframeTwoFormLinear coframe) residual) pair))) =
        ∑ pair : Fin 6,
          parameter *
            (lorentzianTwoFormSign pair *
              p286CoordinateLiePairing
                (liftGaugeTwoFormOperator
                  (coframeTwoFormLinear coframe) first pair)
                (liftGaugeTwoFormOperator lorentzianCoframeHodge
                  (liftGaugeTwoFormOperator
                    (coframeTwoFormLinear coframe) residual) pair)) := by
      apply Finset.sum_congr rfl
      intro pair _
      ring
    _ = _ := by rw [Finset.mul_sum]

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

@[simp] private theorem canonicalP286SpatialGaugeOneForm_one
    (direction : P286SpatialGaugeDirection) :
    canonicalP286SpatialGaugeOneForm direction 1 = direction 0 :=
  canonicalP286SpatialGaugeOneForm_spatial direction 0

@[simp] private theorem canonicalP286SpatialGaugeOneForm_two
    (direction : P286SpatialGaugeDirection) :
    canonicalP286SpatialGaugeOneForm direction 2 = direction 1 :=
  canonicalP286SpatialGaugeOneForm_spatial direction 1

@[simp] private theorem canonicalP286SpatialGaugeOneForm_three
    (direction : P286SpatialGaugeDirection) :
    canonicalP286SpatialGaugeOneForm direction 3 = direction 2 :=
  canonicalP286SpatialGaugeOneForm_spatial direction 2

private theorem p286TimeExteriorSpatialDirection_normalForm
    (direction : P286SpatialGaugeDirection) :
    p286GaugeExteriorDerivativeDirection canonicalLorentzianTimeDirection
        (canonicalP286SpatialGaugeOneForm direction) =
      ![direction 0, direction 1, direction 2, 0, 0, 0] := by
  funext pair
  fin_cases pair <;>
    simp [p286GaugeExteriorDerivativeDirection,
      canonicalLorentzianTimeDirection, pairFirst, pairSecond]

private theorem p286CoordinateLiePairing_neg_right_local
    (first second : P286CoordinateCarrier) :
    p286CoordinateLiePairing first (-second) =
      -p286CoordinateLiePairing first second := by
  rw [show -second = (-1 : ℝ) • second by simp,
    p286CoordinateLiePairing_smul_right]
  ring

private theorem identityP286SpatialBFLegendre_normalForm
    (velocity direction : P286SpatialGaugeDirection) :
    p286GaugeAuxiliaryHodgePairingPolynomial 1
        (p286SpatialAuxiliaryVelocityEmbedding velocity)
        (p286GaugeExteriorDerivativeDirection
          canonicalLorentzianTimeDirection
          (canonicalP286SpatialGaugeOneForm direction)) =
      -(∑ index : Fin 3,
        p286CoordinateLiePairing (velocity index) (direction index)) := by
  unfold p286GaugeAuxiliaryHodgePairingPolynomial
  rw [coframeTwoFormLinear_one]
  simp_rw [liftGaugeTwoFormOperator_id_p286_local]
  rw [p286TimeExteriorSpatialDirection_normalForm,
    Fin.sum_univ_six, Fin.sum_univ_three]
  simp [p286SpatialAuxiliaryVelocityEmbedding,
    liftGaugeTwoFormOperator_fixedHodge_apply_local,
    lorentzianTwoFormSign, minkowskiInternalSign,
    pairFirst, pairSecond, p286CoordinateLiePairing_neg_right_local]
  ring

/-! ## Actual forward response -/

private theorem positiveC3h109TimeLinearAuxiliaryActual_momentum_factor
    (velocity : P286SpatialGaugeDirection)
    (direction : P286GaugeTwoForm)
    (point : BasePoint) :
    p286GaugeConnectionBFDifferentialMomentum
        (positiveC3h109TimeLinearAuxiliaryActual velocity)
        direction point =
      point canonicalLorentzianTimeDirection *
        p286GaugeConnectionBFDifferentialMomentum
          (positiveC3h109ConstantAuxiliaryActual velocity)
          direction point := by
  unfold p286GaugeConnectionBFDifferentialMomentum generatedVolumeDensity
  unfold holonomicP286GaugeAuxiliaryCoordinate
  simp only [positiveC3h109TimeLinearAuxiliaryActual,
    positiveC3h109ConstantAuxiliaryActual, toContinuumPointField,
    p286CoordinateEquiv.apply_symm_apply]
  rw [show
    (fun pair =>
      point canonicalLorentzianTimeDirection •
        p286SpatialAuxiliaryVelocityEmbedding velocity pair) =
      point canonicalLorentzianTimeDirection •
        p286SpatialAuxiliaryVelocityEmbedding velocity by
    rfl]
  rw [show
    (fun pair => p286SpatialAuxiliaryVelocityEmbedding velocity pair) =
      p286SpatialAuxiliaryVelocityEmbedding velocity by
    rfl]
  rw [p286GaugeAuxiliaryHodgePairingPolynomial_smul_left]
  ring

private theorem fieldDirectionalDerivative_time_mul
    (coefficient : BasePoint → ℝ)
    (differentiable : DifferentiableAt ℝ coefficient 0) :
    fieldDirectionalDerivative
        (fun point =>
          point canonicalLorentzianTimeDirection * coefficient point)
        0 canonicalLorentzianTimeDirection =
      coefficient 0 := by
  unfold fieldDirectionalDerivative
  let timeCoordinate :=
    localBaseCoordinate canonicalLorentzianTimeDirection
  have timeDifferentiable : DifferentiableAt ℝ timeCoordinate 0 :=
    timeCoordinate.differentiable.differentiableAt
  change
    fderiv ℝ
        (fun point => timeCoordinate point * coefficient point)
        0 (coordinateDirection canonicalLorentzianTimeDirection) =
      _
  rw [fderiv_fun_mul timeDifferentiable differentiable,
    timeCoordinate.hasFDerivAt.fderiv]
  simp [timeCoordinate, localBaseCoordinate, coordinateDirection,
    canonicalLorentzianTimeDirection]

private theorem positiveC3h109ConstantAuxiliaryMomentum_origin
    (velocity direction : P286SpatialGaugeDirection) :
    p286GaugeConnectionBFDifferentialMomentum
        (positiveC3h109ConstantAuxiliaryActual velocity)
        (p286GaugeExteriorDerivativeDirection
          canonicalLorentzianTimeDirection
          (canonicalP286SpatialGaugeOneForm direction))
        0 =
      -(∑ index : Fin 3,
        p286CoordinateLiePairing (velocity index) (direction index)) := by
  unfold p286GaugeConnectionBFDifferentialMomentum generatedVolumeDensity
  unfold holonomicP286GaugeAuxiliaryCoordinate
  simp only [positiveC3h109ConstantAuxiliaryActual,
    toContinuumPointField, p286CoordinateEquiv.apply_symm_apply]
  rw [show positiveC3h109Actual.coframe 0 = 1 by
    exact
      positiveSourceActionGeneratedCartanConnectionLocalActualLift_coframe 0]
  simp only [Matrix.det_one, abs_one, one_mul]
  exact identityP286SpatialBFLegendre_normalForm velocity direction

/-- The actual physical-time derivative of the installed BF momentum is the
fixed, nondegenerate spatial P286 Legendre principal.  This is a forward
action response theorem, not a residual equation. -/
theorem positiveC3h109TimeLinearAuxiliaryActual_temporalBFMomentumDerivative
    (velocity direction : P286SpatialGaugeDirection) :
    p286GaugeConnectionTemporalBFMomentumDerivative
        (positiveC3h109TimeLinearAuxiliaryActual velocity)
        (canonicalP286SpatialGaugeOneForm direction) 0 =
      -(∑ index : Fin 3,
        p286CoordinateLiePairing (velocity index) (direction index)) := by
  unfold p286GaugeConnectionTemporalBFMomentumDerivative
  rw [show
    p286GaugeConnectionBFDifferentialMomentum
        (positiveC3h109TimeLinearAuxiliaryActual velocity)
        (p286GaugeExteriorDerivativeDirection
          canonicalLorentzianTimeDirection
          (canonicalP286SpatialGaugeOneForm direction)) =
      fun point =>
        point canonicalLorentzianTimeDirection *
          p286GaugeConnectionBFDifferentialMomentum
            (positiveC3h109ConstantAuxiliaryActual velocity)
            (p286GaugeExteriorDerivativeDirection
              canonicalLorentzianTimeDirection
              (canonicalP286SpatialGaugeOneForm direction))
            point by
    funext point
    exact
      positiveC3h109TimeLinearAuxiliaryActual_momentum_factor
        velocity _ point]
  rw [fieldDirectionalDerivative_time_mul]
  · exact
      positiveC3h109ConstantAuxiliaryMomentum_origin velocity direction
  · exact
      ((p286GaugeConnectionBFDifferentialMomentum_contDiff
        (positiveC3h109ConstantAuxiliaryActual velocity)
        (positiveC3h109ConstantAuxiliaryActual_smooth velocity)
        (positiveC3h109ConstantAuxiliaryActual_nondegenerate velocity)
        (p286GaugeExteriorDerivativeDirection
          canonicalLorentzianTimeDirection
          (canonicalP286SpatialGaugeOneForm direction)))
        |>.differentiable (by simp)).differentiableAt

/-! ## Unique finite-dimensional Legendre inverse -/

/-- The actual spatial BF Legendre principal, bundled in the correct finite
linear dual. -/
def p286SpatialBFLegendreDualOperator :
    P286SpatialGaugeDirection →ₗ[ℝ]
      Module.Dual ℝ P286SpatialGaugeDirection where
  toFun velocity :=
    { toFun := fun direction =>
        -(∑ index : Fin 3,
          p286CoordinateLiePairing (velocity index) (direction index))
      map_add' := by
        intro first second
        change
          -(∑ index : Fin 3,
            p286CoordinateLiePairing
              (velocity index) ((first + second) index)) =
            _
        simp_rw [Pi.add_apply, p286CoordinateLiePairing_add_right]
        rw [Finset.sum_add_distrib]
        ring
      map_smul' := by
        intro parameter direction
        change
          -(∑ index : Fin 3,
            p286CoordinateLiePairing
              (velocity index) ((parameter • direction) index)) =
            _
        simp_rw [Pi.smul_apply, p286CoordinateLiePairing_smul_right]
        rw [← Finset.mul_sum]
        simp [smul_eq_mul] }
  map_add' := by
    intro first second
    apply LinearMap.ext
    intro direction
    change
      -(∑ index : Fin 3,
        p286CoordinateLiePairing
          ((first + second) index) (direction index)) =
        -(∑ index : Fin 3,
          p286CoordinateLiePairing (first index) (direction index)) +
        -(∑ index : Fin 3,
          p286CoordinateLiePairing (second index) (direction index))
    simp_rw [Pi.add_apply, p286CoordinateLiePairing_add_left]
    rw [Finset.sum_add_distrib]
    ring
  map_smul' := by
    intro parameter velocity
    apply LinearMap.ext
    intro direction
    change
      -(∑ index : Fin 3,
        p286CoordinateLiePairing
          ((parameter • velocity) index) (direction index)) =
        parameter •
          (-(∑ index : Fin 3,
            p286CoordinateLiePairing (velocity index) (direction index)))
    simp_rw [Pi.smul_apply, p286CoordinateLiePairing_smul_left]
    rw [← Finset.mul_sum]
    simp [smul_eq_mul]

@[simp] theorem p286SpatialBFLegendreDualOperator_apply
    (velocity direction : P286SpatialGaugeDirection) :
    p286SpatialBFLegendreDualOperator velocity direction =
      -(∑ index : Fin 3,
        p286CoordinateLiePairing (velocity index) (direction index)) :=
  rfl

theorem p286SpatialBFLegendreDualOperator_injective :
    Function.Injective p286SpatialBFLegendreDualOperator := by
  intro first second equality
  have responseZero :
      p286SpatialBFLegendreDualOperator (first - second) = 0 := by
    rw [map_sub, equality, sub_self]
  have evaluatedZero :=
    congrArg
      (fun response : Module.Dual ℝ P286SpatialGaugeDirection =>
        response (first - second))
      responseZero
  simp only [p286SpatialBFLegendreDualOperator_apply,
    LinearMap.zero_apply] at evaluatedZero
  have sumZero :
      ∑ index : Fin 3,
        p286CoordinateLiePairing
          ((first - second) index) ((first - second) index) =
        0 := by
    linarith
  have allZero :=
    (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
      (fun index _ =>
        p286CoordinateLiePairing_self_nonnegative
          ((first - second) index))).mp sumZero
  funext index
  have coordinateZero : (first - second) index = 0 :=
    (p286CoordinateLiePairing_self_eq_zero_iff _).mp
      (allZero index (Finset.mem_univ index))
  exact sub_eq_zero.mp (by simpa using coordinateZero)

theorem p286SpatialBFLegendreDualOperator_surjective :
    Function.Surjective p286SpatialBFLegendreDualOperator := by
  have dimensionEquality :
      Module.finrank ℝ P286SpatialGaugeDirection =
        Module.finrank ℝ
          (Module.Dual ℝ P286SpatialGaugeDirection) := by
    exact Subspace.dual_finrank_eq.symm
  apply
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      dimensionEquality).mp
  exact p286SpatialBFLegendreDualOperator_injective

/-- The fixed action Legendre principal is an equivalence.  Its inverse is
therefore unique and carries no caller-selected preimage or branch. -/
noncomputable def p286SpatialBFLegendreEquiv :
    P286SpatialGaugeDirection ≃ₗ[ℝ]
      Module.Dual ℝ P286SpatialGaugeDirection :=
  LinearEquiv.ofBijective p286SpatialBFLegendreDualOperator
    ⟨p286SpatialBFLegendreDualOperator_injective,
      p286SpatialBFLegendreDualOperator_surjective⟩

@[simp] theorem p286SpatialBFLegendreEquiv_apply
    (velocity : P286SpatialGaugeDirection) :
    p286SpatialBFLegendreEquiv velocity =
      p286SpatialBFLegendreDualOperator velocity :=
  rfl

theorem p286SpatialBFLegendreEquiv_unique
    (target : Module.Dual ℝ P286SpatialGaugeDirection)
    (candidate : P286SpatialGaugeDirection)
    (response : p286SpatialBFLegendreDualOperator candidate = target) :
    candidate = p286SpatialBFLegendreEquiv.symm target := by
  apply p286SpatialBFLegendreDualOperator_injective
  rw [response]
  change target = p286SpatialBFLegendreEquiv
    (p286SpatialBFLegendreEquiv.symm target)
  exact (p286SpatialBFLegendreEquiv.apply_symm_apply target).symm

/-! ## Actual P286 action functional -/

private theorem scalarGaugeConnectionKineticFirstVariationDensity_add_local
    (source : SmoothUnifiedSource)
    (chart : StageNineChart)
    (point : BasePoint)
    (field : StageNineContinuumPointField)
    (first second : LorentzianIndex → ScalarCoordinateCarrier) :
    scalarGaugeConnectionKineticFirstVariationDensity source chart point field
        (first + second) =
      scalarGaugeConnectionKineticFirstVariationDensity source chart point
          field first +
        scalarGaugeConnectionKineticFirstVariationDensity source chart point
          field second := by
  unfold scalarGaugeConnectionKineticFirstVariationDensity
  rw [scalarFrameRelativeCovariantDerivative_add]
  simp only [Pi.add_apply, scalarCoordinatePairingRe_add_left,
    scalarCoordinatePairingRe_add_right]
  rw [← mul_add]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro firstDirection _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro secondDirection _
  ring

private theorem matterGaugeConnectionFirstVariationDensity_add_local
    (source : SmoothUnifiedSource)
    (chart : StageNineChart)
    (point : BasePoint)
    (field : StageNineContinuumPointField)
    (first second : LorentzianIndex → DiracExteriorMatterCarrier) :
    matterGaugeConnectionFirstVariationDensity source chart point field
        (first + second) =
      matterGaugeConnectionFirstVariationDensity source chart point field
          first +
        matterGaugeConnectionFirstVariationDensity source chart point field
          second := by
  unfold matterGaugeConnectionFirstVariationDensity
    matterGaugeConnectionVariationVector
  rw [matterGaugeKineticSum_add, smul_add, map_add]
  exact Complex.add_re _ _

private theorem p286GaugeConnectionFirstVariationDensity_add_local
    (source : SmoothUnifiedSource)
    (chart : StageNineChart)
    (point : BasePoint)
    (field : StageNineContinuumPointField)
    (firstCurvature secondCurvature : P286GaugeTwoForm)
    (firstScalar secondScalar :
      LorentzianIndex → ScalarCoordinateCarrier)
    (firstMatter secondMatter :
      LorentzianIndex → DiracExteriorMatterCarrier) :
    p286GaugeConnectionFirstVariationDensity source chart point field
        (firstCurvature + secondCurvature)
        (firstScalar + secondScalar)
        (firstMatter + secondMatter) =
      p286GaugeConnectionFirstVariationDensity source chart point field
          firstCurvature firstScalar firstMatter +
        p286GaugeConnectionFirstVariationDensity source chart point field
          secondCurvature secondScalar secondMatter := by
  unfold p286GaugeConnectionFirstVariationDensity
  rw [p286GaugeBFCurvatureIncrementDensity_add,
    scalarGaugeConnectionKineticFirstVariationDensity_add_local,
    matterGaugeConnectionFirstVariationDensity_add_local]
  ring

private theorem p286GaugeConnectionFirstVariationDensity_smul_local
    (source : SmoothUnifiedSource)
    (chart : StageNineChart)
    (point : BasePoint)
    (field : StageNineContinuumPointField)
    (parameter : ℝ)
    (curvature : P286GaugeTwoForm)
    (scalar : LorentzianIndex → ScalarCoordinateCarrier)
    (matter : LorentzianIndex → DiracExteriorMatterCarrier) :
    p286GaugeConnectionFirstVariationDensity source chart point field
        (parameter • curvature)
        (parameter • scalar)
        (parameter • matter) =
      parameter *
        p286GaugeConnectionFirstVariationDensity source chart point field
          curvature scalar matter := by
  unfold p286GaugeConnectionFirstVariationDensity
  rw [p286GaugeBFCurvatureIncrementDensity_smul,
    scalarGaugeConnectionKineticFirstVariationDensity_real_smul,
    matterGaugeConnectionFirstVariationDensity_real_smul]
  ring

private theorem p286GaugeConnectionAlgebraicCurvatureDirection_add_local
    (configuration : StageNineHolonomicConfiguration)
    (first second : P286GaugeOneForm)
    (point : BasePoint) :
    p286GaugeConnectionAlgebraicCurvatureDirection configuration
        (first + second) point =
      p286GaugeConnectionAlgebraicCurvatureDirection configuration first
          point +
        p286GaugeConnectionAlgebraicCurvatureDirection configuration second
          point := by
  funext pair
  unfold p286GaugeConnectionAlgebraicCurvatureDirection
    p286GaugeConnectionAlgebraicCurvatureVariation
  simp only [Pi.add_apply]
  rw [p286CoordinateLieBracket_add_left,
    p286CoordinateLieBracket_add_right]
  module

private theorem p286GaugeConnectionAlgebraicCurvatureDirection_smul_local
    (configuration : StageNineHolonomicConfiguration)
    (parameter : ℝ)
    (direction : P286GaugeOneForm)
    (point : BasePoint) :
    p286GaugeConnectionAlgebraicCurvatureDirection configuration
        (parameter • direction) point =
      parameter •
        p286GaugeConnectionAlgebraicCurvatureDirection configuration direction
          point := by
  funext pair
  unfold p286GaugeConnectionAlgebraicCurvatureDirection
    p286GaugeConnectionAlgebraicCurvatureVariation
  simp only [Pi.smul_apply]
  rw [p286CoordinateLieBracket_smul_left,
    p286CoordinateLieBracket_smul_right]
  module

private theorem holonomicScalarGaugeConnectionVariation_const_add_local
    (configuration : StageNineHolonomicConfiguration)
    (first second : P286GaugeOneForm)
    (point : BasePoint) :
    holonomicScalarGaugeConnectionVariation configuration
        (fun _ => first + second) point =
      holonomicScalarGaugeConnectionVariation configuration
          (fun _ => first) point +
        holonomicScalarGaugeConnectionVariation configuration
          (fun _ => second) point := by
  funext formDirection
  unfold holonomicScalarGaugeConnectionVariation
    p286GaugeConnectionMotherVariation
  simp only [Pi.add_apply]
  rw [p286CoordinateEquiv.symm.map_add, p286LieBlockEmbed_add,
    scalarMotherLieAction_add]

private theorem holonomicScalarGaugeConnectionVariation_const_smul_local
    (configuration : StageNineHolonomicConfiguration)
    (parameter : ℝ)
    (direction : P286GaugeOneForm)
    (point : BasePoint) :
    holonomicScalarGaugeConnectionVariation configuration
        (fun _ => parameter • direction) point =
      parameter •
        holonomicScalarGaugeConnectionVariation configuration
          (fun _ => direction) point := by
  funext formDirection
  unfold holonomicScalarGaugeConnectionVariation
    p286GaugeConnectionMotherVariation
  simp only [Pi.smul_apply]
  rw [p286CoordinateEquiv.symm.map_smul, p286LieBlockEmbed_real_smul,
    scalarMotherLieAction_real_smul]

private theorem holonomicMatterGaugeConnectionVariation_const_add_local
    (configuration : StageNineHolonomicConfiguration)
    (first second : P286GaugeOneForm)
    (point : BasePoint) :
    holonomicMatterGaugeConnectionVariation configuration
        (fun _ => first + second) point =
      holonomicMatterGaugeConnectionVariation configuration
          (fun _ => first) point +
        holonomicMatterGaugeConnectionVariation configuration
          (fun _ => second) point := by
  funext formDirection
  unfold holonomicMatterGaugeConnectionVariation
    p286GaugeConnectionMotherVariation
  simp only [Pi.add_apply]
  rw [p286CoordinateEquiv.symm.map_add, p286LieBlockEmbed_add,
    diracExteriorMotherLieAction_add]
  rfl

private theorem holonomicMatterGaugeConnectionVariation_const_smul_local
    (configuration : StageNineHolonomicConfiguration)
    (parameter : ℝ)
    (direction : P286GaugeOneForm)
    (point : BasePoint) :
    holonomicMatterGaugeConnectionVariation configuration
        (fun _ => parameter • direction) point =
      parameter •
        holonomicMatterGaugeConnectionVariation configuration
          (fun _ => direction) point := by
  funext formDirection
  unfold holonomicMatterGaugeConnectionVariation
    p286GaugeConnectionMotherVariation
  simp only [Pi.smul_apply]
  rw [p286CoordinateEquiv.symm.map_smul, p286LieBlockEmbed_real_smul,
    diracExteriorMotherLieAction_real_smul]
  rfl

private theorem p286GaugeConnectionAlgebraicCurrentCoefficient_add_local
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (first second : P286GaugeOneForm)
    (point : BasePoint) :
    p286GaugeConnectionAlgebraicCurrentCoefficient source configuration
        (first + second) point =
      p286GaugeConnectionAlgebraicCurrentCoefficient source configuration
          first point +
        p286GaugeConnectionAlgebraicCurrentCoefficient source configuration
          second point := by
  unfold p286GaugeConnectionAlgebraicCurrentCoefficient
  rw [p286GaugeConnectionAlgebraicCurvatureDirection_add_local,
    holonomicScalarGaugeConnectionVariation_const_add_local,
    holonomicMatterGaugeConnectionVariation_const_add_local,
    p286GaugeConnectionFirstVariationDensity_add_local]

private theorem p286GaugeConnectionAlgebraicCurrentCoefficient_smul_local
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (parameter : ℝ)
    (direction : P286GaugeOneForm)
    (point : BasePoint) :
    p286GaugeConnectionAlgebraicCurrentCoefficient source configuration
        (parameter • direction) point =
      parameter *
        p286GaugeConnectionAlgebraicCurrentCoefficient source configuration
          direction point := by
  unfold p286GaugeConnectionAlgebraicCurrentCoefficient
  rw [p286GaugeConnectionAlgebraicCurvatureDirection_smul_local,
    holonomicScalarGaugeConnectionVariation_const_smul_local,
    holonomicMatterGaugeConnectionVariation_const_smul_local,
    p286GaugeConnectionFirstVariationDensity_smul_local]

/-- The actual algebraic P286 connection current is additive in its constant
one-form direction.  This public action-side interface is used by later
source-generated Cauchy developments; it does not mention a residual. -/
theorem p286GaugeConnectionAlgebraicCurrentCoefficient_add_action
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (first second : P286GaugeOneForm)
    (point : BasePoint) :
    p286GaugeConnectionAlgebraicCurrentCoefficient source configuration
        (first + second) point =
      p286GaugeConnectionAlgebraicCurrentCoefficient source configuration
          first point +
        p286GaugeConnectionAlgebraicCurrentCoefficient source configuration
          second point :=
  p286GaugeConnectionAlgebraicCurrentCoefficient_add_local
    source configuration first second point

/-- The same actual current is real-linear in its constant one-form
direction. -/
theorem p286GaugeConnectionAlgebraicCurrentCoefficient_smul_action
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (parameter : ℝ)
    (direction : P286GaugeOneForm)
    (point : BasePoint) :
    p286GaugeConnectionAlgebraicCurrentCoefficient source configuration
        (parameter • direction) point =
      parameter *
        p286GaugeConnectionAlgebraicCurrentCoefficient source configuration
          direction point :=
  p286GaugeConnectionAlgebraicCurrentCoefficient_smul_local
    source configuration parameter direction point

private theorem canonicalP286SpatialGaugeOneForm_add
    (first second : P286SpatialGaugeDirection) :
    canonicalP286SpatialGaugeOneForm (first + second) =
      canonicalP286SpatialGaugeOneForm first +
        canonicalP286SpatialGaugeOneForm second := by
  funext formDirection
  refine Fin.cases ?_ (fun index => ?_) formDirection
  · simp [canonicalP286SpatialGaugeOneForm]
  · simp only [canonicalP286SpatialGaugeOneForm_spatial, Pi.add_apply]

private theorem canonicalP286SpatialGaugeOneForm_smul
    (parameter : ℝ)
    (direction : P286SpatialGaugeDirection) :
    canonicalP286SpatialGaugeOneForm (parameter • direction) =
      parameter • canonicalP286SpatialGaugeOneForm direction := by
  funext formDirection
  refine Fin.cases ?_ (fun index => ?_) formDirection
  · simp [canonicalP286SpatialGaugeOneForm]
  · simp only [canonicalP286SpatialGaugeOneForm_spatial, Pi.smul_apply]

/-- The P286 connection action evaluated on the current C3h109 actual germ,
restricted to spatial gauge directions and bundled as a finite dual. -/
def positiveC3h109P286SpatialActionTarget :
    Module.Dual ℝ P286SpatialGaugeDirection where
  toFun direction :=
    p286GaugeConnectionAlgebraicCurrentCoefficient
      positiveSmoothUnifiedSource positiveC3h109Actual
      (canonicalP286SpatialGaugeOneForm direction) 0
  map_add' := by
    intro first second
    rw [canonicalP286SpatialGaugeOneForm_add,
      p286GaugeConnectionAlgebraicCurrentCoefficient_add_local]
  map_smul' := by
    intro parameter direction
    rw [canonicalP286SpatialGaugeOneForm_smul,
      p286GaugeConnectionAlgebraicCurrentCoefficient_smul_local]
    rfl

/-- The action functional, not a residual, uniquely generates the P286
spatial auxiliary time velocity through the actual Legendre equivalence. -/
def positiveSourceActionGeneratedP286SpatialAuxiliaryVelocity :
    P286SpatialGaugeDirection :=
  p286SpatialBFLegendreEquiv.symm positiveC3h109P286SpatialActionTarget

theorem positiveSourceActionGeneratedP286SpatialAuxiliaryVelocity_response :
    p286SpatialBFLegendreDualOperator
        positiveSourceActionGeneratedP286SpatialAuxiliaryVelocity =
      positiveC3h109P286SpatialActionTarget := by
  change
    p286SpatialBFLegendreEquiv
        (p286SpatialBFLegendreEquiv.symm
          positiveC3h109P286SpatialActionTarget) =
      positiveC3h109P286SpatialActionTarget
  exact
    p286SpatialBFLegendreEquiv.apply_symm_apply
      positiveC3h109P286SpatialActionTarget

/-- Complete positive joint actual germ after the action-generated P286
spatial auxiliary time velocity has been installed. -/
def positiveSourceActionGeneratedP286MomentumJointLocalActualLift :
    StageNineHolonomicConfiguration :=
  positiveC3h109TimeLinearAuxiliaryActual
    positiveSourceActionGeneratedP286SpatialAuxiliaryVelocity

theorem positiveSourceActionGeneratedP286MomentumJointLocalActualLift_smooth :
    positiveSourceActionGeneratedP286MomentumJointLocalActualLift.Smooth :=
  positiveC3h109TimeLinearAuxiliaryActual_smooth _

theorem
    positiveSourceActionGeneratedP286MomentumJointLocalActualLift_nondegenerate :
    positiveSourceActionGeneratedP286MomentumJointLocalActualLift.Nondegenerate :=
  positiveC3h109TimeLinearAuxiliaryActual_nondegenerate _

@[simp] theorem
    positiveSourceActionGeneratedP286MomentumJointLocalActualLift_gaugeAuxiliary_origin :
    (positiveSourceActionGeneratedP286MomentumJointLocalActualLift
      |>.gaugeAuxiliary) 0 =
      0 :=
  positiveC3h109TimeLinearAuxiliaryActual_origin _

/-- The actual producer's temporal BF momentum derivative is exactly the
source/action-generated target functional. -/
theorem
    positiveSourceActionGeneratedP286MomentumJointLocalActualLift_temporalResponse
    (direction : P286SpatialGaugeDirection) :
    p286GaugeConnectionTemporalBFMomentumDerivative
        positiveSourceActionGeneratedP286MomentumJointLocalActualLift
        (canonicalP286SpatialGaugeOneForm direction) 0 =
      positiveC3h109P286SpatialActionTarget direction := by
  rw [positiveSourceActionGeneratedP286MomentumJointLocalActualLift,
    positiveC3h109TimeLinearAuxiliaryActual_temporalBFMomentumDerivative]
  change
    p286SpatialBFLegendreDualOperator
        positiveSourceActionGeneratedP286SpatialAuxiliaryVelocity direction =
      positiveC3h109P286SpatialActionTarget direction
  rw [positiveSourceActionGeneratedP286SpatialAuxiliaryVelocity_response]

private theorem fieldDirectionalDerivative_time_mul_spatial
    (coefficient : BasePoint → ℝ)
    (differentiable : DifferentiableAt ℝ coefficient 0)
    (spatialDirection : Fin 3) :
    fieldDirectionalDerivative
        (fun point =>
          point canonicalLorentzianTimeDirection * coefficient point)
        0 spatialDirection.succ =
      0 := by
  unfold fieldDirectionalDerivative
  let timeCoordinate :=
    localBaseCoordinate canonicalLorentzianTimeDirection
  have timeDifferentiable : DifferentiableAt ℝ timeCoordinate 0 :=
    timeCoordinate.differentiable.differentiableAt
  change
    fderiv ℝ
        (fun point => timeCoordinate point * coefficient point)
        0 (coordinateDirection spatialDirection.succ) =
      _
  rw [fderiv_fun_mul timeDifferentiable differentiable,
    timeCoordinate.hasFDerivAt.fderiv]
  simp [timeCoordinate, localBaseCoordinate, coordinateDirection,
    canonicalLorentzianTimeDirection]

private theorem
    positiveC3h109TimeLinearAuxiliaryActual_spatialMomentumDerivative_zero
    (velocity : P286SpatialGaugeDirection)
    (direction : P286GaugeTwoForm)
    (spatialDirection : Fin 3) :
    fieldDirectionalDerivative
        (p286GaugeConnectionBFDifferentialMomentum
          (positiveC3h109TimeLinearAuxiliaryActual velocity)
          direction)
        0 spatialDirection.succ =
      0 := by
  rw [show
    p286GaugeConnectionBFDifferentialMomentum
        (positiveC3h109TimeLinearAuxiliaryActual velocity)
        direction =
      fun point =>
        point canonicalLorentzianTimeDirection *
          p286GaugeConnectionBFDifferentialMomentum
            (positiveC3h109ConstantAuxiliaryActual velocity)
            direction point by
    funext point
    exact
      positiveC3h109TimeLinearAuxiliaryActual_momentum_factor
        velocity direction point]
  apply fieldDirectionalDerivative_time_mul_spatial
  exact
    ((p286GaugeConnectionBFDifferentialMomentum_contDiff
      (positiveC3h109ConstantAuxiliaryActual velocity)
      (positiveC3h109ConstantAuxiliaryActual_smooth velocity)
      (positiveC3h109ConstantAuxiliaryActual_nondegenerate velocity)
      direction
      |>.differentiable (by simp))).differentiableAt

/-- The time-linear auxiliary installer has no spatial BF-momentum
divergence at the local origin.  This is a derivative theorem about the
generated actual path, not a stored constraint. -/
theorem positiveC3h109TimeLinearAuxiliaryActual_spatialDivergence_zero
    (velocity direction : P286SpatialGaugeDirection) :
    p286GaugeConnectionSpatialBFMomentumDivergence
        (positiveC3h109TimeLinearAuxiliaryActual velocity)
        (canonicalP286SpatialGaugeOneForm direction) 0 =
      0 := by
  unfold p286GaugeConnectionSpatialBFMomentumDivergence
  rw [show
    fieldDirectionalDerivative
        (p286GaugeConnectionBFDifferentialMomentum
          (positiveC3h109TimeLinearAuxiliaryActual velocity)
          (p286GaugeExteriorDerivativeDirection 1
            (canonicalP286SpatialGaugeOneForm direction)))
        0 1 =
      0 by
    simpa using
      positiveC3h109TimeLinearAuxiliaryActual_spatialMomentumDerivative_zero
        velocity
        (p286GaugeExteriorDerivativeDirection 1
          (canonicalP286SpatialGaugeOneForm direction))
        (0 : Fin 3)]
  rw [show
    fieldDirectionalDerivative
        (p286GaugeConnectionBFDifferentialMomentum
          (positiveC3h109TimeLinearAuxiliaryActual velocity)
          (p286GaugeExteriorDerivativeDirection 2
            (canonicalP286SpatialGaugeOneForm direction)))
        0 2 =
      0 by
    simpa using
      positiveC3h109TimeLinearAuxiliaryActual_spatialMomentumDerivative_zero
        velocity
        (p286GaugeExteriorDerivativeDirection 2
          (canonicalP286SpatialGaugeOneForm direction))
        (1 : Fin 3)]
  rw [show
    fieldDirectionalDerivative
        (p286GaugeConnectionBFDifferentialMomentum
          (positiveC3h109TimeLinearAuxiliaryActual velocity)
          (p286GaugeExteriorDerivativeDirection 3
            (canonicalP286SpatialGaugeOneForm direction)))
        0 3 =
      0 by
    simpa using
      positiveC3h109TimeLinearAuxiliaryActual_spatialMomentumDerivative_zero
        velocity
        (p286GaugeExteriorDerivativeDirection 3
          (canonicalP286SpatialGaugeOneForm direction))
        (2 : Fin 3)]
  ring

theorem positiveC3h109Actual_gaugeAuxiliary_eq_zero :
    positiveC3h109Actual.gaugeAuxiliary = 0 := by
  rfl

/-- Every spatial derivative of the C3h110 time-linear BF momentum vanishes
at the local origin, independently of the tested two-form direction.  This
is the action-path fact later Gauss developments need; it is not a residual
projection. -/
theorem
    positiveSourceActionGeneratedP286MomentumJointLocalActualLift_spatialMomentumDerivative_zero
    (direction : P286GaugeTwoForm)
    (spatialDirection : Fin 3) :
    fieldDirectionalDerivative
        (p286GaugeConnectionBFDifferentialMomentum
          positiveSourceActionGeneratedP286MomentumJointLocalActualLift
          direction)
        0 spatialDirection.succ =
      0 := by
  exact
    positiveC3h109TimeLinearAuxiliaryActual_spatialMomentumDerivative_zero
      positiveSourceActionGeneratedP286SpatialAuxiliaryVelocity
      direction spatialDirection

/-- Hence the C3h110 path has zero spatial BF-momentum divergence for every
constant P286 connection one-form, not only the canonical spatial
projection. -/
theorem
    positiveSourceActionGeneratedP286MomentumJointLocalActualLift_spatialDivergence_zero_allDirections
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionSpatialBFMomentumDivergence
        positiveSourceActionGeneratedP286MomentumJointLocalActualLift
        direction 0 =
      0 := by
  unfold p286GaugeConnectionSpatialBFMomentumDivergence
  rw [show
    fieldDirectionalDerivative
        (p286GaugeConnectionBFDifferentialMomentum
          positiveSourceActionGeneratedP286MomentumJointLocalActualLift
          (p286GaugeExteriorDerivativeDirection 1 direction))
        0 1 =
      0 by
    simpa using
      positiveSourceActionGeneratedP286MomentumJointLocalActualLift_spatialMomentumDerivative_zero
        (p286GaugeExteriorDerivativeDirection 1 direction) (0 : Fin 3)]
  rw [show
    fieldDirectionalDerivative
        (p286GaugeConnectionBFDifferentialMomentum
          positiveSourceActionGeneratedP286MomentumJointLocalActualLift
          (p286GaugeExteriorDerivativeDirection 2 direction))
        0 2 =
      0 by
    simpa using
      positiveSourceActionGeneratedP286MomentumJointLocalActualLift_spatialMomentumDerivative_zero
        (p286GaugeExteriorDerivativeDirection 2 direction) (1 : Fin 3)]
  rw [show
    fieldDirectionalDerivative
        (p286GaugeConnectionBFDifferentialMomentum
          positiveSourceActionGeneratedP286MomentumJointLocalActualLift
          (p286GaugeExteriorDerivativeDirection 3 direction))
        0 3 =
      0 by
    simpa using
      positiveSourceActionGeneratedP286MomentumJointLocalActualLift_spatialMomentumDerivative_zero
        (p286GaugeExteriorDerivativeDirection 3 direction) (2 : Fin 3)]
  ring

private theorem
    positiveC3h109TimeLinearAuxiliaryActual_pointField_origin
    (velocity : P286SpatialGaugeDirection) :
    toContinuumPointField
        (positiveC3h109TimeLinearAuxiliaryActual velocity) 0 =
      toContinuumPointField positiveC3h109Actual 0 := by
  apply StageNineContinuumPointField.ext
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · funext pair
    change
      p286CoordinateEquiv.symm
          (0 • p286SpatialAuxiliaryVelocityEmbedding velocity pair) =
        positiveC3h109Actual.gaugeAuxiliary 0 pair
    rw [positiveC3h109Actual_gaugeAuxiliary_eq_zero]
    simp
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem positiveC3h109TimeLinearAuxiliaryActual_actionCurrent_origin
    (velocity : P286SpatialGaugeDirection)
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionAlgebraicCurrentCoefficient
        positiveSmoothUnifiedSource
        (positiveC3h109TimeLinearAuxiliaryActual velocity)
        direction 0 =
      p286GaugeConnectionAlgebraicCurrentCoefficient
        positiveSmoothUnifiedSource positiveC3h109Actual direction 0 := by
  unfold p286GaugeConnectionAlgebraicCurrentCoefficient
  rw [positiveC3h109TimeLinearAuxiliaryActual_pointField_origin]
  rfl

theorem
    positiveSourceActionGeneratedP286MomentumJointLocalActualLift_spatialDivergence_zero
    (direction : P286SpatialGaugeDirection) :
    p286GaugeConnectionSpatialBFMomentumDivergence
        positiveSourceActionGeneratedP286MomentumJointLocalActualLift
        (canonicalP286SpatialGaugeOneForm direction) 0 =
      0 :=
  positiveC3h109TimeLinearAuxiliaryActual_spatialDivergence_zero _ direction

theorem
    positiveSourceActionGeneratedP286MomentumJointLocalActualLift_actionCurrent_origin
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionAlgebraicCurrentCoefficient
        positiveSmoothUnifiedSource
        positiveSourceActionGeneratedP286MomentumJointLocalActualLift
        direction 0 =
      p286GaugeConnectionAlgebraicCurrentCoefficient
        positiveSmoothUnifiedSource positiveC3h109Actual direction 0 :=
  positiveC3h109TimeLinearAuxiliaryActual_actionCurrent_origin _ direction

/-- The forward P286 update changes only the actual auxiliary path away from
the origin.  At the source contact it retains the complete C3h116 point
field, so the action target is evaluated on the same generated `U`, not on a
reconstructed endpoint. -/
theorem
    positiveSourceActionGeneratedP286MomentumJointLocalActualLift_pointField_origin :
    toContinuumPointField
        positiveSourceActionGeneratedP286MomentumJointLocalActualLift 0 =
      toContinuumPointField
        positiveSourceActionGeneratedCartanConnectionLocalActualLift 0 := by
  simpa [positiveSourceActionGeneratedP286MomentumJointLocalActualLift,
    positiveC3h109Actual] using
    positiveC3h109TimeLinearAuxiliaryActual_pointField_origin
      positiveSourceActionGeneratedP286SpatialAuxiliaryVelocity

/-- Frontier theorem: the proof-free positive source and the actual P286
action generate one complete joint local actual germ whose spatial BF
momentum obeys the P286 connection evolution equation at the origin.

The theorem accepts no residual, shell, endpoint, update witness, or equation
receipt. -/
theorem
    positiveSourceActionGeneratedP286MomentumJointLocalActualLift_satisfies_actionLaw :
    CanonicalP286GaugeSpatialMomentumEvolutionAt
      positiveSmoothUnifiedSource
      positiveSourceActionGeneratedP286MomentumJointLocalActualLift
      0 := by
  intro direction directionTimeZero
  let spatialDirection : P286SpatialGaugeDirection :=
    fun index => direction index.succ
  have directionEquality :
      direction =
        canonicalP286SpatialGaugeOneForm spatialDirection := by
    funext formDirection
    refine Fin.cases ?_ (fun index => ?_) formDirection
    · change direction canonicalLorentzianTimeDirection = 0
      exact directionTimeZero
    · rfl
  rw [directionEquality]
  rw [
    positiveSourceActionGeneratedP286MomentumJointLocalActualLift_temporalResponse,
    positiveSourceActionGeneratedP286MomentumJointLocalActualLift_actionCurrent_origin,
    positiveSourceActionGeneratedP286MomentumJointLocalActualLift_spatialDivergence_zero]
  simp [positiveC3h109P286SpatialActionTarget]

/-- C3h117 positive checkpoint.  The bundle records the producer order:
C3h116 first supplies the actual Cartan germ, its action supplies a unique
P286 momentum update, and only then is the spatial connection equation read
back.  It contains no residual or endpoint certificate. -/
structure PositiveSourceActionGeneratedP286MomentumUpdateLaw : Prop where
  cartanActual :
    PositiveSourceActionGeneratedCartanConnectionLocalActualLaw
  baseIsCartan :
    positiveC3h109Actual =
      positiveSourceActionGeneratedCartanConnectionLocalActualLift
  smooth :
    positiveSourceActionGeneratedP286MomentumJointLocalActualLift.Smooth
  nondegenerate :
    positiveSourceActionGeneratedP286MomentumJointLocalActualLift.Nondegenerate
  sameSourceContact :
    toContinuumPointField
        positiveSourceActionGeneratedP286MomentumJointLocalActualLift 0 =
      toContinuumPointField
        positiveSourceActionGeneratedCartanConnectionLocalActualLift 0
  generatedResponse :
    p286SpatialBFLegendreDualOperator
        positiveSourceActionGeneratedP286SpatialAuxiliaryVelocity =
      positiveC3h109P286SpatialActionTarget
  spatialEvolution :
    CanonicalP286GaugeSpatialMomentumEvolutionAt
      positiveSmoothUnifiedSource
      positiveSourceActionGeneratedP286MomentumJointLocalActualLift
      0

theorem
    positiveSourceActionGeneratedP286MomentumJointLocalActualLift_realizes_C3h117 :
    PositiveSourceActionGeneratedP286MomentumUpdateLaw := by
  exact
    { cartanActual :=
        positiveSourceActionGeneratedCartanConnectionLocalActualLift_realizes_C3h116
      baseIsCartan := positiveC3h109Actual_eq_C3h116
      smooth :=
        positiveSourceActionGeneratedP286MomentumJointLocalActualLift_smooth
      nondegenerate :=
        positiveSourceActionGeneratedP286MomentumJointLocalActualLift_nondegenerate
      sameSourceContact :=
        positiveSourceActionGeneratedP286MomentumJointLocalActualLift_pointField_origin
      generatedResponse :=
        positiveSourceActionGeneratedP286SpatialAuxiliaryVelocity_response
      spatialEvolution :=
        positiveSourceActionGeneratedP286MomentumJointLocalActualLift_satisfies_actionLaw }

end

end
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP286MomentumJointLocalActualLift
