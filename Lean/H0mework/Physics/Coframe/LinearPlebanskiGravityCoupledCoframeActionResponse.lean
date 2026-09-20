import H0mework.Physics.Coframe.LinearPlebanskiCoframeActionPrincipal
import H0mework.Physics.Exterior.GravityAuxiliaryVariation

/-!
# S9-C3h157a: gravity-coupled linear-Plebanski coframe action response

The C3h150 trace reversal cancels a supplied non-gravity action stress while
holding the gravity curvature fixed.  The auxiliary action does not in fact
hold that curvature fixed: once the linear-Plebanski multiplier is generated,
the same action forces

`F = ⋆ᵢ B - λ`.

At the identity coframe with `B = II⁺(1)`, this feedback contributes exactly

`6 * (tr k - 1) * tr δe`

to the densitized gravity-BF coframe principal.  Consequently the complete
action equation has the unique response

`k = (1/5) I + (1/2) Tᵀ - (2/15) tr(T) I`,

where `T` is the already generated non-gravity action stress.  No residual,
endpoint, inverse principal, preimage witness, coefficient, source parameter,
or branch receipt enters this construction.  The constants are forced by the
four-dimensional gravity-BF and linear-Plebanski action algebra.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineLinearPlebanskiGravityCoupledCoframeActionResponse

open ProofFreeRicherAnholonomicSource
open StageNineBlockwiseConstitutive
open StageNineCartanTangentSimplicityResponse
open StageNineCoframeLocalDifferentiability
open StageNineCoframeVariation
open StageNineGlobalIntegratedAction
open StageNineGravityAuxiliaryVariation
open StageNineLinearPlebanskiCoframeActionPrincipal
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

/-! ## The action-generated complete response -/

/-- Gravity-coupled four-dimensional trace reversal.  The affine identity
term and both rational normalizations are fixed by the complete action
principal; they are not source data. -/
def gravityCoupledLinearPlebanskiCoframeResponseOfStress
    (stress : LorentzianCoframe →L[ℝ] ℝ) : LorentzianCoframe :=
  (1 / 5 : ℝ) • (1 : LorentzianCoframe) +
    (1 / 2 : ℝ) • (coframeCovectorCoordinates stress).transpose -
      (2 / 15 * Matrix.trace (coframeCovectorCoordinates stress)) •
        (1 : LorentzianCoframe)

/-- The gravity-BF coframe feedback after the auxiliary equation has
generated the curvature from the same response. -/
def gravityBFCoframeFeedbackLinear
    (response : LorentzianCoframe) :
    LorentzianCoframe →ₗ[ℝ] ℝ where
  toFun := fun variation =>
    6 * (Matrix.trace response - 1) * Matrix.trace variation
  map_add' := by
    intro first second
    simp [Matrix.trace, Fin.sum_univ_four]
    ring
  map_smul' := by
    intro scalar variation
    simp [Matrix.trace, Fin.sum_univ_four]
    ring

def gravityBFCoframeFeedback
    (response : LorentzianCoframe) :
    LorentzianCoframe →L[ℝ] ℝ :=
  (gravityBFCoframeFeedbackLinear response).toContinuousLinearMap

@[simp] theorem gravityBFCoframeFeedback_apply
    (response variation : LorentzianCoframe) :
    gravityBFCoframeFeedback response variation =
      6 * (Matrix.trace response - 1) * Matrix.trace variation :=
  rfl

theorem gravityCoupledLinearPlebanskiCoframeResponse_trace
    (stress : LorentzianCoframe →L[ℝ] ℝ) :
    Matrix.trace
        (gravityCoupledLinearPlebanskiCoframeResponseOfStress stress) =
      4 / 5 -
        (1 / 30) * Matrix.trace (coframeCovectorCoordinates stress) := by
  simp [gravityCoupledLinearPlebanskiCoframeResponseOfStress,
    Matrix.trace, Fin.sum_univ_four]
  ring

/-! ## Complete finite-dimensional action balance -/

/-- The gravity-coupled response cancels the linear-Plebanski principal,
the induced gravity-BF feedback, and the complete non-gravity stress in every
coframe direction. -/
theorem gravityCoupledLinearPlebanskiCoframeResponse_actionBalance
    (stress : LorentzianCoframe →L[ℝ] ℝ) :
    linearPlebanskiCoframePrincipal
          (gravityCoupledLinearPlebanskiCoframeResponseOfStress stress) +
        gravityBFCoframeFeedback
          (gravityCoupledLinearPlebanskiCoframeResponseOfStress stress) +
        stress =
      0 := by
  apply (coframeCovector_eq_iff_coordinateDirections _ _).2
  intro row column
  rw [add_apply, add_apply,
    linearPlebanskiCoframePrincipal_coordinateDirection]
  simp only [gravityBFCoframeFeedback_apply,
    zero_apply]
  fin_cases row <;> fin_cases column <;>
    simp [gravityCoupledLinearPlebanskiCoframeResponseOfStress,
      coframeCovectorCoordinates, coframeCoordinateDirection,
      Matrix.trace, Fin.sum_univ_four] <;>
    ring

/-- Pointwise form used by the downstream source/action producer. -/
theorem gravityCoupledLinearPlebanskiCoframeResponse_actionBalance_apply
    (stress : LorentzianCoframe →L[ℝ] ℝ)
    (variation : LorentzianCoframe) :
    linearPlebanskiCoframePrincipal
          (gravityCoupledLinearPlebanskiCoframeResponseOfStress stress)
          variation +
        gravityBFCoframeFeedback
          (gravityCoupledLinearPlebanskiCoframeResponseOfStress stress)
          variation +
        stress variation =
      0 := by
  have balance := DFunLike.congr_fun
    (gravityCoupledLinearPlebanskiCoframeResponse_actionBalance stress)
    variation
  simpa using balance

/-! ## Canonical uniqueness of the response -/

/-- The combined linear-Plebanski plus induced gravity-BF coframe operator
is injective.  Thus the affine identity term in the response formula does
not hide a branch choice. -/
theorem gravityCoupledLinearPlebanskiCoframeOperator_injective :
    Function.Injective fun response : LorentzianCoframe =>
      linearPlebanskiCoframePrincipal response +
        gravityBFCoframeFeedback response := by
  intro first second operatorEq
  have coordinateEq (row column : Fin 4) :
      linearPlebanskiCoframePrincipal first
            (coframeCoordinateDirection row column) +
          gravityBFCoframeFeedback first
            (coframeCoordinateDirection row column) =
        linearPlebanskiCoframePrincipal second
            (coframeCoordinateDirection row column) +
          gravityBFCoframeFeedback second
            (coframeCoordinateDirection row column) := by
    exact DFunLike.congr_fun operatorEq
      (coframeCoordinateDirection row column)
  have diagonalZero := coordinateEq 0 0
  have diagonalOne := coordinateEq 1 1
  have diagonalTwo := coordinateEq 2 2
  have diagonalThree := coordinateEq 3 3
  simp only [linearPlebanskiCoframePrincipal_coordinateDirection,
    gravityBFCoframeFeedback_apply] at diagonalZero diagonalOne diagonalTwo diagonalThree
  simp [coframeCoordinateDirection, Matrix.trace, Fin.sum_univ_four]
    at diagonalZero diagonalOne diagonalTwo diagonalThree
  have traceEq : Matrix.trace first = Matrix.trace second := by
    simp [Matrix.trace, Fin.sum_univ_four]
    linarith
  ext row column
  by_cases diagonal : row = column
  · subst column
    have entryEq := coordinateEq row row
    simp only [linearPlebanskiCoframePrincipal_coordinateDirection,
      gravityBFCoframeFeedback_apply] at entryEq
    simp [coframeCoordinateDirection, Matrix.trace, Fin.sum_univ_four,
      traceEq] at entryEq
    linarith
  · have entryEq := coordinateEq column row
    have reverse : column ≠ row := Ne.symm diagonal
    simp only [linearPlebanskiCoframePrincipal_coordinateDirection,
      gravityBFCoframeFeedback_apply] at entryEq
    simp [coframeCoordinateDirection, Matrix.trace, Fin.sum_univ_four,
      diagonal, reverse] at entryEq
    linarith

/-- Any response satisfying the complete coframe action balance is the
action-generated response. -/
theorem gravityCoupledLinearPlebanskiCoframeResponse_unique
    (stress : LorentzianCoframe →L[ℝ] ℝ)
    (candidate : LorentzianCoframe)
    (candidateBalance :
      linearPlebanskiCoframePrincipal candidate +
          gravityBFCoframeFeedback candidate + stress =
        0) :
    candidate = gravityCoupledLinearPlebanskiCoframeResponseOfStress stress := by
  apply gravityCoupledLinearPlebanskiCoframeOperator_injective
  exact add_right_cancel (by
    rw [candidateBalance,
      gravityCoupledLinearPlebanskiCoframeResponse_actionBalance])

/-! ## The feedback is the actual densitized gravity-BF derivative -/

def gravityCoupledLinearPlebanskiMultiplier
    (response : LorentzianCoframe) : PhysicalBivector :=
  linearPlebanskiMultiplierOfCoframeResponse response

def gravityCoupledLinearPlebanskiCurvature
    (response : LorentzianCoframe) : PhysicalBivector :=
  gravityInternalDualEquiv
      (physicalIIPlusBivector (1 : LorentzianCoframe)) -
    gravityCoupledLinearPlebanskiMultiplier response

/-- Inverse-free gravity-BF polynomial.  It is equal to the dynamical-Hodge
density on every nondegenerate coframe. -/
def gravityCoupledLinearPlebanskiBFPolynomial
    (response coframe : LorentzianCoframe) : ℝ :=
  gravityAuxiliaryHodgePairingPolynomial coframe
      (physicalIIPlusBivector (1 : LorentzianCoframe))
      (gravityCoupledLinearPlebanskiCurvature response) -
    (1 / 2 : ℝ) *
      gravityAuxiliaryHodgePairingPolynomial coframe
        (physicalIIPlusBivector (1 : LorentzianCoframe))
        (gravityInternalDualEquiv
          (physicalIIPlusBivector (1 : LorentzianCoframe)))

/-- One actual affine coordinate path through the identity coframe. -/
def gravityFeedbackCoordinateCoframe
    (row column : Fin 4) (parameter : ℝ) : LorentzianCoframe :=
  if _diagonal : row = column then
    Matrix.diagonal (fun index =>
      if index = row then 1 + parameter else 1)
  else
    Matrix.transvection row column parameter

theorem gravityFeedbackCoordinateCoframe_eq_one_add
    (row column : Fin 4) (parameter : ℝ) :
    gravityFeedbackCoordinateCoframe row column parameter =
      (1 : LorentzianCoframe) +
        parameter • coframeCoordinateDirection row column := by
  ext output input
  fin_cases row <;> fin_cases column <;>
    fin_cases output <;> fin_cases input <;>
    norm_num [gravityFeedbackCoordinateCoframe,
      coframeCoordinateDirection, Matrix.diagonal_apply,
      Matrix.transvection, Matrix.one_apply, Matrix.single]

theorem gravityFeedbackCoordinateCoframe_det
    (row column : Fin 4) (parameter : ℝ) :
    Matrix.det (gravityFeedbackCoordinateCoframe row column parameter) =
      if row = column then 1 + parameter else 1 := by
  by_cases diagonal : row = column
  · subst column
    fin_cases row <;>
      simp [gravityFeedbackCoordinateCoframe, Matrix.det_diagonal,
        Fin.prod_univ_succ]
  · simp [gravityFeedbackCoordinateCoframe, diagonal,
      Matrix.det_transvection_of_ne row column diagonal]

theorem gravityFeedbackCoordinateCoframe_det_eventually_positive
    (row column : Fin 4) :
    ∀ᶠ parameter in nhds (0 : ℝ),
      0 < Matrix.det
        (gravityFeedbackCoordinateCoframe row column parameter) := by
  simp_rw [gravityFeedbackCoordinateCoframe_det]
  by_cases diagonal : row = column
  · filter_upwards [eventually_gt_nhds
        (show (-1 : ℝ) < 0 by norm_num)] with parameter greater
    rw [if_pos diagonal]
    linarith
  · simp [diagonal]

/-- On every coordinate path the complete densitized gravity-BF polynomial
depends only on the trace of the generated response.  Diagonal paths carry
the forced quadratic volume/frame factor; off-diagonal paths are constant. -/
theorem gravityCoupledLinearPlebanskiBFPolynomial_coordinate_normalForm
    (response : LorentzianCoframe)
    (row column : Fin 4) (parameter : ℝ) :
    (if row = column then 1 + parameter else 1) *
        gravityCoupledLinearPlebanskiBFPolynomial response
          (gravityFeedbackCoordinateCoframe row column parameter) =
      if row = column then
        3 * (Matrix.trace response - 1) * (1 + parameter) ^ 2
      else
        3 * (Matrix.trace response - 1) := by
  fin_cases row <;> fin_cases column <;>
    simp [gravityCoupledLinearPlebanskiBFPolynomial,
      gravityCoupledLinearPlebanskiCurvature,
      gravityCoupledLinearPlebanskiMultiplier,
      linearPlebanskiMultiplierOfCoframeResponse,
      physicalIIPlusCoframeTangent, coframeWedgeTangent,
      physicalIIPlusBivector, gravityInternalDualEquiv,
      gravityInternalDualLinear, internalBivectorDual,
      gravityAuxiliaryHodgePairingPolynomial,
      gravityFeedbackCoordinateCoframe, coframeCoordinateDirection,
      coframeTwoFormLinear, coframeWedge, lorentzianCoframeHodge,
      lorentzianTwoFormSign, minkowskiInternalSign,
      pairFirst, pairSecond, Matrix.trace,
      Matrix.diagonal_apply, Matrix.transvection, Matrix.single,
      Matrix.one_apply, Fin.sum_univ_six, Fin.sum_univ_four] <;>
    ring

/-- Direct finite-coordinate calculation of the gravity-BF feedback. -/
theorem gravityCoupledLinearPlebanskiBFPolynomial_coordinate_hasDerivAt
    (response : LorentzianCoframe)
    (row column : Fin 4) :
    HasDerivAt
      (fun parameter : ℝ =>
        (if row = column then 1 + parameter else 1) *
          gravityCoupledLinearPlebanskiBFPolynomial response
            (gravityFeedbackCoordinateCoframe row column parameter))
      (gravityBFCoframeFeedback response
        (coframeCoordinateDirection row column))
      0 := by
  rw [show
      (fun parameter : ℝ =>
        (if row = column then 1 + parameter else 1) *
          gravityCoupledLinearPlebanskiBFPolynomial response
            (gravityFeedbackCoordinateCoframe row column parameter)) =
        fun parameter =>
          if row = column then
            3 * (Matrix.trace response - 1) * (1 + parameter) ^ 2
          else
            3 * (Matrix.trace response - 1) by
    funext parameter
    exact
      gravityCoupledLinearPlebanskiBFPolynomial_coordinate_normalForm
        response row column parameter]
  by_cases diagonal : row = column
  · subst column
    simp only [if_pos]
    have affineDerivative :=
      (hasDerivAt_const (x := (0 : ℝ)) (1 : ℝ)).add
        (hasDerivAt_id (x := (0 : ℝ)))
    have squaredDerivative := affineDerivative.pow 2
    have scaledDerivative := squaredDerivative.const_mul
      (3 * (Matrix.trace response - 1))
    convert! scaledDerivative using 1
    all_goals
      fin_cases row <;>
        simp [gravityBFCoframeFeedback, gravityBFCoframeFeedbackLinear,
          coframeCoordinateDirection, Matrix.trace, Fin.sum_univ_four] <;>
        ring
  · simp only [diagonal, if_neg]
    convert!
      (hasDerivAt_const (x := (0 : ℝ))
        (3 * (Matrix.trace response - 1))) using 1
    all_goals
      fin_cases row <;> fin_cases column <;>
        simp_all [gravityBFCoframeFeedback, gravityBFCoframeFeedbackLinear,
          coframeCoordinateDirection, Matrix.trace, Fin.sum_univ_four,
          diagonal]

/-! ## Fréchet derivative of the actual densitized gravity-BF sector -/

def gravityCoupledLinearPlebanskiBFCoframeDensity
    (response coframe : LorentzianCoframe) : ℝ :=
  |Matrix.det coframe| *
    gravityCoupledLinearPlebanskiBFPolynomial response coframe

theorem gravityCoupledLinearPlebanskiBFCoframeDensity_coordinate_hasDerivAt
    (response : LorentzianCoframe)
    (row column : Fin 4) :
    HasDerivAt
      (fun parameter : ℝ =>
        gravityCoupledLinearPlebanskiBFCoframeDensity response
          ((1 : LorentzianCoframe) +
            parameter • coframeCoordinateDirection row column))
      (gravityBFCoframeFeedback response
        (coframeCoordinateDirection row column))
      0 := by
  have polynomialDerivative :=
    gravityCoupledLinearPlebanskiBFPolynomial_coordinate_hasDerivAt
      response row column
  apply polynomialDerivative.congr_of_eventuallyEq
  filter_upwards
      [gravityFeedbackCoordinateCoframe_det_eventually_positive row column]
      with parameter determinantPositive
  rw [← gravityFeedbackCoordinateCoframe_eq_one_add]
  unfold gravityCoupledLinearPlebanskiBFCoframeDensity
  rw [abs_of_pos determinantPositive,
    gravityFeedbackCoordinateCoframe_det]

theorem gravityAuxiliaryHodgePairingPolynomial_contDiff_local
    (first residual : PhysicalBivector) :
    ContDiff ℝ ∞ (fun coframe : LorentzianCoframe =>
      gravityAuxiliaryHodgePairingPolynomial coframe first residual) := by
  unfold gravityAuxiliaryHodgePairingPolynomial
  apply ContDiff.sum
  intro internalPair _
  apply contDiff_const.mul
  apply ContDiff.sum
  intro spacetimePair _
  have firstSmooth :=
    coframeTwoFormLinear_apply_contDiff (first internalPair) spacetimePair
  have residualHodgeSmooth : ContDiff ℝ ∞
      (fun coframe : LorentzianCoframe =>
        lorentzianCoframeHodge
          (coframeTwoFormLinear coframe (residual internalPair))
          spacetimePair) := by
    fin_cases spacetimePair
    · exact coframeTwoFormLinear_apply_contDiff (residual internalPair) 3
    · exact coframeTwoFormLinear_apply_contDiff (residual internalPair) 4
    · exact coframeTwoFormLinear_apply_contDiff (residual internalPair) 5
    · exact (coframeTwoFormLinear_apply_contDiff
        (residual internalPair) 0).neg
    · exact (coframeTwoFormLinear_apply_contDiff
        (residual internalPair) 1).neg
    · exact (coframeTwoFormLinear_apply_contDiff
        (residual internalPair) 2).neg
  exact (contDiff_const.mul firstSmooth).mul residualHodgeSmooth

theorem gravityCoupledLinearPlebanskiBFPolynomial_contDiff
    (response : LorentzianCoframe) :
    ContDiff ℝ ∞
      (gravityCoupledLinearPlebanskiBFPolynomial response) := by
  unfold gravityCoupledLinearPlebanskiBFPolynomial
  exact
    (gravityAuxiliaryHodgePairingPolynomial_contDiff_local
      (physicalIIPlusBivector (1 : LorentzianCoframe))
      (gravityCoupledLinearPlebanskiCurvature response)).sub
    (contDiff_const.mul
      (gravityAuxiliaryHodgePairingPolynomial_contDiff_local
        (physicalIIPlusBivector (1 : LorentzianCoframe))
        (gravityInternalDualEquiv
          (physicalIIPlusBivector (1 : LorentzianCoframe)))))

theorem gravityCoupledLinearPlebanskiBFCoframeDensity_contDiffAt
    (response : LorentzianCoframe) :
    ContDiffAt ℝ ∞
      (gravityCoupledLinearPlebanskiBFCoframeDensity response)
      (1 : LorentzianCoframe) := by
  unfold gravityCoupledLinearPlebanskiBFCoframeDensity
  exact
    (coframe_volume_contDiffAt (1 : LorentzianCoframe) (by simp)).mul
      (gravityCoupledLinearPlebanskiBFPolynomial_contDiff response).contDiffAt

def gravityCoupledLinearPlebanskiBFCoframeStress
    (response : LorentzianCoframe) :
    LorentzianCoframe →L[ℝ] ℝ :=
  fderiv ℝ
    (gravityCoupledLinearPlebanskiBFCoframeDensity response)
    (1 : LorentzianCoframe)

theorem gravityCoupledLinearPlebanskiBFCoframeDensity_hasFDerivAt
    (response : LorentzianCoframe) :
    HasFDerivAt
      (gravityCoupledLinearPlebanskiBFCoframeDensity response)
      (gravityCoupledLinearPlebanskiBFCoframeStress response)
      (1 : LorentzianCoframe) :=
  ((gravityCoupledLinearPlebanskiBFCoframeDensity_contDiffAt response).differentiableAt
    (by simp)).hasFDerivAt

/-- The finite-coordinate feedback above is exactly the Fréchet derivative
of the actual densitized gravity-BF action, not a residual-shaped surrogate. -/
theorem gravityCoupledLinearPlebanskiBFCoframeStress_eq_feedback
    (response : LorentzianCoframe) :
    gravityCoupledLinearPlebanskiBFCoframeStress response =
      gravityBFCoframeFeedback response := by
  apply (coframeCovector_eq_iff_coordinateDirections _ _).2
  intro row column
  have identityDerivative := hasDerivAt_id (x := (0 : ℝ))
  have coordinateDerivative :=
    identityDerivative.smul_const (coframeCoordinateDirection row column)
  have coordinateDerivativeValue :
      (1 : ℝ) • coframeCoordinateDirection row column =
        coframeCoordinateDirection row column := by
    simp
  have coordinateDerivativeAtZero :=
    coordinateDerivative.congr_deriv coordinateDerivativeValue
  have pathDerivative :=
    coordinateDerivativeAtZero.const_add (1 : LorentzianCoframe)
  have pointEquality :
      (1 : LorentzianCoframe) =
        (1 : LorentzianCoframe) +
          (0 : ℝ) • coframeCoordinateDirection row column := by
    simp
  have composedDerivative :=
    (gravityCoupledLinearPlebanskiBFCoframeDensity_hasFDerivAt response).comp_hasDerivAt_of_eq
      (0 : ℝ) pathDerivative pointEquality
  exact composedDerivative.unique
    (gravityCoupledLinearPlebanskiBFCoframeDensity_coordinate_hasDerivAt
      response row column)

theorem gravityCoupledLinearPlebanskiBFCoframeDensity_path_hasDerivAt
    (response variation : LorentzianCoframe) :
    HasDerivAt
      (fun parameter : ℝ =>
        gravityCoupledLinearPlebanskiBFCoframeDensity response
          ((1 : LorentzianCoframe) + parameter • variation))
      (gravityBFCoframeFeedback response variation)
      0 := by
  have identityDerivative := hasDerivAt_id (x := (0 : ℝ))
  have variationDerivative := identityDerivative.smul_const variation
  have variationDerivativeValue :
      (1 : ℝ) • variation = variation := by
    simp
  have variationDerivativeAtZero :=
    variationDerivative.congr_deriv variationDerivativeValue
  have pathDerivative :=
    variationDerivativeAtZero.const_add (1 : LorentzianCoframe)
  have pointEquality :
      (1 : LorentzianCoframe) =
        (1 : LorentzianCoframe) + (0 : ℝ) • variation := by
    simp
  have actual :=
    (gravityCoupledLinearPlebanskiBFCoframeDensity_hasFDerivAt response).comp_hasDerivAt_of_eq
      (0 : ℝ) pathDerivative pointEquality
  rw [gravityCoupledLinearPlebanskiBFCoframeStress_eq_feedback] at actual
  exact actual

end

end
  SaturationMonoid.PhysicsCore.StageNineLinearPlebanskiGravityCoupledCoframeActionResponse
