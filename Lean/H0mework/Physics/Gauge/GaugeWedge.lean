import H0mework.Physics.Geometry.TopologicalFourFormPairing

/-!
# Form-native gauge wedge algebra

This module supplies the missing algebraic authority for varying the gauge
auxiliary two-forms in the form-native Stage-9 mother action.  Its first hard
gate is independent of any field equation: the coframe-generated Lorentzian
Hodge must be self-adjoint for the metric-free oriented wedge pairing.  If
that identity failed, the quadratic gauge term would generate the symmetric
part of the constitutive operator rather than the advertised `K_e`.

The proof uses the actual exterior-square coframe action.  Its wedge-volume
scale is shown nonzero from the inverse coframe action, without expanding a
matrix inverse or accepting a determinant receipt.  The remaining results
lift this spacetime identity through an arbitrary symmetric fiber bilinear
form.  No action derivative, stationarity certificate, source value,
constitutive inverse, residual zero, or target equation is consumed.
-/

namespace SaturationMonoid.PhysicsCore.StageNineFormNativeGaugeWedge

open ProofFreeRicherAnholonomicSource
open SU7MotherLieAlgebra
open StageNineBlockwiseConstitutive
open StageNineCoframeTwoFormPairing
open StageNineGlobalIntegratedAction
open StageNineTopologicalFourFormPairing
open Matrix
open scoped ComplexConjugate

noncomputable section

set_option autoImplicit false

/-! ## Exterior-square wedge scale -/

/-- The oriented four-form scale of the actual exterior-square coframe
action.  The two coordinate probes have unit wedge before transport. -/
def coframeTwoFormWedgeScale (coframe : LorentzianCoframe) : ℝ :=
  orientedTwoFormWedgeCoefficient
    (coframeTwoFormLinear coframe (twoFormCoordinateBasis 0))
    (coframeTwoFormLinear coframe (twoFormCoordinateBasis 3))

/-- The exterior-square action scales the metric-free wedge by one common
coframe-dependent factor.  This is the finite-coordinate `∧⁴` covariance
identity; it is not a metric or action equation. -/
theorem orientedTwoFormWedgeCoefficient_coframeTwoFormLinear
    (coframe : LorentzianCoframe) (first second : GaugeTwoForm) :
    orientedTwoFormWedgeCoefficient (coframeTwoFormLinear coframe first)
        (coframeTwoFormLinear coframe second) =
      coframeTwoFormWedgeScale coframe *
        orientedTwoFormWedgeCoefficient first second := by
  simp (disch := decide)
    [coframeTwoFormWedgeScale, orientedTwoFormWedgeCoefficient_explicit,
      twoFormCoordinateBasis, coframeTwoFormLinear, coframeWedge,
      pairFirst, pairSecond, Fin.sum_univ_six]
  ring

/-- On the nondegenerate coframe branch the exterior-square wedge scale
cannot vanish.  The proof composes the actual coframe action with the action
of its matrix inverse, so no formula for the scale is supplied. -/
theorem coframeTwoFormWedgeScale_ne_zero
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0) :
    coframeTwoFormWedgeScale coframe ≠ 0 := by
  have cancel (form : GaugeTwoForm) :
      coframeTwoFormLinear coframe⁻¹
          (coframeTwoFormLinear coframe form) = form := by
    have applied := congrArg
      (fun operator : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm => operator form)
      (coframeTwoFormLinear_inv_comp coframe nondegenerate)
    simpa using applied
  have covariance :=
    orientedTwoFormWedgeCoefficient_coframeTwoFormLinear coframe⁻¹
      (coframeTwoFormLinear coframe (twoFormCoordinateBasis 0))
      (coframeTwoFormLinear coframe (twoFormCoordinateBasis 3))
  have productOne :
      coframeTwoFormWedgeScale coframe⁻¹ *
          coframeTwoFormWedgeScale coframe = 1 := by
    rw [cancel, cancel] at covariance
    rw [orientedTwoFormWedgeCoefficient_basis_zero_three] at covariance
    simpa [coframeTwoFormWedgeScale] using covariance.symm
  intro scaleZero
  rw [scaleZero, mul_zero] at productOne
  norm_num at productOne

/-! ## Dynamic Hodge self-adjointness -/

/-- The fixed Lorentzian two-form Hodge is self-adjoint for the oriented
wedge pairing.  This is the identity-coframe normalization used below. -/
theorem orientedTwoFormWedgeCoefficient_lorentzianHodge_symmetric
    (first second : GaugeTwoForm) :
    orientedTwoFormWedgeCoefficient first
        (lorentzianCoframeHodge second) =
      orientedTwoFormWedgeCoefficient second
        (lorentzianCoframeHodge first) := by
  simp [orientedTwoFormWedgeCoefficient_explicit,
    lorentzianCoframeHodge]
  ring

/-- The actual coframe-generated Hodge is self-adjoint for the metric-free
oriented wedge on every nondegenerate coframe.  This is the decisive
formulation seam for the active gauge-auxiliary Euler derivative. -/
theorem orientedTwoFormWedgeCoefficient_coframeHodge_symmetric
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (first second : GaugeTwoForm) :
    orientedTwoFormWedgeCoefficient first
        (coframeGaugeSpacetimeHodgeLinear coframe second) =
      orientedTwoFormWedgeCoefficient second
        (coframeGaugeSpacetimeHodgeLinear coframe first) := by
  have scaleNonzero :=
    coframeTwoFormWedgeScale_ne_zero coframe nondegenerate
  apply mul_left_cancel₀ scaleNonzero
  calc
    coframeTwoFormWedgeScale coframe *
        orientedTwoFormWedgeCoefficient first
          (coframeGaugeSpacetimeHodgeLinear coframe second) =
      orientedTwoFormWedgeCoefficient
        (coframeTwoFormLinear coframe first)
        (coframeTwoFormLinear coframe
          (coframeGaugeSpacetimeHodgeLinear coframe second)) := by
            rw [orientedTwoFormWedgeCoefficient_coframeTwoFormLinear]
    _ = orientedTwoFormWedgeCoefficient
        (coframeTwoFormLinear coframe first)
        (lorentzianCoframeHodge
          (coframeTwoFormLinear coframe second)) := by
            rw [coframeTwoFormLinear_dynamicHodge coframe nondegenerate]
    _ = orientedTwoFormWedgeCoefficient
        (coframeTwoFormLinear coframe second)
        (lorentzianCoframeHodge
          (coframeTwoFormLinear coframe first)) :=
      orientedTwoFormWedgeCoefficient_lorentzianHodge_symmetric _ _
    _ = orientedTwoFormWedgeCoefficient
        (coframeTwoFormLinear coframe second)
        (coframeTwoFormLinear coframe
          (coframeGaugeSpacetimeHodgeLinear coframe first)) := by
            rw [coframeTwoFormLinear_dynamicHodge coframe nondegenerate]
    _ = coframeTwoFormWedgeScale coframe *
        orientedTwoFormWedgeCoefficient second
          (coframeGaugeSpacetimeHodgeLinear coframe first) := by
            rw [orientedTwoFormWedgeCoefficient_coframeTwoFormLinear]

/-! ## Lie-valued lift of a wedge-self-adjoint spacetime operator -/

/-- Coordinate direction matching the basis used by
`gaugeOperatorCoefficient`. -/
def formNativeGaugeTwoFormCoordinateDirection
    (input : Fin 6) : GaugeTwoForm :=
  fun candidate => if candidate = input then 1 else 0

/-- Wedge self-adjointness of a spacetime operator is exactly symmetry of
its complementary-coordinate coefficient matrix. -/
theorem gaugeOperatorCoefficient_complement_symmetric_of_wedge
    (operator : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm)
    (wedgeSelfAdjoint : ∀ first second : GaugeTwoForm,
      orientedTwoFormWedgeCoefficient first (operator second) =
        orientedTwoFormWedgeCoefficient second (operator first))
    (first second : Fin 6) :
    gaugeOperatorCoefficient operator (twoFormComplement first) second =
      gaugeOperatorCoefficient operator (twoFormComplement second) first := by
  change operator (formNativeGaugeTwoFormCoordinateDirection second)
      (twoFormComplement first) =
    operator (formNativeGaugeTwoFormCoordinateDirection first)
      (twoFormComplement second)
  have actual := wedgeSelfAdjoint
    (formNativeGaugeTwoFormCoordinateDirection first)
    (formNativeGaugeTwoFormCoordinateDirection second)
  fin_cases first <;> fin_cases second <;>
    simp (disch := decide)
      [orientedTwoFormWedgeCoefficient_explicit,
        formNativeGaugeTwoFormCoordinateDirection,
        twoFormComplement] at actual ⊢ <;>
    exact actual

/-- Expand a lifted spacetime operator while leaving the fiber bilinear form
typed. -/
theorem generatedTwoFormWedgeCoefficient_lift_eq_sum
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (pairing : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (operator : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm)
    (first second : Fin 6 → V) :
    generatedTwoFormWedgeCoefficient
        (fun x y => pairing x y) first
        (liftGaugeTwoFormOperator operator second) =
      ∑ pair : Fin 6, ∑ input : Fin 6,
        gaugeOperatorCoefficient operator (twoFormComplement pair) input *
          pairing (first pair) (second input) := by
  unfold generatedTwoFormWedgeCoefficient liftGaugeTwoFormOperator
  apply Finset.sum_congr rfl
  intro pair _
  change (pairing (first pair))
      (∑ input : Fin 6,
        gaugeOperatorCoefficient operator (twoFormComplement pair) input •
          second input) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro input _
  rw [map_smul]
  rfl

/-- A wedge-self-adjoint spacetime operator remains self-adjoint after it is
lifted through any symmetric real fiber bilinear form. -/
theorem generatedTwoFormWedgeCoefficient_lift_symmetric
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (pairing : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (pairingSymmetric : ∀ first second : V,
      pairing first second = pairing second first)
    (operator : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm)
    (wedgeSelfAdjoint : ∀ first second : GaugeTwoForm,
      orientedTwoFormWedgeCoefficient first (operator second) =
        orientedTwoFormWedgeCoefficient second (operator first))
    (first second : Fin 6 → V) :
    generatedTwoFormWedgeCoefficient
        (fun x y => pairing x y) first
        (liftGaugeTwoFormOperator operator second) =
      generatedTwoFormWedgeCoefficient
        (fun x y => pairing x y) second
        (liftGaugeTwoFormOperator operator first) := by
  rw [generatedTwoFormWedgeCoefficient_lift_eq_sum,
    generatedTwoFormWedgeCoefficient_lift_eq_sum]
  calc
    (∑ pair : Fin 6, ∑ input : Fin 6,
        gaugeOperatorCoefficient operator (twoFormComplement pair) input *
          pairing (first pair) (second input)) =
      ∑ pair : Fin 6, ∑ input : Fin 6,
        gaugeOperatorCoefficient operator (twoFormComplement input) pair *
          pairing (first pair) (second input) := by
            apply Finset.sum_congr rfl
            intro pair _
            apply Finset.sum_congr rfl
            intro input _
            rw [gaugeOperatorCoefficient_complement_symmetric_of_wedge
              operator wedgeSelfAdjoint pair input]
    _ = ∑ input : Fin 6, ∑ pair : Fin 6,
        gaugeOperatorCoefficient operator (twoFormComplement input) pair *
          pairing (first pair) (second input) := Finset.sum_comm
    _ = ∑ input : Fin 6, ∑ pair : Fin 6,
        gaugeOperatorCoefficient operator (twoFormComplement input) pair *
          pairing (second input) (first pair) := by
            apply Finset.sum_congr rfl
            intro input _
            apply Finset.sum_congr rfl
            intro pair _
            rw [pairingSymmetric]

/-- A real multiple of the actual dynamic Hodge is wedge-self-adjoint. -/
theorem orientedTwoFormWedgeCoefficient_smul_coframeHodge_symmetric
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (parameter : ℝ) (first second : GaugeTwoForm) :
    orientedTwoFormWedgeCoefficient first
        ((parameter • coframeGaugeSpacetimeHodgeLinear coframe) second) =
      orientedTwoFormWedgeCoefficient second
        ((parameter • coframeGaugeSpacetimeHodgeLinear coframe) first) := by
  change orientedTwoFormWedgeCoefficient first
      (parameter • coframeGaugeSpacetimeHodgeLinear coframe second) =
    orientedTwoFormWedgeCoefficient second
      (parameter • coframeGaugeSpacetimeHodgeLinear coframe first)
  rw [orientedTwoFormWedgeCoefficient_smul_right,
    orientedTwoFormWedgeCoefficient_smul_right,
    orientedTwoFormWedgeCoefficient_coframeHodge_symmetric coframe
      nondegenerate]

/-! ## Canonical P286 fiber pairing -/

private theorem formNativeSpecialUnitaryLiePairing_add_left
    {n : Type*} [Fintype n] [DecidableEq n]
    (first second residual : SpecialUnitaryLieMatrix n) :
    specialUnitaryLiePairing (first + second) residual =
      specialUnitaryLiePairing first residual +
        specialUnitaryLiePairing second residual := by
  simp [specialUnitaryLiePairing, Matrix.add_mul, Matrix.trace_add]
  ring

private theorem formNativeSpecialUnitaryLiePairing_add_right
    {n : Type*} [Fintype n] [DecidableEq n]
    (first second residual : SpecialUnitaryLieMatrix n) :
    specialUnitaryLiePairing residual (first + second) =
      specialUnitaryLiePairing residual first +
        specialUnitaryLiePairing residual second := by
  simp [specialUnitaryLiePairing, Matrix.mul_add, Matrix.trace_add]
  ring

private theorem formNativeSpecialUnitaryLiePairing_smul_left
    {n : Type*} [Fintype n] [DecidableEq n]
    (parameter : ℝ) (first residual : SpecialUnitaryLieMatrix n) :
    specialUnitaryLiePairing (parameter • first) residual =
      parameter * specialUnitaryLiePairing first residual := by
  simp [specialUnitaryLiePairing, Matrix.trace_smul]

private theorem formNativeSpecialUnitaryLiePairing_smul_right
    {n : Type*} [Fintype n] [DecidableEq n]
    (parameter : ℝ) (first residual : SpecialUnitaryLieMatrix n) :
    specialUnitaryLiePairing residual (parameter • first) =
      parameter * specialUnitaryLiePairing residual first := by
  simp [specialUnitaryLiePairing, Matrix.trace_smul]

private theorem formNativeSpecialUnitaryLiePairing_symmetric
    {n : Type*} [Fintype n] [DecidableEq n]
    (first second : SpecialUnitaryLieMatrix n) :
    specialUnitaryLiePairing first second =
      specialUnitaryLiePairing second first := by
  unfold specialUnitaryLiePairing
  rw [Matrix.trace_mul_comm]

private theorem formNativeSpecialUnitaryLiePairing_self_eq_sum_normSq
    {n : Type*} [Fintype n] [DecidableEq n]
    (matrix : SpecialUnitaryLieMatrix n) :
    specialUnitaryLiePairing matrix matrix =
      ∑ row : n, ∑ column : n,
        Complex.normSq ((matrix : Matrix n n ℂ) column row) := by
  unfold specialUnitaryLiePairing
  calc
    -(Matrix.trace
        ((matrix : Matrix n n ℂ) * (matrix : Matrix n n ℂ))).re =
      (Matrix.trace
        ((-(matrix : Matrix n n ℂ)) *
          (matrix : Matrix n n ℂ))).re := by simp
    _ = (Matrix.trace
        (star (matrix : Matrix n n ℂ) *
          (matrix : Matrix n n ℂ))).re := by
      rw [specialUnitaryLieMatrix_star]
    _ = _ := by
      simp [Matrix.trace, Matrix.mul_apply, star_eq_conjTranspose,
        Complex.normSq_apply, Complex.mul_re]

private theorem formNativeSpecialUnitaryLiePairing_self_nonnegative
    {n : Type*} [Fintype n] [DecidableEq n]
    (matrix : SpecialUnitaryLieMatrix n) :
    0 ≤ specialUnitaryLiePairing matrix matrix := by
  rw [formNativeSpecialUnitaryLiePairing_self_eq_sum_normSq]
  exact Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

private theorem formNativeSpecialUnitaryLiePairing_self_eq_zero_iff
    {n : Type*} [Fintype n] [DecidableEq n]
    (matrix : SpecialUnitaryLieMatrix n) :
    specialUnitaryLiePairing matrix matrix = 0 ↔ matrix = 0 := by
  rw [formNativeSpecialUnitaryLiePairing_self_eq_sum_normSq]
  constructor
  · intro sumZero
    apply Subtype.ext
    funext row column
    have columnSumZero :
        (∑ candidateRow : n,
          Complex.normSq
            ((matrix : Matrix n n ℂ) candidateRow column)) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ =>
        Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)).mp
          sumZero column (Finset.mem_univ column)
    have entryNormZero :
        Complex.normSq ((matrix : Matrix n n ℂ) row column) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ =>
        Complex.normSq_nonneg _)).mp columnSumZero row (Finset.mem_univ row)
    exact Complex.normSq_eq_zero.mp entryNormZero
  · rintro rfl
    simp

private theorem formNativeHypercharge_real_part_eq_zero
    (value : HyperchargeLieScalar) : value.1.re = 0 := by
  have starEquality : star value.1 = -value.1 := value.property
  change conj value.1 = -value.1 at starEquality
  have equality := congrArg Complex.re starEquality
  simp only [Complex.conj_re, Complex.neg_re] at equality
  linarith

private theorem formNativeHyperchargeLiePairing_eq_im_mul
    (first second : HyperchargeLieScalar) :
    hyperchargeLiePairing first second = first.1.im * second.1.im := by
  have firstRe := formNativeHypercharge_real_part_eq_zero first
  have secondRe := formNativeHypercharge_real_part_eq_zero second
  unfold hyperchargeLiePairing
  simp [Complex.mul_re, firstRe, secondRe]

private theorem formNativeHyperchargeLiePairing_add_left
    (first second residual : HyperchargeLieScalar) :
    hyperchargeLiePairing (first + second) residual =
      hyperchargeLiePairing first residual +
        hyperchargeLiePairing second residual := by
  simp_rw [formNativeHyperchargeLiePairing_eq_im_mul]
  have addImaginary : (first + second).1.im =
      first.1.im + second.1.im := by
    exact Complex.add_im first.1 second.1
  rw [addImaginary]
  ring

private theorem formNativeHyperchargeLiePairing_add_right
    (first second residual : HyperchargeLieScalar) :
    hyperchargeLiePairing residual (first + second) =
      hyperchargeLiePairing residual first +
        hyperchargeLiePairing residual second := by
  simp_rw [formNativeHyperchargeLiePairing_eq_im_mul]
  have addImaginary : (first + second).1.im =
      first.1.im + second.1.im := by
    exact Complex.add_im first.1 second.1
  rw [addImaginary]
  ring

private theorem formNativeHyperchargeLiePairing_smul_left
    (parameter : ℝ) (first residual : HyperchargeLieScalar) :
    hyperchargeLiePairing (parameter • first) residual =
      parameter * hyperchargeLiePairing first residual := by
  simp_rw [formNativeHyperchargeLiePairing_eq_im_mul]
  have smulImaginary : (parameter • first).1.im =
      parameter * first.1.im := by
    simp
  rw [smulImaginary]
  ring

private theorem formNativeHyperchargeLiePairing_smul_right
    (parameter : ℝ) (first residual : HyperchargeLieScalar) :
    hyperchargeLiePairing residual (parameter • first) =
      parameter * hyperchargeLiePairing residual first := by
  simp_rw [formNativeHyperchargeLiePairing_eq_im_mul]
  have smulImaginary : (parameter • first).1.im =
      parameter * first.1.im := by
    simp
  rw [smulImaginary]
  ring

private theorem formNativeHyperchargeLiePairing_symmetric
    (first second : HyperchargeLieScalar) :
    hyperchargeLiePairing first second =
      hyperchargeLiePairing second first := by
  simp [formNativeHyperchargeLiePairing_eq_im_mul, mul_comm]

private theorem formNativeHyperchargeLiePairing_self_nonnegative
    (value : HyperchargeLieScalar) :
    0 ≤ hyperchargeLiePairing value value := by
  rw [formNativeHyperchargeLiePairing_eq_im_mul]
  exact mul_self_nonneg _

private theorem formNativeHyperchargeLiePairing_self_eq_zero_iff
    (value : HyperchargeLieScalar) :
    hyperchargeLiePairing value value = 0 ↔ value = 0 := by
  rw [formNativeHyperchargeLiePairing_eq_im_mul]
  constructor
  · intro imaginarySquareZero
    have imaginaryZero : value.1.im = 0 :=
      (mul_self_eq_zero.mp imaginarySquareZero)
    apply Subtype.ext
    apply Complex.ext
    · simp [formNativeHypercharge_real_part_eq_zero value]
    · simp [imaginaryZero]
  · rintro rfl
    simp

/-- Canonical positive fiber pairing on the actual `SU(3) × SU(2) × U(1)`
block.  This is a representation readout, not a coupling or field equation. -/
def formNativeP286LiePairing
    (first second : P286LieBlockData) : ℝ :=
  specialUnitaryLiePairing first.1 second.1 +
    specialUnitaryLiePairing first.2.1 second.2.1 +
    hyperchargeLiePairing first.2.2 second.2.2

theorem formNativeP286LiePairing_add_left
    (first second residual : P286LieBlockData) :
    formNativeP286LiePairing (first + second) residual =
      formNativeP286LiePairing first residual +
        formNativeP286LiePairing second residual := by
  simp [formNativeP286LiePairing,
    formNativeSpecialUnitaryLiePairing_add_left,
    formNativeHyperchargeLiePairing_add_left]
  ring

theorem formNativeP286LiePairing_add_right
    (first second residual : P286LieBlockData) :
    formNativeP286LiePairing residual (first + second) =
      formNativeP286LiePairing residual first +
        formNativeP286LiePairing residual second := by
  simp [formNativeP286LiePairing,
    formNativeSpecialUnitaryLiePairing_add_right,
    formNativeHyperchargeLiePairing_add_right]
  ring

theorem formNativeP286LiePairing_smul_left
    (parameter : ℝ) (first residual : P286LieBlockData) :
    formNativeP286LiePairing (parameter • first) residual =
      parameter * formNativeP286LiePairing first residual := by
  simp [formNativeP286LiePairing,
    formNativeSpecialUnitaryLiePairing_smul_left,
    formNativeHyperchargeLiePairing_smul_left]
  ring

theorem formNativeP286LiePairing_smul_right
    (parameter : ℝ) (first residual : P286LieBlockData) :
    formNativeP286LiePairing residual (parameter • first) =
      parameter * formNativeP286LiePairing residual first := by
  simp [formNativeP286LiePairing,
    formNativeSpecialUnitaryLiePairing_smul_right,
    formNativeHyperchargeLiePairing_smul_right]
  ring

theorem formNativeP286LiePairing_symmetric
    (first second : P286LieBlockData) :
    formNativeP286LiePairing first second =
      formNativeP286LiePairing second first := by
  simp [formNativeP286LiePairing,
    formNativeSpecialUnitaryLiePairing_symmetric,
    formNativeHyperchargeLiePairing_symmetric]

theorem formNativeP286LiePairing_self_nonnegative
    (data : P286LieBlockData) :
    0 ≤ formNativeP286LiePairing data data := by
  have strongNonnegative :=
    formNativeSpecialUnitaryLiePairing_self_nonnegative data.1
  have weakNonnegative :=
    formNativeSpecialUnitaryLiePairing_self_nonnegative data.2.1
  have hyperchargeNonnegative :=
    formNativeHyperchargeLiePairing_self_nonnegative data.2.2
  unfold formNativeP286LiePairing
  linarith

theorem formNativeP286LiePairing_self_eq_zero_iff
    (data : P286LieBlockData) :
    formNativeP286LiePairing data data = 0 ↔ data = 0 := by
  constructor
  · intro pairingZero
    have strongNonnegative :=
      formNativeSpecialUnitaryLiePairing_self_nonnegative data.1
    have weakNonnegative :=
      formNativeSpecialUnitaryLiePairing_self_nonnegative data.2.1
    have hyperchargeNonnegative :=
      formNativeHyperchargeLiePairing_self_nonnegative data.2.2
    have strongZero : specialUnitaryLiePairing data.1 data.1 = 0 := by
      unfold formNativeP286LiePairing at pairingZero
      linarith
    have weakZero :
        specialUnitaryLiePairing data.2.1 data.2.1 = 0 := by
      unfold formNativeP286LiePairing at pairingZero
      linarith
    have hyperchargeZero :
        hyperchargeLiePairing data.2.2 data.2.2 = 0 := by
      unfold formNativeP286LiePairing at pairingZero
      linarith
    exact Prod.ext
      ((formNativeSpecialUnitaryLiePairing_self_eq_zero_iff data.1).mp
        strongZero)
      (Prod.ext
        ((formNativeSpecialUnitaryLiePairing_self_eq_zero_iff data.2.1).mp
          weakZero)
        ((formNativeHyperchargeLiePairing_self_eq_zero_iff data.2.2).mp
          hyperchargeZero))
  · rintro rfl
    simp [formNativeP286LiePairing, specialUnitaryLiePairing,
      hyperchargeLiePairing]

/-- Bilinear packaging of the canonical P286 fiber pairing. -/
def formNativeP286LiePairingBilinear :
    P286LieBlockData →ₗ[ℝ] P286LieBlockData →ₗ[ℝ] ℝ where
  toFun first :=
    { toFun := fun second => formNativeP286LiePairing first second
      map_add' := fun second residual =>
        formNativeP286LiePairing_add_right second residual first
      map_smul' := by
        intro parameter second
        simpa [smul_eq_mul] using
          formNativeP286LiePairing_smul_right parameter second first }
  map_add' := by
    intro first second
    apply LinearMap.ext
    intro residual
    exact formNativeP286LiePairing_add_left first second residual
  map_smul' := by
    intro parameter first
    apply LinearMap.ext
    intro residual
    simpa [smul_eq_mul] using
      formNativeP286LiePairing_smul_left parameter first residual

private def formNativeSpecialUnitaryLiePairingBilinear
    {n : Type*} [Fintype n] [DecidableEq n] :
    SpecialUnitaryLieMatrix n →ₗ[ℝ]
      SpecialUnitaryLieMatrix n →ₗ[ℝ] ℝ where
  toFun first :=
    { toFun := fun second => specialUnitaryLiePairing first second
      map_add' := fun second residual =>
        formNativeSpecialUnitaryLiePairing_add_right second residual first
      map_smul' := by
        intro parameter second
        simpa [smul_eq_mul] using
          formNativeSpecialUnitaryLiePairing_smul_right
            parameter second first }
  map_add' := by
    intro first second
    apply LinearMap.ext
    intro residual
    exact formNativeSpecialUnitaryLiePairing_add_left first second residual
  map_smul' := by
    intro parameter first
    apply LinearMap.ext
    intro residual
    simpa [smul_eq_mul] using
      formNativeSpecialUnitaryLiePairing_smul_left parameter first residual

private def formNativeHyperchargeLiePairingBilinear :
    HyperchargeLieScalar →ₗ[ℝ] HyperchargeLieScalar →ₗ[ℝ] ℝ where
  toFun first :=
    { toFun := fun second => hyperchargeLiePairing first second
      map_add' := fun second residual =>
        formNativeHyperchargeLiePairing_add_right second residual first
      map_smul' := by
        intro parameter second
        simpa [smul_eq_mul] using
          formNativeHyperchargeLiePairing_smul_right
            parameter second first }
  map_add' := by
    intro first second
    apply LinearMap.ext
    intro residual
    exact formNativeHyperchargeLiePairing_add_left first second residual
  map_smul' := by
    intro parameter first
    apply LinearMap.ext
    intro residual
    simpa [smul_eq_mul] using
      formNativeHyperchargeLiePairing_smul_left parameter first residual

abbrev FormNativeP286GaugeTwoForm := Fin 6 → P286LieBlockData

/-- Metric-free oriented wedge on the actual full P286 gauge carrier. -/
def formNativeP286GaugeWedgeCoefficient
    (first second : FormNativeP286GaugeTwoForm) : ℝ :=
  generatedTwoFormWedgeCoefficient formNativeP286LiePairing first second

theorem formNativeP286GaugeWedgeCoefficient_decompose
    (first second : FormNativeP286GaugeTwoForm) :
    formNativeP286GaugeWedgeCoefficient first second =
      generatedTwoFormWedgeCoefficient
          (@specialUnitaryLiePairing (Fin 3) _ _)
          (fun pair => (first pair).1) (fun pair => (second pair).1) +
        generatedTwoFormWedgeCoefficient
          (@specialUnitaryLiePairing (Fin 2) _ _)
          (fun pair => (first pair).2.1) (fun pair => (second pair).2.1) +
        generatedTwoFormWedgeCoefficient hyperchargeLiePairing
          (fun pair => (first pair).2.2) (fun pair => (second pair).2.2) := by
  unfold formNativeP286GaugeWedgeCoefficient
    generatedTwoFormWedgeCoefficient formNativeP286LiePairing
  simp_rw [Finset.sum_add_distrib]

/-! ## Three-coupling blockwise constitutive operator -/

/-- Apply the same live coframe Hodge with the independently typed real
coupling coefficient of each P286 block. -/
def formNativeP286BlockwiseConstitutive
    (coframe : LorentzianCoframe)
    (strongSquared weakSquared hyperchargeSquared : ℝ)
    (form : FormNativeP286GaugeTwoForm) :
    FormNativeP286GaugeTwoForm :=
  fun output =>
    (liftGaugeTwoFormOperator
        (strongSquared • coframeGaugeSpacetimeHodgeLinear coframe)
        (fun input => (form input).1) output,
      liftGaugeTwoFormOperator
        (weakSquared • coframeGaugeSpacetimeHodgeLinear coframe)
        (fun input => (form input).2.1) output,
      liftGaugeTwoFormOperator
        (hyperchargeSquared • coframeGaugeSpacetimeHodgeLinear coframe)
        (fun input => (form input).2.2) output)

theorem formNativeP286BlockwiseConstitutive_add
    (coframe : LorentzianCoframe)
    (strongSquared weakSquared hyperchargeSquared : ℝ)
    (first second : FormNativeP286GaugeTwoForm) :
    formNativeP286BlockwiseConstitutive coframe strongSquared weakSquared
        hyperchargeSquared (first + second) =
      formNativeP286BlockwiseConstitutive coframe strongSquared weakSquared
          hyperchargeSquared first +
        formNativeP286BlockwiseConstitutive coframe strongSquared weakSquared
          hyperchargeSquared second := by
  funext output
  apply Prod.ext
  · simp [formNativeP286BlockwiseConstitutive,
      liftGaugeTwoFormOperator, smul_add, Finset.sum_add_distrib]
  · apply Prod.ext
    · simp [formNativeP286BlockwiseConstitutive,
        liftGaugeTwoFormOperator, smul_add, Finset.sum_add_distrib]
    · simp [formNativeP286BlockwiseConstitutive,
        liftGaugeTwoFormOperator, smul_add, Finset.sum_add_distrib]

theorem formNativeP286BlockwiseConstitutive_smul
    (coframe : LorentzianCoframe)
    (strongSquared weakSquared hyperchargeSquared parameter : ℝ)
    (form : FormNativeP286GaugeTwoForm) :
    formNativeP286BlockwiseConstitutive coframe strongSquared weakSquared
        hyperchargeSquared (parameter • form) =
      parameter •
        formNativeP286BlockwiseConstitutive coframe strongSquared weakSquared
          hyperchargeSquared form := by
  funext output
  apply Prod.ext
  · simp [formNativeP286BlockwiseConstitutive,
      liftGaugeTwoFormOperator, smul_smul, Finset.smul_sum,
      mul_comm]
  · apply Prod.ext
    · simp [formNativeP286BlockwiseConstitutive,
        liftGaugeTwoFormOperator, smul_smul, Finset.smul_sum,
        mul_comm]
    · simp [formNativeP286BlockwiseConstitutive,
        liftGaugeTwoFormOperator, smul_smul, Finset.smul_sum,
        mul_comm]

/-- The actual three-coupling blockwise constitutive operator is
self-adjoint for the faithful form-native P286 wedge. -/
theorem formNativeP286GaugeWedgeCoefficient_blockwiseConstitutive_symmetric
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (strongSquared weakSquared hyperchargeSquared : ℝ)
    (first second : FormNativeP286GaugeTwoForm) :
    formNativeP286GaugeWedgeCoefficient first
        (formNativeP286BlockwiseConstitutive coframe strongSquared weakSquared
          hyperchargeSquared second) =
      formNativeP286GaugeWedgeCoefficient second
        (formNativeP286BlockwiseConstitutive coframe strongSquared weakSquared
          hyperchargeSquared first) := by
  have strongSymmetry := generatedTwoFormWedgeCoefficient_lift_symmetric
    (@formNativeSpecialUnitaryLiePairingBilinear (Fin 3) _ _)
    (@formNativeSpecialUnitaryLiePairing_symmetric (Fin 3) _ _)
    (strongSquared • coframeGaugeSpacetimeHodgeLinear coframe)
    (orientedTwoFormWedgeCoefficient_smul_coframeHodge_symmetric coframe
      nondegenerate strongSquared)
    (fun pair => (first pair).1) (fun pair => (second pair).1)
  have weakSymmetry := generatedTwoFormWedgeCoefficient_lift_symmetric
    (@formNativeSpecialUnitaryLiePairingBilinear (Fin 2) _ _)
    (@formNativeSpecialUnitaryLiePairing_symmetric (Fin 2) _ _)
    (weakSquared • coframeGaugeSpacetimeHodgeLinear coframe)
    (orientedTwoFormWedgeCoefficient_smul_coframeHodge_symmetric coframe
      nondegenerate weakSquared)
    (fun pair => (first pair).2.1) (fun pair => (second pair).2.1)
  have hyperchargeSymmetry :=
    generatedTwoFormWedgeCoefficient_lift_symmetric
      formNativeHyperchargeLiePairingBilinear
      formNativeHyperchargeLiePairing_symmetric
      (hyperchargeSquared • coframeGaugeSpacetimeHodgeLinear coframe)
      (orientedTwoFormWedgeCoefficient_smul_coframeHodge_symmetric coframe
        nondegenerate hyperchargeSquared)
      (fun pair => (first pair).2.2) (fun pair => (second pair).2.2)
  have strongSymmetry' :
      generatedTwoFormWedgeCoefficient
          (@specialUnitaryLiePairing (Fin 3) _ _)
          (fun pair => (first pair).1)
          (liftGaugeTwoFormOperator
            (strongSquared • coframeGaugeSpacetimeHodgeLinear coframe)
            (fun pair => (second pair).1)) =
        generatedTwoFormWedgeCoefficient
          (@specialUnitaryLiePairing (Fin 3) _ _)
          (fun pair => (second pair).1)
          (liftGaugeTwoFormOperator
            (strongSquared • coframeGaugeSpacetimeHodgeLinear coframe)
            (fun pair => (first pair).1)) := by
    simpa [formNativeSpecialUnitaryLiePairingBilinear] using strongSymmetry
  have weakSymmetry' :
      generatedTwoFormWedgeCoefficient
          (@specialUnitaryLiePairing (Fin 2) _ _)
          (fun pair => (first pair).2.1)
          (liftGaugeTwoFormOperator
            (weakSquared • coframeGaugeSpacetimeHodgeLinear coframe)
            (fun pair => (second pair).2.1)) =
        generatedTwoFormWedgeCoefficient
          (@specialUnitaryLiePairing (Fin 2) _ _)
          (fun pair => (second pair).2.1)
          (liftGaugeTwoFormOperator
            (weakSquared • coframeGaugeSpacetimeHodgeLinear coframe)
            (fun pair => (first pair).2.1)) := by
    simpa [formNativeSpecialUnitaryLiePairingBilinear] using weakSymmetry
  have hyperchargeSymmetry' :
      generatedTwoFormWedgeCoefficient hyperchargeLiePairing
          (fun pair => (first pair).2.2)
          (liftGaugeTwoFormOperator
            (hyperchargeSquared • coframeGaugeSpacetimeHodgeLinear coframe)
            (fun pair => (second pair).2.2)) =
        generatedTwoFormWedgeCoefficient hyperchargeLiePairing
          (fun pair => (second pair).2.2)
          (liftGaugeTwoFormOperator
            (hyperchargeSquared • coframeGaugeSpacetimeHodgeLinear coframe)
            (fun pair => (first pair).2.2)) := by
    simpa [formNativeHyperchargeLiePairingBilinear] using
      hyperchargeSymmetry
  rw [formNativeP286GaugeWedgeCoefficient_decompose,
    formNativeP286GaugeWedgeCoefficient_decompose]
  simp only [formNativeP286BlockwiseConstitutive]
  rw [strongSymmetry', weakSymmetry', hyperchargeSymmetry']

theorem formNativeP286GaugeWedgeCoefficient_add_left
    (first second residual : FormNativeP286GaugeTwoForm) :
    formNativeP286GaugeWedgeCoefficient (first + second) residual =
      formNativeP286GaugeWedgeCoefficient first residual +
        formNativeP286GaugeWedgeCoefficient second residual := by
  unfold formNativeP286GaugeWedgeCoefficient
    generatedTwoFormWedgeCoefficient
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro pair _
  exact formNativeP286LiePairing_add_left _ _ _

theorem formNativeP286GaugeWedgeCoefficient_add_right
    (first second residual : FormNativeP286GaugeTwoForm) :
    formNativeP286GaugeWedgeCoefficient residual (first + second) =
      formNativeP286GaugeWedgeCoefficient residual first +
        formNativeP286GaugeWedgeCoefficient residual second := by
  unfold formNativeP286GaugeWedgeCoefficient
    generatedTwoFormWedgeCoefficient
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro pair _
  exact formNativeP286LiePairing_add_right _ _ _

theorem formNativeP286GaugeWedgeCoefficient_smul_left
    (parameter : ℝ) (first second : FormNativeP286GaugeTwoForm) :
    formNativeP286GaugeWedgeCoefficient (parameter • first) second =
      parameter * formNativeP286GaugeWedgeCoefficient first second := by
  unfold formNativeP286GaugeWedgeCoefficient
    generatedTwoFormWedgeCoefficient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro pair _
  exact formNativeP286LiePairing_smul_left _ _ _

theorem formNativeP286GaugeWedgeCoefficient_smul_right
    (parameter : ℝ) (first second : FormNativeP286GaugeTwoForm) :
    formNativeP286GaugeWedgeCoefficient first (parameter • second) =
      parameter * formNativeP286GaugeWedgeCoefficient first second := by
  unfold formNativeP286GaugeWedgeCoefficient
    generatedTwoFormWedgeCoefficient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro pair _
  exact formNativeP286LiePairing_smul_right _ _ _

theorem formNativeP286GaugeWedgeCoefficient_symmetric
    (first second : FormNativeP286GaugeTwoForm) :
    formNativeP286GaugeWedgeCoefficient first second =
      formNativeP286GaugeWedgeCoefficient second first := by
  simp only [formNativeP286GaugeWedgeCoefficient,
    generatedTwoFormWedgeCoefficient, Fin.sum_univ_six]
  simp [twoFormComplement]
  rw [formNativeP286LiePairing_symmetric (first 0) (second 3),
    formNativeP286LiePairing_symmetric (first 1) (second 4),
    formNativeP286LiePairing_symmetric (first 2) (second 5),
    formNativeP286LiePairing_symmetric (first 3) (second 0),
    formNativeP286LiePairing_symmetric (first 4) (second 1),
    formNativeP286LiePairing_symmetric (first 5) (second 2)]
  ring

@[simp] theorem formNativeP286GaugeWedgeCoefficient_zero_left
    (second : FormNativeP286GaugeTwoForm) :
    formNativeP286GaugeWedgeCoefficient 0 second = 0 := by
  simp [formNativeP286GaugeWedgeCoefficient,
    generatedTwoFormWedgeCoefficient, formNativeP286LiePairing,
    specialUnitaryLiePairing, hyperchargeLiePairing]

@[simp] theorem formNativeP286GaugeWedgeCoefficient_zero_right
    (first : FormNativeP286GaugeTwoForm) :
    formNativeP286GaugeWedgeCoefficient first 0 = 0 := by
  rw [formNativeP286GaugeWedgeCoefficient_symmetric]
  exact formNativeP286GaugeWedgeCoefficient_zero_left first

/-- Install one P286 Lie-fiber value in one spacetime two-form coordinate. -/
def singleFormNativeP286GaugeTwoForm
    (pair : Fin 6) (value : P286LieBlockData) :
    FormNativeP286GaugeTwoForm :=
  fun candidate => if candidate = pair then value else 0

/-- Pairing with all P286-valued two-form tests faithfully separates the
residual.  In particular, one self-wedge value is deliberately not used. -/
theorem formNativeP286GaugeWedgeCoefficient_separates_left
    (first : FormNativeP286GaugeTwoForm)
    (annihilates : ∀ second : FormNativeP286GaugeTwoForm,
      formNativeP286GaugeWedgeCoefficient first second = 0) :
    first = 0 := by
  funext pair
  fin_cases pair
  · apply (formNativeP286LiePairing_self_eq_zero_iff _).mp
    simpa (disch := decide)
      [formNativeP286GaugeWedgeCoefficient,
        generatedTwoFormWedgeCoefficient, twoFormComplement,
        singleFormNativeP286GaugeTwoForm, Fin.sum_univ_six,
        formNativeP286LiePairing, specialUnitaryLiePairing,
        hyperchargeLiePairing] using
      annihilates
        (singleFormNativeP286GaugeTwoForm 3 (first 0))
  · apply (formNativeP286LiePairing_self_eq_zero_iff _).mp
    simpa (disch := decide)
      [formNativeP286GaugeWedgeCoefficient,
        generatedTwoFormWedgeCoefficient, twoFormComplement,
        singleFormNativeP286GaugeTwoForm, Fin.sum_univ_six,
        formNativeP286LiePairing, specialUnitaryLiePairing,
        hyperchargeLiePairing] using
      annihilates
        (singleFormNativeP286GaugeTwoForm 4 (first 1))
  · apply (formNativeP286LiePairing_self_eq_zero_iff _).mp
    simpa (disch := decide)
      [formNativeP286GaugeWedgeCoefficient,
        generatedTwoFormWedgeCoefficient, twoFormComplement,
        singleFormNativeP286GaugeTwoForm, Fin.sum_univ_six,
        formNativeP286LiePairing, specialUnitaryLiePairing,
        hyperchargeLiePairing] using
      annihilates
        (singleFormNativeP286GaugeTwoForm 5 (first 2))
  · apply (formNativeP286LiePairing_self_eq_zero_iff _).mp
    simpa (disch := decide)
      [formNativeP286GaugeWedgeCoefficient,
        generatedTwoFormWedgeCoefficient, twoFormComplement,
        singleFormNativeP286GaugeTwoForm, Fin.sum_univ_six,
        formNativeP286LiePairing, specialUnitaryLiePairing,
        hyperchargeLiePairing] using
      annihilates
        (singleFormNativeP286GaugeTwoForm 0 (first 3))
  · apply (formNativeP286LiePairing_self_eq_zero_iff _).mp
    simpa (disch := decide)
      [formNativeP286GaugeWedgeCoefficient,
        generatedTwoFormWedgeCoefficient, twoFormComplement,
        singleFormNativeP286GaugeTwoForm, Fin.sum_univ_six,
        formNativeP286LiePairing, specialUnitaryLiePairing,
        hyperchargeLiePairing] using
      annihilates
        (singleFormNativeP286GaugeTwoForm 1 (first 4))
  · apply (formNativeP286LiePairing_self_eq_zero_iff _).mp
    simpa (disch := decide)
      [formNativeP286GaugeWedgeCoefficient,
        generatedTwoFormWedgeCoefficient, twoFormComplement,
        singleFormNativeP286GaugeTwoForm, Fin.sum_univ_six,
        formNativeP286LiePairing, specialUnitaryLiePairing,
        hyperchargeLiePairing] using
      annihilates
        (singleFormNativeP286GaugeTwoForm 2 (first 5))

/-- Faithful dual induced by the form-native P286 wedge. -/
def formNativeP286GaugeWedgeDual
    (first : FormNativeP286GaugeTwoForm) :
    Module.Dual ℝ FormNativeP286GaugeTwoForm where
  toFun := fun second => formNativeP286GaugeWedgeCoefficient first second
  map_add' := fun second residual =>
    formNativeP286GaugeWedgeCoefficient_add_right second residual first
  map_smul' := by
    intro parameter second
    exact formNativeP286GaugeWedgeCoefficient_smul_right
      parameter first second

theorem formNativeP286GaugeWedgeDual_eq_zero_iff
    (first : FormNativeP286GaugeTwoForm) :
    formNativeP286GaugeWedgeDual first = 0 ↔ first = 0 := by
  constructor
  · intro equality
    apply formNativeP286GaugeWedgeCoefficient_separates_left first
    intro second
    have applied := LinearMap.congr_fun equality second
    simpa [formNativeP286GaugeWedgeDual] using applied
  · rintro rfl
    apply LinearMap.ext
    intro second
    simp [formNativeP286GaugeWedgeDual]

end

end SaturationMonoid.PhysicsCore.StageNineFormNativeGaugeWedge
