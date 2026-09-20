import H0mework.Physics.IdentityGerms.CoframeHessianLocalActualLift

/-!
# Nonlinear Levi--Civita first germ of the identity-contact quadratic coframe

This module recomputes the pointwise Levi--Civita spin connection from the
actual quadratic coframe germ

`e_H(x) = I + (1 / 2) H(x,x)`.

The first-jet field fed to the pointwise connection producer is proved equal
to `holonomicCoframeFirstJetAt e_H`; it is not supplied independently.  The
main first-germ theorem then differentiates the resulting nonlinear
connection at the origin and recovers the forward Koszul symbol
`identityECLeviCivitaSpinConnectionFirstJet H`.

This is an origin-germ statement.  It neither asserts global
nondegeneracy of the polynomial coframe nor installs a Cartan reaction,
field equation, target residual, branch, or acceptance receipt.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeIdentityECNonlinearLeviCivitaFirstGerm

open ProofFreeRicherAnholonomicSource
open StageNineCoframeFirstJet
open StageNineCoframeHolonomicSecondJetCarrier
open StageNineCoframeLocalDifferentiability
open StageNineCoframeVariation
open StageNineDiracDualFormNativeIdentityECHolonomicCoframeHessianLocalActualLift
open StageNineDiracDualFormNativeIdentityECHolonomicCoframeHessianSection
open StageNineHolonomicField
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2400000

/-! ## Actual quadratic coframe and its generated first-jet field -/

/-- Identity coframe with vanishing first derivative at the contact. -/
def identityECZeroCoframeFirstJet : PointwiseLorentzianCoframeJet where
  coframe := 1
  derivative := 0

/-- Actual affine-plus-quadratic coframe realization based at `(I,0)`. -/
def identityECQuadraticCoframeField
    (hessian : CoframeHolonomicSecondJet) :
    BasePoint → LorentzianCoframe :=
  coframeFieldOfFirstAndSecondJet identityECZeroCoframeFirstJet hessian

/-- Explicit first-jet formula forced by differentiating the actual
quadratic coframe.  Its derivative slot is `H(point,-)`. -/
def identityECQuadraticCoframeJet
    (hessian : CoframeHolonomicSecondJet)
    (point : BasePoint) : PointwiseLorentzianCoframeJet where
  coframe := identityECQuadraticCoframeField hessian point
  derivative := fun derivativeDirection internal coordinate =>
    hessian.1 point (coordinateDirection derivativeDirection)
      internal coordinate

@[simp] private theorem
    coframeJetAffineLinear_identityECZeroCoframeFirstJet :
    coframeJetAffineLinear identityECZeroCoframeFirstJet = 0 := by
  have componentZero
      (internal coordinate : LorentzianIndex) :
      coframeJetAffineComponentLinear identityECZeroCoframeFirstJet
          internal coordinate = 0 := by
    ext point
    simp [coframeJetAffineComponentLinear, identityECZeroCoframeFirstJet]
  ext point internal coordinate
  change
    coframeJetAffineComponentLinear identityECZeroCoframeFirstJet
        internal coordinate point = 0
  rw [componentZero]
  rfl

private def coframeEntryEvaluation
    (internal coordinate : LorentzianIndex) :
    LorentzianCoframe →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj coordinate :
      (LorentzianIndex → ℝ) →L[ℝ] ℝ).comp
    (ContinuousLinearMap.proj internal :
      LorentzianCoframe →L[ℝ] (LorentzianIndex → ℝ))

/-- The explicit jet above is a readout of the actual field derivative at
every point, not a separately supplied jet. -/
theorem holonomicCoframeFirstJetAt_identityECQuadraticCoframeField
    (hessian : CoframeHolonomicSecondJet)
    (point : BasePoint) :
    holonomicCoframeFirstJetAt
        (identityECQuadraticCoframeField hessian) point =
      identityECQuadraticCoframeJet hessian point := by
  apply coframeJet_eq_of_fields_eq
  · rfl
  · funext derivativeDirection internal coordinate
    let evaluation := coframeEntryEvaluation internal coordinate
    have componentDerivative : HasFDerivAt
        (fun candidate =>
          evaluation (identityECQuadraticCoframeField hessian candidate))
        (evaluation.comp (hessian.1 point)) point := by
      have fieldDerivative :
          HasFDerivAt (identityECQuadraticCoframeField hessian)
            (hessian.1 point) point := by
        simpa only [identityECQuadraticCoframeField,
          coframeJetAffineLinear_identityECZeroCoframeFirstJet,
          zero_add] using
          (coframeFieldOfFirstAndSecondJet_hasFDerivAt
            identityECZeroCoframeFirstJet hessian point)
      exact evaluation.hasFDerivAt.comp point fieldDerivative
    unfold holonomicCoframeFirstJetAt
    change
      fderiv ℝ
          (fun candidate =>
            evaluation (identityECQuadraticCoframeField hessian candidate))
          point (coordinateDirection derivativeDirection) =
        hessian.1 point (coordinateDirection derivativeDirection)
          internal coordinate
    rw [componentDerivative.fderiv]
    rfl

/-- Nonlinear pointwise Levi--Civita connection recomputed from the actual
quadratic coframe at every point. -/
def identityECNonlinearLeviCivitaConnection
    (hessian : CoframeHolonomicSecondJet) :
    LorentzConnectionField :=
  fun point =>
    (holonomicCoframeFirstJetAt
      (identityECQuadraticCoframeField hessian) point).lorentzSpinConnection

theorem identityECNonlinearLeviCivitaConnection_eq_explicitJet
    (hessian : CoframeHolonomicSecondJet)
    (point : BasePoint) :
    identityECNonlinearLeviCivitaConnection hessian point =
      (identityECQuadraticCoframeJet hessian point).lorentzSpinConnection := by
  rw [identityECNonlinearLeviCivitaConnection,
    holonomicCoframeFirstJetAt_identityECQuadraticCoframeField]

/-! ## First-order comparison with the frozen identity coframe -/

/-- Product carrier used only to differentiate the existing pointwise
connection producer in its genuine coframe and derivative inputs. -/
abbrev IdentityECCoframeJetCarrier :=
  LorentzianCoframe × LorentzianCoframeDerivative

def pointwiseCoframeJetOfCarrier
    (carrier : IdentityECCoframeJetCarrier) :
    PointwiseLorentzianCoframeJet where
  coframe := carrier.1
  derivative := carrier.2

def identityECSpinConnectionComponentOfCarrier
    (formDirection internalOut internalIn : LorentzianIndex)
    (carrier : IdentityECCoframeJetCarrier) : ℝ :=
  (pointwiseCoframeJetOfCarrier carrier).lorentzSpinConnection
    formDirection internalOut internalIn

private theorem identityEC_coframeInverseEntry_contDiffAt
    (row column : LorentzianIndex) :
    ContDiffAt ℝ ∞
      (fun carrier : IdentityECCoframeJetCarrier =>
        carrier.1⁻¹ row column)
      ((1 : LorentzianCoframe), (0 : LorentzianCoframeDerivative)) := by
  have inverseSmooth :=
    coframe_inv_contDiffAt (1 : LorentzianCoframe) (by simp)
  exact (contDiffAt_pi.mp
    (contDiffAt_pi.mp inverseSmooth row) column).comp
      ((1 : LorentzianCoframe), (0 : LorentzianCoframeDerivative))
      contDiffAt_fst

private theorem identityEC_metricInverseEntry_contDiffAt
    (row column : LorentzianIndex) :
    ContDiffAt ℝ ∞
      (fun carrier : IdentityECCoframeJetCarrier =>
        (lorentzianMetricOfCoframe carrier.1)⁻¹ row column)
      ((1 : LorentzianCoframe), (0 : LorentzianCoframeDerivative)) := by
  have inverseSmooth :=
    lorentzianMetric_inv_contDiffAt
      (1 : LorentzianCoframe) (by simp)
  exact (contDiffAt_pi.mp
    (contDiffAt_pi.mp inverseSmooth row) column).comp
      ((1 : LorentzianCoframe), (0 : LorentzianCoframeDerivative))
      contDiffAt_fst

/-- The existing pointwise nonlinear Levi--Civita producer is genuinely
differentiable in its two primitive jet inputs at the identity/zero contact.
The inverse coframe and inverse metric are justified by the actual
nondegeneracy of the identity coframe. -/
theorem identityECSpinConnectionComponentOfCarrier_differentiableAt
    (formDirection internalOut internalIn : LorentzianIndex) :
    DifferentiableAt ℝ
      (identityECSpinConnectionComponentOfCarrier
        formDirection internalOut internalIn)
      ((1 : LorentzianCoframe), (0 : LorentzianCoframeDerivative)) := by
  have coframeInverseDifferentiable
      (row column : LorentzianIndex) :
      DifferentiableAt ℝ
        (fun carrier : IdentityECCoframeJetCarrier =>
          carrier.1⁻¹ row column)
        ((1 : LorentzianCoframe),
          (0 : LorentzianCoframeDerivative)) :=
    (identityEC_coframeInverseEntry_contDiffAt row column).differentiableAt
      (by simp)
  have metricInverseDifferentiable
      (row column : LorentzianIndex) :
      DifferentiableAt ℝ
        (fun carrier : IdentityECCoframeJetCarrier =>
          (lorentzianMetricOfCoframe carrier.1)⁻¹ row column)
        ((1 : LorentzianCoframe),
          (0 : LorentzianCoframeDerivative)) :=
    (identityEC_metricInverseEntry_contDiffAt row column).differentiableAt
      (by simp)
  have metricDerivativeDifferentiable
      (first second third : LorentzianIndex) :
      DifferentiableAt ℝ
        (fun carrier : IdentityECCoframeJetCarrier =>
          (pointwiseCoframeJetOfCarrier carrier).metricDerivative
            first second third)
        ((1 : LorentzianCoframe),
          (0 : LorentzianCoframeDerivative)) := by
    unfold pointwiseCoframeJetOfCarrier
      PointwiseLorentzianCoframeJet.metricDerivative
    refine DifferentiableAt.fun_sum (u := Finset.univ) ?_
    intro internal _
    have firstProduct : DifferentiableAt ℝ
        (fun carrier : IdentityECCoframeJetCarrier =>
          carrier.2 first internal second * carrier.1 internal third)
        ((1 : LorentzianCoframe),
          (0 : LorentzianCoframeDerivative)) := by
      fun_prop
    have secondProduct : DifferentiableAt ℝ
        (fun carrier : IdentityECCoframeJetCarrier =>
          carrier.1 internal second * carrier.2 first internal third)
        ((1 : LorentzianCoframe),
          (0 : LorentzianCoframeDerivative)) := by
      fun_prop
    exact
      (differentiableAt_const
        (c := minkowskiInternalSign internal)).mul
        (firstProduct.add secondProduct)
  have loweredConnectionDifferentiable
      (lower first second : LorentzianIndex) :
      DifferentiableAt ℝ
        (fun carrier : IdentityECCoframeJetCarrier =>
          (pointwiseCoframeJetOfCarrier carrier).loweredLeviCivitaConnection
            lower first second)
        ((1 : LorentzianCoframe),
          (0 : LorentzianCoframeDerivative)) := by
    unfold PointwiseLorentzianCoframeJet.loweredLeviCivitaConnection
    fun_prop (disch := exact metricDerivativeDifferentiable _ _ _)
  have raisedConnectionDifferentiable
      (upper first second : LorentzianIndex) :
      DifferentiableAt ℝ
        (fun carrier : IdentityECCoframeJetCarrier =>
          (pointwiseCoframeJetOfCarrier carrier).leviCivitaConnection
            upper first second)
        ((1 : LorentzianCoframe),
          (0 : LorentzianCoframeDerivative)) := by
    unfold PointwiseLorentzianCoframeJet.leviCivitaConnection
      PointwiseLorentzianCoframeJet.leviCivitaConnectionVector
      PointwiseLorentzianCoframeJet.metric
      PointwiseLorentzianCoframeJet.loweredLeviCivitaVector
    simp only [Matrix.mulVec, dotProduct]
    refine DifferentiableAt.fun_sum (u := Finset.univ) ?_
    intro lower _
    exact (metricInverseDifferentiable upper lower).mul
      (loweredConnectionDifferentiable lower first second)
  unfold identityECSpinConnectionComponentOfCarrier
    PointwiseLorentzianCoframeJet.lorentzSpinConnection
    PointwiseLorentzianCoframeJet.lorentzSpinConnectionMatrix
    PointwiseLorentzianCoframeJet.coordinateConnectionMatrix
    affineConnectionMatrix
    PointwiseLorentzianCoframeJet.coframeDerivativeMatrix
  simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.of_apply]
  refine DifferentiableAt.fun_sum (u := Finset.univ) ?_
  intro intermediate _
  apply DifferentiableAt.mul
  · apply DifferentiableAt.sub
    · refine DifferentiableAt.fun_sum (u := Finset.univ) ?_
      intro coordinate _
      have coframeEntry : DifferentiableAt ℝ
          (fun carrier : IdentityECCoframeJetCarrier =>
            carrier.1 internalOut coordinate)
          ((1 : LorentzianCoframe),
            (0 : LorentzianCoframeDerivative)) := by
        fun_prop
      exact coframeEntry.mul
        (raisedConnectionDifferentiable coordinate formDirection intermediate)
    · fun_prop
  · exact coframeInverseDifferentiable intermediate internalIn

/-! ## Equal first-order input germs -/

/-- Complete derivative tensor `H(point,-)` as a continuous linear map of
the base point. -/
def identityECQuadraticCoframeDerivativeLinear
    (hessian : CoframeHolonomicSecondJet) :
    BasePoint →L[ℝ] LorentzianCoframeDerivative :=
  ContinuousLinearMap.pi fun derivativeDirection =>
    ContinuousLinearMap.pi fun internal =>
      ContinuousLinearMap.pi fun coordinate =>
        (coframeEntryEvaluation internal coordinate).comp
          ((ContinuousLinearMap.apply ℝ LorentzianCoframe
            (coordinateDirection derivativeDirection)).comp hessian.1)

@[simp] theorem identityECQuadraticCoframeDerivativeLinear_apply
    (hessian : CoframeHolonomicSecondJet)
    (point : BasePoint)
    (derivativeDirection internal coordinate : LorentzianIndex) :
    identityECQuadraticCoframeDerivativeLinear hessian point
        derivativeDirection internal coordinate =
      hessian.1 point (coordinateDirection derivativeDirection)
        internal coordinate :=
  rfl

/-- Genuine nonlinear jet-input path read from the quadratic coframe. -/
def identityECActualQuadraticJetCarrierPath
    (hessian : CoframeHolonomicSecondJet) :
    BasePoint → IdentityECCoframeJetCarrier :=
  fun point =>
    (identityECQuadraticCoframeField hessian point,
      identityECQuadraticCoframeDerivativeLinear hessian point)

/-- Comparison path retaining the same generated derivative tensor while
freezing only the coframe value at the identity. -/
def identityECFrozenCoframeJetCarrierPath
    (hessian : CoframeHolonomicSecondJet) :
    BasePoint → IdentityECCoframeJetCarrier :=
  fun point =>
    ((1 : LorentzianCoframe),
      identityECQuadraticCoframeDerivativeLinear hessian point)

@[simp] theorem identityECActualQuadraticJetCarrierPath_origin
    (hessian : CoframeHolonomicSecondJet) :
    identityECActualQuadraticJetCarrierPath hessian 0 =
      ((1 : LorentzianCoframe),
        (0 : LorentzianCoframeDerivative)) := by
  ext <;> simp [identityECActualQuadraticJetCarrierPath,
    identityECQuadraticCoframeField,
    identityECZeroCoframeFirstJet]

@[simp] theorem identityECFrozenCoframeJetCarrierPath_origin
    (hessian : CoframeHolonomicSecondJet) :
    identityECFrozenCoframeJetCarrierPath hessian 0 =
      ((1 : LorentzianCoframe),
        (0 : LorentzianCoframeDerivative)) := by
  ext <;> simp [identityECFrozenCoframeJetCarrierPath]

theorem identityECActualQuadraticJetCarrierPath_hasFDerivAt_origin
    (hessian : CoframeHolonomicSecondJet) :
    HasFDerivAt (identityECActualQuadraticJetCarrierPath hessian)
      ((0 : BasePoint →L[ℝ] LorentzianCoframe).prod
        (identityECQuadraticCoframeDerivativeLinear hessian)) 0 := by
  have coframeDerivative :
      HasFDerivAt (identityECQuadraticCoframeField hessian)
        (0 : BasePoint →L[ℝ] LorentzianCoframe) 0 := by
    simpa only [identityECQuadraticCoframeField,
      coframeJetAffineLinear_identityECZeroCoframeFirstJet,
      map_zero, add_zero] using
      (coframeFieldOfFirstAndSecondJet_hasFDerivAt
        identityECZeroCoframeFirstJet hessian 0)
  exact coframeDerivative.prodMk
    (identityECQuadraticCoframeDerivativeLinear hessian).hasFDerivAt

theorem identityECFrozenCoframeJetCarrierPath_hasFDerivAt_origin
    (hessian : CoframeHolonomicSecondJet) :
    HasFDerivAt (identityECFrozenCoframeJetCarrierPath hessian)
      ((0 : BasePoint →L[ℝ] LorentzianCoframe).prod
        (identityECQuadraticCoframeDerivativeLinear hessian)) 0 := by
  exact (hasFDerivAt_const (x := (0 : BasePoint))
      (c := (1 : LorentzianCoframe))).prodMk
    (identityECQuadraticCoframeDerivativeLinear hessian).hasFDerivAt

/-- Recomputing the nonlinear producer on the actual quadratic coframe and
freezing its coframe value at `I` give the same first-order output germ.  This
uses differentiability of the producer plus equality of the two input
first germs; no derivative formula for matrix inversion is assumed. -/
theorem identityECSpinConnectionComponent_actual_fderiv_eq_frozen
    (hessian : CoframeHolonomicSecondJet)
    (formDirection internalOut internalIn : LorentzianIndex) :
    fderiv ℝ
        (fun point =>
          identityECSpinConnectionComponentOfCarrier
            formDirection internalOut internalIn
            (identityECActualQuadraticJetCarrierPath hessian point))
        0 =
      fderiv ℝ
        (fun point =>
          identityECSpinConnectionComponentOfCarrier
            formDirection internalOut internalIn
            (identityECFrozenCoframeJetCarrierPath hessian point))
        0 := by
  have outerDerivative :=
    (identityECSpinConnectionComponentOfCarrier_differentiableAt
      formDirection internalOut internalIn).hasFDerivAt
  have outerDerivativeAtActual :
      HasFDerivAt
        (identityECSpinConnectionComponentOfCarrier
          formDirection internalOut internalIn)
        (fderiv ℝ
          (identityECSpinConnectionComponentOfCarrier
            formDirection internalOut internalIn)
          ((1 : LorentzianCoframe),
            (0 : LorentzianCoframeDerivative)))
        (identityECActualQuadraticJetCarrierPath hessian 0) := by
    simpa using outerDerivative
  have outerDerivativeAtFrozen :
      HasFDerivAt
        (identityECSpinConnectionComponentOfCarrier
          formDirection internalOut internalIn)
        (fderiv ℝ
          (identityECSpinConnectionComponentOfCarrier
            formDirection internalOut internalIn)
          ((1 : LorentzianCoframe),
            (0 : LorentzianCoframeDerivative)))
        (identityECFrozenCoframeJetCarrierPath hessian 0) := by
    simpa using outerDerivative
  have actualDerivative := outerDerivativeAtActual.comp 0
    (identityECActualQuadraticJetCarrierPath_hasFDerivAt_origin hessian)
  have frozenDerivative := outerDerivativeAtFrozen.comp 0
    (identityECFrozenCoframeJetCarrierPath_hasFDerivAt_origin hessian)
  change
    fderiv ℝ
        ((identityECSpinConnectionComponentOfCarrier
          formDirection internalOut internalIn) ∘
          identityECActualQuadraticJetCarrierPath hessian) 0 =
      fderiv ℝ
        ((identityECSpinConnectionComponentOfCarrier
          formDirection internalOut internalIn) ∘
          identityECFrozenCoframeJetCarrierPath hessian) 0
  rw [actualDerivative.fderiv, frozenDerivative.fderiv]

/-! ## Exact frozen-coframe linear readout -/

private theorem identityECMinkowskiInternalMetric_inv :
    minkowskiInternalMetric⁻¹ = minkowskiInternalMetric := by
  apply Matrix.inv_eq_left_inv
  rw [minkowskiInternalMetric, Matrix.diagonal_mul_diagonal]
  ext row column
  fin_cases row <;> fin_cases column <;> norm_num

private theorem identityECLorentzianMetricOfCoframe_one_inv :
    (lorentzianMetricOfCoframe (1 : LorentzianCoframe))⁻¹ =
      minkowskiInternalMetric := by
  rw [show lorentzianMetricOfCoframe (1 : LorentzianCoframe) =
      minkowskiInternalMetric by
    simp [lorentzianMetricOfCoframe]]
  exact identityECMinkowskiInternalMetric_inv

/-- Identity coframe carrying an arbitrary first derivative tensor. -/
def identityECCoframeJetOfDerivative
    (derivative : LorentzianCoframeDerivative) :
    PointwiseLorentzianCoframeJet where
  coframe := 1
  derivative := derivative

private theorem identityECCoframeJetOfDerivative_metricDerivative
    (derivative : LorentzianCoframeDerivative)
    (first second third : LorentzianIndex) :
    (identityECCoframeJetOfDerivative derivative).metricDerivative
        first second third =
      minkowskiInternalSign third * derivative first third second +
        minkowskiInternalSign second * derivative first second third := by
  fin_cases second <;> fin_cases third <;>
    simp [identityECCoframeJetOfDerivative,
      PointwiseLorentzianCoframeJet.metricDerivative,
      Matrix.one_apply, minkowskiInternalSign, Fin.sum_univ_four] <;>
    ring

private theorem identityECCoframeJetOfDerivative_leviCivitaConnection
    (derivative : LorentzianCoframeDerivative)
    (upper first second : LorentzianIndex) :
    (identityECCoframeJetOfDerivative derivative).leviCivitaConnection
        upper first second =
      minkowskiInternalSign upper *
        PointwiseLorentzianCoframeJet.loweredLeviCivitaConnection
          (identityECCoframeJetOfDerivative derivative)
          upper first second := by
  fin_cases upper <;>
    simp [identityECCoframeJetOfDerivative,
      PointwiseLorentzianCoframeJet.leviCivitaConnection,
      PointwiseLorentzianCoframeJet.leviCivitaConnectionVector,
      PointwiseLorentzianCoframeJet.loweredLeviCivitaVector,
      PointwiseLorentzianCoframeJet.metric,
      identityECLorentzianMetricOfCoframe_one_inv,
      minkowskiInternalMetric, minkowskiInternalSign,
      Matrix.mulVec, dotProduct, Fin.sum_univ_four]

private theorem identityECCoframeJetOfDerivative_lorentzSpinConnection
    (derivative : LorentzianCoframeDerivative)
    (formDirection internalOut internalIn : LorentzianIndex) :
    (identityECCoframeJetOfDerivative derivative).lorentzSpinConnection
        formDirection internalOut internalIn =
      (identityECCoframeJetOfDerivative derivative).leviCivitaConnection
          internalOut formDirection internalIn -
        derivative formDirection internalOut internalIn := by
  simp [identityECCoframeJetOfDerivative,
    PointwiseLorentzianCoframeJet.lorentzSpinConnection,
    PointwiseLorentzianCoframeJet.lorentzSpinConnectionMatrix,
    PointwiseLorentzianCoframeJet.coordinateConnectionMatrix,
    affineConnectionMatrix,
    PointwiseLorentzianCoframeJet.coframeDerivativeMatrix]

theorem identityECCoframeJetOfDerivative_spinConnection_koszul
    (derivative : LorentzianCoframeDerivative)
    (formDirection internalOut internalIn : LorentzianIndex) :
    (identityECCoframeJetOfDerivative derivative).lorentzSpinConnection
        formDirection internalOut internalIn =
      minkowskiInternalSign internalOut / 2 *
          ((identityECCoframeJetOfDerivative derivative).metricDerivative
              formDirection internalIn internalOut +
            (identityECCoframeJetOfDerivative derivative).metricDerivative
              internalIn formDirection internalOut -
            (identityECCoframeJetOfDerivative derivative).metricDerivative
              internalOut formDirection internalIn) -
        derivative formDirection internalOut internalIn := by
  rw [identityECCoframeJetOfDerivative_lorentzSpinConnection,
    identityECCoframeJetOfDerivative_leviCivitaConnection]
  unfold PointwiseLorentzianCoframeJet.loweredLeviCivitaConnection
  ring

/-- At the identity coframe, the `(form,out,in) = (1,3,1)` nonlinear
Levi--Civita component reads exactly the two indicated derivative slots. -/
theorem identityECSpinConnectionComponentOfCarrier_one_131
    (derivative : LorentzianCoframeDerivative) :
    identityECSpinConnectionComponentOfCarrier 1 3 1
        ((1 : LorentzianCoframe), derivative) =
      derivative 1 1 3 - derivative 3 1 1 := by
  change
    (identityECCoframeJetOfDerivative derivative).lorentzSpinConnection
        1 3 1 =
      _
  rw [identityECCoframeJetOfDerivative_spinConnection_koszul]
  simp_rw [identityECCoframeJetOfDerivative_metricDerivative]
  simp [minkowskiInternalSign]
  ring

/-- At the identity coframe, the `(form,out,in) = (2,2,3)` nonlinear
Levi--Civita component reads exactly the two indicated derivative slots. -/
theorem identityECSpinConnectionComponentOfCarrier_one_223
    (derivative : LorentzianCoframeDerivative) :
    identityECSpinConnectionComponentOfCarrier 2 2 3
        ((1 : LorentzianCoframe), derivative) =
      derivative 3 2 2 - derivative 2 2 3 := by
  change
    (identityECCoframeJetOfDerivative derivative).lorentzSpinConnection
        2 2 3 =
      _
  rw [identityECCoframeJetOfDerivative_spinConnection_koszul]
  simp_rw [identityECCoframeJetOfDerivative_metricDerivative]
  simp [minkowskiInternalSign]
  ring

private theorem basePoint_eq_sum_coordinateDirections
    (point : BasePoint) :
    point =
      ∑ direction : LorentzianIndex,
        point direction • coordinateDirection direction := by
  ext coordinate
  fin_cases coordinate <;>
    simp [coordinateDirection, Fin.sum_univ_four]

private theorem coframeHessian_expand_first
    (hessian : CoframeHolonomicSecondJet)
    (point second : BasePoint)
    (internal coordinate : LorentzianIndex) :
    hessian.1 point second internal coordinate =
      ∑ direction : LorentzianIndex,
        point direction *
          hessian.1 (coordinateDirection direction) second
            internal coordinate := by
  conv_lhs => rw [basePoint_eq_sum_coordinateDirections point]
  rw [map_sum]
  simp_rw [ContinuousLinearMap.map_smul, sum_apply, smul_apply]
  rfl

theorem identityECQuadraticCoframeDerivativeLinear_apply_eq_sum
    (hessian : CoframeHolonomicSecondJet)
    (point : BasePoint)
    (derivativeDirection internal coordinate : LorentzianIndex) :
    identityECQuadraticCoframeDerivativeLinear hessian point
        derivativeDirection internal coordinate =
      ∑ direction : LorentzianIndex,
        point direction *
          hessian.1 (coordinateDirection direction)
            (coordinateDirection derivativeDirection)
            internal coordinate := by
  rw [identityECQuadraticCoframeDerivativeLinear_apply,
    coframeHessian_expand_first]

private theorem identityECFrozen_metricDerivative_eq_sum
    (hessian : CoframeHolonomicSecondJet)
    (point : BasePoint)
    (first second third : LorentzianIndex) :
    PointwiseLorentzianCoframeJet.metricDerivative
        (identityECCoframeJetOfDerivative
          (identityECQuadraticCoframeDerivativeLinear hessian point))
        first second third =
      ∑ derivativeDirection : LorentzianIndex,
        point derivativeDirection *
          identityECCoframeMetricHessian hessian
            derivativeDirection first second third := by
  rw [identityECCoframeJetOfDerivative_metricDerivative]
  simp only [identityECQuadraticCoframeDerivativeLinear_apply_eq_sum,
    identityECCoframeMetricHessian, Finset.mul_sum, mul_add,
    Finset.sum_add_distrib];
    ring_nf

private theorem identityECFrozen_spinConnection_eq_sum
    (hessian : CoframeHolonomicSecondJet)
    (point : BasePoint)
    (formDirection internalOut internalIn : LorentzianIndex) :
    PointwiseLorentzianCoframeJet.lorentzSpinConnection
        (identityECCoframeJetOfDerivative
          (identityECQuadraticCoframeDerivativeLinear hessian point))
        formDirection internalOut internalIn =
      ∑ derivativeDirection : LorentzianIndex,
        point derivativeDirection *
          identityECLeviCivitaSpinConnectionFirstJet hessian
            derivativeDirection formDirection internalOut internalIn := by
  rw [identityECCoframeJetOfDerivative_spinConnection_koszul,
    identityECFrozen_metricDerivative_eq_sum,
    identityECFrozen_metricDerivative_eq_sum,
    identityECFrozen_metricDerivative_eq_sum,
    identityECQuadraticCoframeDerivativeLinear_apply_eq_sum]
  simp only [identityECLeviCivitaSpinConnectionFirstJet,
    Finset.mul_sum, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib];
    ring_nf

/-- Scalar continuous-linear first-germ component encoded by the forward
Koszul symbol. -/
def identityECLeviCivitaSpinConnectionFirstGermComponent
    (hessian : CoframeHolonomicSecondJet)
    (formDirection internalOut internalIn : LorentzianIndex) :
    BasePoint →L[ℝ] ℝ :=
  ∑ derivativeDirection : LorentzianIndex,
    identityECLeviCivitaSpinConnectionFirstJet hessian
        derivativeDirection formDirection internalOut internalIn •
      coframeBaseCoordinate derivativeDirection

/-- With the coframe value frozen at `I`, the existing nonlinear pointwise
producer is exactly the forward Koszul linear germ of the generated
derivative tensor `H(point,-)`. -/
theorem identityECSpinConnectionComponent_frozen_eq_firstGerm
    (hessian : CoframeHolonomicSecondJet)
    (point : BasePoint)
    (formDirection internalOut internalIn : LorentzianIndex) :
    identityECSpinConnectionComponentOfCarrier
        formDirection internalOut internalIn
        (identityECFrozenCoframeJetCarrierPath hessian point) =
      identityECLeviCivitaSpinConnectionFirstGermComponent hessian
        formDirection internalOut internalIn point := by
  change
    PointwiseLorentzianCoframeJet.lorentzSpinConnection
        (identityECCoframeJetOfDerivative
          (identityECQuadraticCoframeDerivativeLinear hessian point))
        formDirection internalOut internalIn = _
  rw [identityECFrozen_spinConnection_eq_sum]
  simp [identityECLeviCivitaSpinConnectionFirstGermComponent,
    coframeBaseCoordinate, mul_comm]

/-! ## Nonlinear origin first-germ theorem -/

/-- The actual nonlinear Levi--Civita connection generated by the quadratic
coframe has exactly the forward coframe-Hessian first jet at the origin. -/
theorem identityECNonlinearLeviCivitaConnection_directionalDerivative_origin
    (hessian : CoframeHolonomicSecondJet)
    (derivativeDirection formDirection internalOut internalIn :
      LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          identityECNonlinearLeviCivitaConnection hessian point
            formDirection internalOut internalIn)
        0 derivativeDirection =
      identityECLeviCivitaSpinConnectionFirstJet hessian
        derivativeDirection formDirection internalOut internalIn := by
  have actualFunctionEquality :
      (fun point =>
        identityECNonlinearLeviCivitaConnection hessian point
          formDirection internalOut internalIn) =
        (fun point =>
          identityECSpinConnectionComponentOfCarrier
            formDirection internalOut internalIn
            (identityECActualQuadraticJetCarrierPath hessian point)) := by
    funext point
    rw [identityECNonlinearLeviCivitaConnection_eq_explicitJet]
    rfl
  have frozenFunctionEquality :
      (fun point =>
        identityECSpinConnectionComponentOfCarrier
          formDirection internalOut internalIn
          (identityECFrozenCoframeJetCarrierPath hessian point)) =
        identityECLeviCivitaSpinConnectionFirstGermComponent hessian
          formDirection internalOut internalIn := by
    funext point
    exact identityECSpinConnectionComponent_frozen_eq_firstGerm
      hessian point formDirection internalOut internalIn
  unfold fieldDirectionalDerivative
  rw [actualFunctionEquality,
    identityECSpinConnectionComponent_actual_fderiv_eq_frozen,
    frozenFunctionEquality,
    (identityECLeviCivitaSpinConnectionFirstGermComponent hessian
      formDirection internalOut internalIn).hasFDerivAt.fderiv]
  fin_cases derivativeDirection <;>
    simp [identityECLeviCivitaSpinConnectionFirstGermComponent,
      coframeBaseCoordinate, coordinateDirection, Fin.sum_univ_four]

/-- On the six canonical internal-pair coordinates, the first germ of the
nonlinear pointwise producer agrees with the previously generated complete
affine Levi--Civita increment. -/
theorem identityECNonlinearLeviCivitaConnection_firstGerm_eq_affineIncrement
    (hessian : CoframeHolonomicSecondJet)
    (derivativeDirection formDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    fieldDirectionalDerivative
        (fun point =>
          identityECNonlinearLeviCivitaConnection hessian point
            formDirection (pairFirst internalPair) (pairSecond internalPair))
        0 derivativeDirection =
      fieldDirectionalDerivative
        (fun point =>
          identityECLeviCivitaAffineConnectionIncrement hessian point
            formDirection (pairFirst internalPair) (pairSecond internalPair))
        0 derivativeDirection := by
  rw [
    identityECNonlinearLeviCivitaConnection_directionalDerivative_origin,
    identityECLeviCivitaAffineConnectionIncrement_directionalDerivative_origin]

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeIdentityECNonlinearLeviCivitaFirstGerm
