import H0mework.Physics.Geometry.PointwiseLeviCivitaRecovery

/-!
# Pointwise Lorentz spin connection generated from a coframe first jet

This module closes the next finite-dimensional producer step after
`PointwiseLeviCivitaRecovery`.  The raw input remains only a coframe and its
coordinate first derivative.  From the already computed Levi-Civita
connection it defines

`omega_mu = (e * Gamma_mu - partial_mu e) * e^-1`.

On the nondegenerate-coframe slice, Lean proves both the tetrad postulate and
the Lorentz Lie-algebra law

`omega_mu^T * eta + eta * omega_mu = 0`.

Neither law is stored in the raw jet.  They are theorem outputs of the same
coframe-jet producer.

Boundary: this is still a first-jet theorem at one coordinate point.  It does
not construct a smooth spin-connection field, chart or local-Lorentz
naturality, curvature, principal-bundle descent, global gluing, or a
source-generated coframe jet.
-/

namespace SaturationMonoid
namespace PhysicsCore

open scoped Matrix

noncomputable section

abbrev PointwiseLorentzSpinConnection :=
  LorentzianIndex → LorentzianIndex → LorentzianIndex → ℝ

/-- Matrix readout of the internal indices of a pointwise spin connection at
one coordinate direction. -/
def spinConnectionMatrix
    (connection : PointwiseLorentzSpinConnection)
    (mu : LorentzianIndex) : LorentzianMetric :=
  Matrix.of fun internalOut internalIn => connection mu internalOut internalIn

/-- Matrix readout of the coordinate indices of a pointwise affine
connection in one derivative direction. -/
def affineConnectionMatrix
    (connection : PointwiseAffineConnection)
    (mu : LorentzianIndex) : LorentzianMetric :=
  Matrix.of fun upper lower => connection upper mu lower

/-- The coordinate tetrad postulate for an affine connection and an internal
frame connection. -/
def TetradCompatible
    (J : PointwiseLorentzianCoframeJet)
    (affine : PointwiseAffineConnection)
    (spin : PointwiseLorentzSpinConnection) : Prop :=
  ∀ mu internal coordinate,
    J.derivative mu internal coordinate -
        ∑ upper, affine upper mu coordinate * J.coframe internal upper +
        ∑ internalIn, spin mu internal internalIn *
          J.coframe internalIn coordinate = 0

/-- Pointwise membership in `so(1,3)` for the fixed internal metric. -/
def LorentzSkew
    (connection : PointwiseLorentzSpinConnection) : Prop :=
  ∀ mu,
    (spinConnectionMatrix connection mu).transpose *
          minkowskiInternalMetric +
        minkowskiInternalMetric * spinConnectionMatrix connection mu = 0

namespace PointwiseLorentzianCoframeJet

def coframeDerivativeMatrix
    (J : PointwiseLorentzianCoframeJet)
    (mu : LorentzianIndex) : LorentzianCoframe :=
  Matrix.of fun internal coordinate => J.derivative mu internal coordinate

def coordinateConnectionMatrix
    (J : PointwiseLorentzianCoframeJet)
    (mu : LorentzianIndex) : LorentzianMetric :=
  affineConnectionMatrix J.leviCivitaConnection mu

def metricDerivativeMatrix
    (J : PointwiseLorentzianCoframeJet)
    (mu : LorentzianIndex) : LorentzianMetric :=
  Matrix.of fun first second => J.metricDerivative mu first second

theorem minkowskiInternalMetric_eq_diagonal_sign :
    minkowskiInternalMetric = Matrix.diagonal minkowskiInternalSign := by
  ext first second
  fin_cases first <;> fin_cases second <;>
    simp [minkowskiInternalMetric, minkowskiInternalSign]

theorem transpose_mul_minkowski_mul_apply
    (left right : LorentzianCoframe)
    (first second : LorentzianIndex) :
    (left.transpose * minkowskiInternalMetric * right) first second =
      ∑ internal, minkowskiInternalSign internal *
        left internal first * right internal second := by
  rw [minkowskiInternalMetric_eq_diagonal_sign]
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro internal _hinternal
  rw [Matrix.mul_diagonal]
  simp only [Matrix.transpose_apply]
  ring

theorem metric_symm
    (J : PointwiseLorentzianCoframeJet)
    (first second : LorentzianIndex) :
    J.metric first second = J.metric second first := by
  rw [metric, lorentzianMetricOfCoframe,
    transpose_mul_minkowski_mul_apply,
    transpose_mul_minkowski_mul_apply]
  apply Finset.sum_congr rfl
  intro internal _hinternal
  ring

/-- Matrix form of the coframe product rule for `partial_mu g`. -/
theorem metricDerivativeMatrix_eq_productRule
    (J : PointwiseLorentzianCoframeJet)
    (mu : LorentzianIndex) :
    J.metricDerivativeMatrix mu =
      (J.coframeDerivativeMatrix mu).transpose *
          minkowskiInternalMetric * J.coframe +
        J.coframe.transpose * minkowskiInternalMetric *
          J.coframeDerivativeMatrix mu := by
  ext first second
  change
    (∑ internal, minkowskiInternalSign internal *
      (J.derivative mu internal first * J.coframe internal second +
        J.coframe internal first * J.derivative mu internal second)) = _
  rw [Matrix.add_apply,
    transpose_mul_minkowski_mul_apply,
    transpose_mul_minkowski_mul_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro internal _hinternal
  simp only [coframeDerivativeMatrix, Matrix.of_apply]
  ring

/-- Matrix form of metric compatibility for the computed Levi-Civita
connection. -/
theorem metricDerivativeMatrix_eq_connectionRule
    (J : PointwiseLorentzianCoframeJet)
    (hcoframe : Matrix.det J.coframe ≠ 0)
    (mu : LorentzianIndex) :
    J.metricDerivativeMatrix mu =
      (J.coordinateConnectionMatrix mu).transpose * J.metric +
        J.metric * J.coordinateConnectionMatrix mu := by
  ext first second
  have hmetric :=
    J.leviCivitaConnection_metricCompatible hcoframe mu first second
  unfold metricCovariantDerivative at hmetric
  simp only [metricDerivativeMatrix, coordinateConnectionMatrix,
    affineConnectionMatrix, Matrix.add_apply, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.of_apply]
  have hfirst :
      (∑ upper,
        J.leviCivitaConnection upper mu first * J.metric upper second) =
        ∑ upper,
          J.metric second upper *
            J.leviCivitaConnection upper mu first := by
    apply Finset.sum_congr rfl
    intro upper _hupper
    rw [J.metric_symm upper second]
    ring
  rw [hfirst]
  linarith

/-- Internal connection matrix computed from the coframe jet and the already
generated Levi-Civita connection. -/
def lorentzSpinConnectionMatrix
    (J : PointwiseLorentzianCoframeJet)
    (mu : LorentzianIndex) : LorentzianMetric :=
  (J.coframe * J.coordinateConnectionMatrix mu -
      J.coframeDerivativeMatrix mu) * J.coframe⁻¹

def lorentzSpinConnection
    (J : PointwiseLorentzianCoframeJet) :
    PointwiseLorentzSpinConnection :=
  fun mu internalOut internalIn =>
    J.lorentzSpinConnectionMatrix mu internalOut internalIn

@[simp] theorem spinConnectionMatrix_lorentzSpinConnection
    (J : PointwiseLorentzianCoframeJet)
    (mu : LorentzianIndex) :
    spinConnectionMatrix J.lorentzSpinConnection mu =
      J.lorentzSpinConnectionMatrix mu :=
  rfl

theorem lorentzSpinConnectionMatrix_mul_coframe
    (J : PointwiseLorentzianCoframeJet)
    (hcoframe : IsUnit J.coframe.det)
    (mu : LorentzianIndex) :
    J.lorentzSpinConnectionMatrix mu * J.coframe =
      J.coframe * J.coordinateConnectionMatrix mu -
        J.coframeDerivativeMatrix mu := by
  rw [lorentzSpinConnectionMatrix, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul J.coframe hcoframe, Matrix.mul_one]

/-- The computed affine and spin connections satisfy the tetrad postulate. -/
theorem tetradPostulate_lorentzSpinConnection
    (J : PointwiseLorentzianCoframeJet)
    (hcoframe : IsUnit J.coframe.det)
    (mu internal coordinate : LorentzianIndex) :
    J.derivative mu internal coordinate -
        ∑ upper, J.leviCivitaConnection upper mu coordinate *
          J.coframe internal upper +
        ∑ internalIn,
          J.lorentzSpinConnection mu internal internalIn *
            J.coframe internalIn coordinate = 0 := by
  have hmatrix := congrFun
    (congrFun
      (J.lorentzSpinConnectionMatrix_mul_coframe hcoframe mu)
      internal)
    coordinate
  simp only [Matrix.mul_apply, Matrix.sub_apply,
    coordinateConnectionMatrix, affineConnectionMatrix,
    coframeDerivativeMatrix, Matrix.of_apply] at hmatrix
  change
    J.derivative mu internal coordinate -
        ∑ upper, J.leviCivitaConnection upper mu coordinate *
          J.coframe internal upper +
        ∑ internalIn,
          J.lorentzSpinConnectionMatrix mu internal internalIn *
            J.coframe internalIn coordinate = 0
  rw [Finset.sum_congr rfl (fun upper _ => mul_comm _ _)]
  linarith

theorem leviCivita_lorentzSpinConnection_tetradCompatible
    (J : PointwiseLorentzianCoframeJet)
    (hcoframe : Matrix.det J.coframe ≠ 0) :
    TetradCompatible J J.leviCivitaConnection
      J.lorentzSpinConnection := by
  exact J.tetradPostulate_lorentzSpinConnection
    (isUnit_iff_ne_zero.mpr hcoframe)

/-- Matrix form of an arbitrary supplied tetrad-postulate proof. -/
theorem spinConnectionMatrix_mul_coframe_of_tetradCompatible
    (J : PointwiseLorentzianCoframeJet)
    (affine : PointwiseAffineConnection)
    (spin : PointwiseLorentzSpinConnection)
    (htetrad : TetradCompatible J affine spin)
    (mu : LorentzianIndex) :
    spinConnectionMatrix spin mu * J.coframe =
      J.coframe * affineConnectionMatrix affine mu -
        J.coframeDerivativeMatrix mu := by
  ext internal coordinate
  have h := htetrad mu internal coordinate
  simp only [Matrix.mul_apply, Matrix.sub_apply, spinConnectionMatrix,
    affineConnectionMatrix, coframeDerivativeMatrix, Matrix.of_apply]
  rw [Finset.sum_congr rfl (fun upper _ => mul_comm _ _)] at h
  linarith

/-- With the affine Levi-Civita connection fixed, the nondegenerate coframe
makes the tetrad-compatible internal connection unique. -/
theorem lorentzSpinConnection_unique_for_leviCivita
    (J : PointwiseLorentzianCoframeJet)
    (hcoframe : Matrix.det J.coframe ≠ 0)
    (spin : PointwiseLorentzSpinConnection)
    (htetrad : TetradCompatible J J.leviCivitaConnection spin) :
    spin = J.lorentzSpinConnection := by
  have hcoframeUnit : IsUnit J.coframe.det :=
    isUnit_iff_ne_zero.mpr hcoframe
  funext mu internalOut internalIn
  have hsupplied :=
    J.spinConnectionMatrix_mul_coframe_of_tetradCompatible
      J.leviCivitaConnection spin htetrad mu
  have hproduced :=
    J.lorentzSpinConnectionMatrix_mul_coframe hcoframeUnit mu
  have hmatrixMul :
      spinConnectionMatrix spin mu * J.coframe =
        J.lorentzSpinConnectionMatrix mu * J.coframe := by
    exact hsupplied.trans hproduced.symm
  have hcancel := congrArg (fun M => M * J.coframe⁻¹) hmatrixMul
  have hmatrix :
      spinConnectionMatrix spin mu =
        J.lorentzSpinConnectionMatrix mu := by
    calc
      spinConnectionMatrix spin mu =
          spinConnectionMatrix spin mu *
            (J.coframe * J.coframe⁻¹) := by
              rw [Matrix.mul_nonsing_inv J.coframe hcoframeUnit]
              simp
      _ = (spinConnectionMatrix spin mu * J.coframe) *
            J.coframe⁻¹ := by
              rw [Matrix.mul_assoc]
      _ = (J.lorentzSpinConnectionMatrix mu * J.coframe) *
            J.coframe⁻¹ := hcancel
      _ = J.lorentzSpinConnectionMatrix mu *
            (J.coframe * J.coframe⁻¹) := by
              rw [Matrix.mul_assoc]
      _ = J.lorentzSpinConnectionMatrix mu := by
              rw [Matrix.mul_nonsing_inv J.coframe hcoframeUnit]
              simp
  exact congrFun (congrFun hmatrix internalOut) internalIn

def lorentzSkewMatrix
    (J : PointwiseLorentzianCoframeJet)
    (mu : LorentzianIndex) : LorentzianMetric :=
  (J.lorentzSpinConnectionMatrix mu).transpose *
      minkowskiInternalMetric +
    minkowskiInternalMetric * J.lorentzSpinConnectionMatrix mu

/-- Metric compatibility of `Gamma` and the coframe product rule imply that
the internal connection is Lorentz-skew after sandwiching by the coframe. -/
theorem coframe_sandwich_lorentzSkewMatrix_eq_zero
    (J : PointwiseLorentzianCoframeJet)
    (hcoframe : Matrix.det J.coframe ≠ 0)
    (mu : LorentzianIndex) :
    J.coframe.transpose * J.lorentzSkewMatrix mu * J.coframe = 0 := by
  have hcoframeUnit : IsUnit J.coframe.det :=
    isUnit_iff_ne_zero.mpr hcoframe
  have hframe :=
    J.lorentzSpinConnectionMatrix_mul_coframe hcoframeUnit mu
  have hframeTranspose := congrArg Matrix.transpose hframe
  simp only [Matrix.transpose_mul, Matrix.transpose_sub] at hframeTranspose
  have hproduct := J.metricDerivativeMatrix_eq_productRule mu
  have hconnection :=
    J.metricDerivativeMatrix_eq_connectionRule hcoframe mu
  rw [lorentzSkewMatrix]
  calc
    J.coframe.transpose *
          ((J.lorentzSpinConnectionMatrix mu).transpose *
              minkowskiInternalMetric +
            minkowskiInternalMetric *
              J.lorentzSpinConnectionMatrix mu) *
        J.coframe =
      (J.coframe.transpose *
          (J.lorentzSpinConnectionMatrix mu).transpose) *
          minkowskiInternalMetric * J.coframe +
        J.coframe.transpose * minkowskiInternalMetric *
          (J.lorentzSpinConnectionMatrix mu * J.coframe) := by
            noncomm_ring
    _ =
      ((J.coordinateConnectionMatrix mu).transpose *
          J.coframe.transpose -
          (J.coframeDerivativeMatrix mu).transpose) *
            minkowskiInternalMetric * J.coframe +
        J.coframe.transpose * minkowskiInternalMetric *
          (J.coframe * J.coordinateConnectionMatrix mu -
            J.coframeDerivativeMatrix mu) := by
              rw [hframeTranspose, hframe]
    _ =
      ((J.coordinateConnectionMatrix mu).transpose * J.metric +
          J.metric * J.coordinateConnectionMatrix mu) -
        ((J.coframeDerivativeMatrix mu).transpose *
            minkowskiInternalMetric * J.coframe +
          J.coframe.transpose * minkowskiInternalMetric *
            J.coframeDerivativeMatrix mu) := by
              rw [metric, lorentzianMetricOfCoframe]
              noncomm_ring
    _ = 0 := by
      rw [← hconnection, ← hproduct]
      simp

/-- Since the coframe is invertible, the sandwich result is exactly the
`so(1,3)` skew law. -/
theorem lorentzSkewMatrix_eq_zero
    (J : PointwiseLorentzianCoframeJet)
    (hcoframe : Matrix.det J.coframe ≠ 0)
    (mu : LorentzianIndex) :
    J.lorentzSkewMatrix mu = 0 := by
  have hcoframeUnit : IsUnit J.coframe.det :=
    isUnit_iff_ne_zero.mpr hcoframe
  have htransposeUnit : IsUnit J.coframe.transpose.det := by
    rw [Matrix.det_transpose]
    exact hcoframeUnit
  have hsandwich :=
    J.coframe_sandwich_lorentzSkewMatrix_eq_zero hcoframe mu
  have hcancel := congrArg
    (fun M => J.coframe.transpose⁻¹ * M * J.coframe⁻¹)
    hsandwich
  simp only [Matrix.mul_zero, Matrix.zero_mul] at hcancel
  calc
    J.lorentzSkewMatrix mu =
        (J.coframe.transpose⁻¹ * J.coframe.transpose) *
          J.lorentzSkewMatrix mu *
            (J.coframe * J.coframe⁻¹) := by
              rw [Matrix.nonsing_inv_mul J.coframe.transpose
                  htransposeUnit,
                Matrix.mul_nonsing_inv J.coframe hcoframeUnit]
              simp
    _ = J.coframe.transpose⁻¹ *
          (J.coframe.transpose * J.lorentzSkewMatrix mu * J.coframe) *
            J.coframe⁻¹ := by
              noncomm_ring
    _ = 0 := hcancel

theorem lorentzSpinConnection_lorentzSkew
    (J : PointwiseLorentzianCoframeJet)
    (hcoframe : Matrix.det J.coframe ≠ 0) :
    LorentzSkew J.lorentzSpinConnection := by
  intro mu
  change J.lorentzSkewMatrix mu = 0
  exact J.lorentzSkewMatrix_eq_zero hcoframe mu

/-! ## Certified pointwise Lorentz producer -/

/-- The complete theorem output produced from a nondegenerate coframe first
jet.  None of these proof fields occurs in the raw jet. -/
structure LorentzSpinConnectionOutput
    (J : PointwiseLorentzianCoframeJet) where
  affineConnection : PointwiseAffineConnection
  spinConnection : PointwiseLorentzSpinConnection
  affineTorsionFree : TorsionFree affineConnection
  affineMetricCompatible : J.MetricCompatible affineConnection
  tetradCompatible : TetradCompatible J affineConnection spinConnection
  lorentzSkew : LorentzSkew spinConnection

/-- A nondegenerate coframe first jet produces the affine Levi-Civita
connection and its pointwise `so(1,3)` spin connection. -/
def produceLorentzSpinConnection
    (J : PointwiseLorentzianCoframeJet)
    (hcoframe : Matrix.det J.coframe ≠ 0) :
    LorentzSpinConnectionOutput J where
  affineConnection := J.leviCivitaConnection
  spinConnection := J.lorentzSpinConnection
  affineTorsionFree := J.leviCivitaConnection_torsionFree
  affineMetricCompatible :=
    J.leviCivitaConnection_metricCompatible hcoframe
  tetradCompatible :=
    J.leviCivita_lorentzSpinConnection_tetradCompatible hcoframe
  lorentzSkew := J.lorentzSpinConnection_lorentzSkew hcoframe

@[simp] theorem produceLorentzSpinConnection_affine
    (J : PointwiseLorentzianCoframeJet)
    (hcoframe : Matrix.det J.coframe ≠ 0) :
    (J.produceLorentzSpinConnection hcoframe).affineConnection =
      J.leviCivitaConnection :=
  rfl

@[simp] theorem produceLorentzSpinConnection_spin
    (J : PointwiseLorentzianCoframeJet)
    (hcoframe : Matrix.det J.coframe ≠ 0) :
    (J.produceLorentzSpinConnection hcoframe).spinConnection =
      J.lorentzSpinConnection :=
  rfl

/-- Joint uniqueness: any torsion-free metric-compatible affine connection
and any tetrad-compatible internal connection coincide with the produced
pair.  Lorentz-skewness need not be assumed; it is already forced for the
produced pair by the preceding theorem. -/
theorem produceLorentzSpinConnection_unique
    (J : PointwiseLorentzianCoframeJet)
    (hcoframe : Matrix.det J.coframe ≠ 0)
    (affine : PointwiseAffineConnection)
    (spin : PointwiseLorentzSpinConnection)
    (htorsion : TorsionFree affine)
    (hmetric : J.MetricCompatible affine)
    (htetrad : TetradCompatible J affine spin) :
    affine = (J.produceLorentzSpinConnection hcoframe).affineConnection ∧
      spin = (J.produceLorentzSpinConnection hcoframe).spinConnection := by
  have haffine : affine = J.leviCivitaConnection :=
    J.leviCivitaConnection_unique
      (J.metric_det_isUnit_of_coframe hcoframe)
      affine htorsion hmetric
  subst affine
  exact ⟨rfl,
    J.lorentzSpinConnection_unique_for_leviCivita
      hcoframe spin htetrad⟩

end PointwiseLorentzianCoframeJet

end
end PhysicsCore
end SaturationMonoid
