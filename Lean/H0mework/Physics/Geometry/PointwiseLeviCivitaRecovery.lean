import H0mework.Physics.Lorentz.RawLorentzianMetricHodgeRecovery

/-!
# Pointwise Levi-Civita connection generated from a Lorentzian coframe jet

This module adds a non-circular positive connection producer between the
computed coframe metric and the still-open smooth Lorentz-connection gate.
The raw input is only a coframe and its coordinate first derivative at one
point.  From that jet it computes

* the Lorentzian metric `eᵀ η e`;
* its product-rule first derivative;
* the lowered Christoffel formula;
* the raised Levi-Civita connection using the computed metric inverse.

On the coframe-nondegenerate slice, Lean proves that the produced connection
is torsion-free, metric-compatible, and unique among pointwise coordinate
connections with those two properties.  Torsion-freeness and compatibility
are theorem outputs; they are not fields of the raw jet.

Boundary: this is a coordinate, first-jet theorem at one point.  It does not
yet construct a smooth connection field, chart-change naturality, a
`so(1,3)` spin connection `ω`, non-Abelian curvature, global section gluing,
or a source-generated coframe jet.  Those remain separate producer gates.
-/

namespace SaturationMonoid
namespace PhysicsCore

open scoped Matrix

noncomputable section

abbrev LorentzianIndex := Fin 4
abbrev LorentzianCoframeDerivative :=
  LorentzianIndex → LorentzianIndex → LorentzianIndex → ℝ
abbrev PointwiseAffineConnection :=
  LorentzianIndex → LorentzianIndex → LorentzianIndex → ℝ

/-- The diagonal coefficient of the fixed internal metric in the chosen
coframe convention. -/
def minkowskiInternalSign (internal : LorentzianIndex) : ℝ :=
  if internal = 0 then -1 else 1

/-- Raw first-order coframe data at one coordinate point.  No connection,
torsion equation, or compatibility certificate is stored. -/
structure PointwiseLorentzianCoframeJet where
  coframe : LorentzianCoframe
  derivative : LorentzianCoframeDerivative

namespace PointwiseLorentzianCoframeJet

/-- The same Lorentzian metric already used by the physical-admissibility
reconstruction, now read from the jet's coframe. -/
def metric (J : PointwiseLorentzianCoframeJet) : LorentzianMetric :=
  lorentzianMetricOfCoframe J.coframe

/-- Product-rule derivative of `eᵀ η e` in the diagonal internal frame.
The indices are `∂_μ g_{νρ}`. -/
def metricDerivative
    (J : PointwiseLorentzianCoframeJet)
    (μ ν ρ : LorentzianIndex) : ℝ :=
  ∑ internal, minkowskiInternalSign internal *
    (J.derivative μ internal ν * J.coframe internal ρ +
      J.coframe internal ν * J.derivative μ internal ρ)

theorem metricDerivative_symm
    (J : PointwiseLorentzianCoframeJet)
    (μ ν ρ : LorentzianIndex) :
    J.metricDerivative μ ν ρ = J.metricDerivative μ ρ ν := by
  unfold metricDerivative
  apply Finset.sum_congr rfl
  intro internal _hinternal
  ring

/-- Christoffel's formula with its first index lowered:
`Γ_{ρμν} = (∂_μ g_{νρ} + ∂_ν g_{μρ} - ∂_ρ g_{μν}) / 2`. -/
def loweredLeviCivitaConnection
    (J : PointwiseLorentzianCoframeJet) : PointwiseAffineConnection :=
  fun ρ μ ν =>
    (J.metricDerivative μ ν ρ +
      J.metricDerivative ν μ ρ -
      J.metricDerivative ρ μ ν) / 2

theorem loweredLeviCivitaConnection_symm
    (J : PointwiseLorentzianCoframeJet)
    (ρ μ ν : LorentzianIndex) :
    J.loweredLeviCivitaConnection ρ μ ν =
      J.loweredLeviCivitaConnection ρ ν μ := by
  unfold loweredLeviCivitaConnection
  rw [J.metricDerivative_symm ρ μ ν]
  ring

theorem metricDerivative_eq_lowered_add
    (J : PointwiseLorentzianCoframeJet)
    (μ ν ρ : LorentzianIndex) :
    J.metricDerivative μ ν ρ =
      J.loweredLeviCivitaConnection ρ μ ν +
        J.loweredLeviCivitaConnection ν μ ρ := by
  unfold loweredLeviCivitaConnection
  rw [J.metricDerivative_symm μ ν ρ]
  ring

def loweredLeviCivitaVector
    (J : PointwiseLorentzianCoframeJet)
    (μ ν : LorentzianIndex) : LorentzianIndex → ℝ :=
  fun ρ => J.loweredLeviCivitaConnection ρ μ ν

theorem loweredLeviCivitaVector_symm
    (J : PointwiseLorentzianCoframeJet)
    (μ ν : LorentzianIndex) :
    J.loweredLeviCivitaVector μ ν =
      J.loweredLeviCivitaVector ν μ := by
  funext ρ
  exact J.loweredLeviCivitaConnection_symm ρ μ ν

/-- Raise the first Christoffel index using the inverse of the metric computed
from the same coframe. -/
def leviCivitaConnectionVector
    (J : PointwiseLorentzianCoframeJet)
    (μ ν : LorentzianIndex) : LorentzianIndex → ℝ :=
  J.metric⁻¹ *ᵥ J.loweredLeviCivitaVector μ ν

/-- The pointwise affine connection produced by the coframe jet. -/
def leviCivitaConnection
    (J : PointwiseLorentzianCoframeJet) : PointwiseAffineConnection :=
  fun upper μ ν => J.leviCivitaConnectionVector μ ν upper

theorem leviCivitaConnection_symm
    (J : PointwiseLorentzianCoframeJet)
    (upper μ ν : LorentzianIndex) :
    J.leviCivitaConnection upper μ ν =
      J.leviCivitaConnection upper ν μ := by
  unfold leviCivitaConnection leviCivitaConnectionVector
  rw [J.loweredLeviCivitaVector_symm μ ν]

theorem metric_mulVec_leviCivitaConnectionVector
    (J : PointwiseLorentzianCoframeJet)
    (hmetric : IsUnit J.metric.det)
    (μ ν : LorentzianIndex) :
    J.metric *ᵥ J.leviCivitaConnectionVector μ ν =
      J.loweredLeviCivitaVector μ ν := by
  rw [leviCivitaConnectionVector, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv J.metric hmetric, Matrix.one_mulVec]

/-- Coordinate expression for `∇_μ g_{νρ}`. -/
def metricCovariantDerivative
    (J : PointwiseLorentzianCoframeJet)
    (connection : PointwiseAffineConnection)
    (μ ν ρ : LorentzianIndex) : ℝ :=
  J.metricDerivative μ ν ρ -
    ∑ upper, J.metric ρ upper * connection upper μ ν -
    ∑ upper, J.metric ν upper * connection upper μ ρ

def TorsionFree (connection : PointwiseAffineConnection) : Prop :=
  ∀ upper μ ν,
    connection upper μ ν = connection upper ν μ

def MetricCompatible
    (J : PointwiseLorentzianCoframeJet)
    (connection : PointwiseAffineConnection) : Prop :=
  ∀ μ ν ρ, J.metricCovariantDerivative connection μ ν ρ = 0

def connectionVector
    (connection : PointwiseAffineConnection)
    (μ ν : LorentzianIndex) : LorentzianIndex → ℝ :=
  fun upper => connection upper μ ν

def lowerConnectionVector
    (J : PointwiseLorentzianCoframeJet)
    (connection : PointwiseAffineConnection)
    (μ ν : LorentzianIndex) : LorentzianIndex → ℝ :=
  J.metric *ᵥ connectionVector connection μ ν

def lowerConnection
    (J : PointwiseLorentzianCoframeJet)
    (connection : PointwiseAffineConnection) : PointwiseAffineConnection :=
  fun ρ μ ν => J.lowerConnectionVector connection μ ν ρ

theorem lowerConnection_symm_of_torsionFree
    (J : PointwiseLorentzianCoframeJet)
    (connection : PointwiseAffineConnection)
    (htorsion : TorsionFree connection)
    (ρ μ ν : LorentzianIndex) :
    J.lowerConnection connection ρ μ ν =
      J.lowerConnection connection ρ ν μ := by
  unfold lowerConnection lowerConnectionVector connectionVector
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro upper _hupper
  rw [htorsion upper μ ν]

theorem metricDerivative_eq_lowerConnection_add_of_metricCompatible
    (J : PointwiseLorentzianCoframeJet)
    (connection : PointwiseAffineConnection)
    (hmetric : J.MetricCompatible connection)
    (μ ν ρ : LorentzianIndex) :
    J.metricDerivative μ ν ρ =
      J.lowerConnection connection ρ μ ν +
        J.lowerConnection connection ν μ ρ := by
  have h := hmetric μ ν ρ
  unfold metricCovariantDerivative at h
  change
    J.metricDerivative μ ν ρ -
      J.lowerConnection connection ρ μ ν -
        J.lowerConnection connection ν μ ρ = 0 at h
  linarith

/-- The pointwise Koszul calculation: torsion-free metric-compatible data
must have the lowered Christoffel coefficients computed from the jet. -/
theorem lowerConnection_eq_loweredLeviCivitaConnection
    (J : PointwiseLorentzianCoframeJet)
    (connection : PointwiseAffineConnection)
    (htorsion : TorsionFree connection)
    (hmetric : J.MetricCompatible connection)
    (ρ μ ν : LorentzianIndex) :
    J.lowerConnection connection ρ μ ν =
      J.loweredLeviCivitaConnection ρ μ ν := by
  have h1 :=
    J.metricDerivative_eq_lowerConnection_add_of_metricCompatible
      connection hmetric μ ν ρ
  have h2 :=
    J.metricDerivative_eq_lowerConnection_add_of_metricCompatible
      connection hmetric ν μ ρ
  have h3 :=
    J.metricDerivative_eq_lowerConnection_add_of_metricCompatible
      connection hmetric ρ μ ν
  have hs1 :=
    J.lowerConnection_symm_of_torsionFree connection htorsion ρ μ ν
  have hs2 :=
    J.lowerConnection_symm_of_torsionFree connection htorsion μ ν ρ
  have hs3 :=
    J.lowerConnection_symm_of_torsionFree connection htorsion ν ρ μ
  unfold loweredLeviCivitaConnection
  linarith

theorem metricCovariantDerivative_leviCivitaConnection_eq_zero
    (J : PointwiseLorentzianCoframeJet)
    (hmetric : IsUnit J.metric.det)
    (μ ν ρ : LorentzianIndex) :
    J.metricCovariantDerivative J.leviCivitaConnection μ ν ρ = 0 := by
  change
    J.metricDerivative μ ν ρ -
      (J.metric *ᵥ J.leviCivitaConnectionVector μ ν) ρ -
        (J.metric *ᵥ J.leviCivitaConnectionVector μ ρ) ν = 0
  rw [J.metric_mulVec_leviCivitaConnectionVector hmetric μ ν,
    J.metric_mulVec_leviCivitaConnectionVector hmetric μ ρ]
  rw [J.metricDerivative_eq_lowered_add]
  simp only [loweredLeviCivitaVector]
  ring

/-- Uniqueness of the computed pointwise connection in the torsion-free,
metric-compatible class. -/
theorem leviCivitaConnection_unique
    (J : PointwiseLorentzianCoframeJet)
    (hmetric : IsUnit J.metric.det)
    (connection : PointwiseAffineConnection)
    (htorsion : TorsionFree connection)
    (hcompatible : J.MetricCompatible connection) :
    connection = J.leviCivitaConnection := by
  funext upper μ ν
  have hinverse :
      J.metric⁻¹ *ᵥ J.lowerConnectionVector connection μ ν =
        connectionVector connection μ ν := by
    rw [lowerConnectionVector, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul J.metric hmetric, Matrix.one_mulVec]
  have hlower :
      J.lowerConnectionVector connection μ ν =
        J.loweredLeviCivitaVector μ ν := by
    funext ρ
    exact J.lowerConnection_eq_loweredLeviCivitaConnection
      connection htorsion hcompatible ρ μ ν
  calc
    connection upper μ ν =
        (connectionVector connection μ ν) upper := rfl
    _ = (J.metric⁻¹ *ᵥ J.lowerConnectionVector connection μ ν) upper := by
        rw [hinverse]
    _ = (J.metric⁻¹ *ᵥ J.loweredLeviCivitaVector μ ν) upper := by
        rw [hlower]
    _ = J.leviCivitaConnection upper μ ν := rfl

theorem minkowskiInternalMetric_det :
    Matrix.det minkowskiInternalMetric = -1 := by
  rw [minkowskiInternalMetric, Matrix.det_diagonal]
  norm_num [Fin.prod_univ_succ]

theorem metric_det
    (J : PointwiseLorentzianCoframeJet) :
    Matrix.det J.metric = -(Matrix.det J.coframe) ^ 2 := by
  simp [metric, lorentzianMetricOfCoframe, Matrix.det_mul,
    minkowskiInternalMetric_det, Matrix.det_transpose]
  ring

theorem metric_det_ne_zero_of_coframe
    (J : PointwiseLorentzianCoframeJet)
    (hcoframe : Matrix.det J.coframe ≠ 0) :
    Matrix.det J.metric ≠ 0 := by
  rw [J.metric_det]
  exact neg_ne_zero.mpr (pow_ne_zero 2 hcoframe)

theorem metric_det_isUnit_of_coframe
    (J : PointwiseLorentzianCoframeJet)
    (hcoframe : Matrix.det J.coframe ≠ 0) :
    IsUnit J.metric.det := by
  exact isUnit_iff_ne_zero.mpr
    (J.metric_det_ne_zero_of_coframe hcoframe)

theorem leviCivitaConnection_torsionFree
    (J : PointwiseLorentzianCoframeJet) :
    TorsionFree J.leviCivitaConnection :=
  J.leviCivitaConnection_symm

theorem leviCivitaConnection_metricCompatible
    (J : PointwiseLorentzianCoframeJet)
    (hcoframe : Matrix.det J.coframe ≠ 0) :
    J.MetricCompatible J.leviCivitaConnection :=
  J.metricCovariantDerivative_leviCivitaConnection_eq_zero
    (J.metric_det_isUnit_of_coframe hcoframe)

/-- Certified theorem output of the coframe-jet producer. -/
structure LeviCivitaOutput
    (J : PointwiseLorentzianCoframeJet) where
  connection : PointwiseAffineConnection
  torsionFree : TorsionFree connection
  metricCompatible : J.MetricCompatible connection

/-- A nondegenerate coframe jet directly produces its unique pointwise
torsion-free metric-compatible connection. -/
def produceLeviCivitaConnection
    (J : PointwiseLorentzianCoframeJet)
    (hcoframe : Matrix.det J.coframe ≠ 0) :
    LeviCivitaOutput J where
  connection := J.leviCivitaConnection
  torsionFree := J.leviCivitaConnection_torsionFree
  metricCompatible := J.leviCivitaConnection_metricCompatible hcoframe

@[simp] theorem produceLeviCivitaConnection_connection
    (J : PointwiseLorentzianCoframeJet)
    (hcoframe : Matrix.det J.coframe ≠ 0) :
    (J.produceLeviCivitaConnection hcoframe).connection =
      J.leviCivitaConnection :=
  rfl

theorem produceLeviCivitaConnection_unique
    (J : PointwiseLorentzianCoframeJet)
    (hcoframe : Matrix.det J.coframe ≠ 0)
    (connection : PointwiseAffineConnection)
    (htorsion : TorsionFree connection)
    (hcompatible : J.MetricCompatible connection) :
    connection = (J.produceLeviCivitaConnection hcoframe).connection := by
  exact J.leviCivitaConnection_unique
    (J.metric_det_isUnit_of_coframe hcoframe)
    connection htorsion hcompatible

end PointwiseLorentzianCoframeJet

end
end PhysicsCore
end SaturationMonoid
