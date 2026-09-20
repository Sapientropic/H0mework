import H0mework.Realization.Fibres.P574

/-!
# Proposition 575: sigma-zero bounded lifts preserve metric contraction

P574 transported norm and pointwise operator bounds.  Lemma 3, however, is
stated in metric form:

`dist (T x) (T y) ≤ q * dist x y`.

This file closes that last local gap for bounded linear reducers.  A standard
bounded linear map is metrically contractive iff its sigma-zero lift is
metrically contractive.  Consequently the contraction side of the observable
bisimulation / fading-memory lemma can be checked on the ordinary carrier and
then transported through the sigma-zero specialization without changing the
constant.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

universe u v w x y

/-! ## Normed zero-fiber distance -/

/-- The normed zero-fiber distance is exactly carrier distance after forgetting
headroom.  This is the normed-space instance analogue of P554's induced metric
statement. -/
@[simp] theorem sigmaZeroRelaxed_dist_eq_normed
    (K : Type u) [Zero K]
    (X : Type v) (H : Type w) [Inhabited H]
    [NormedAddCommGroup X]
    (a b : SigmaRelaxedObject K X H (0 : K)) :
    letI := sigmaZeroRelaxedAddCommGroupInst K X H
    letI := sigmaZeroRelaxedNormedAddCommGroupInst K X H
    dist a b =
      dist
        (sigmaZeroForget (K := K) (X := X) (H := H) a)
        (sigmaZeroForget (K := K) (X := X) (H := H) b) :=
  rfl

/-! ## Standard bounded operators give metric contractions -/

/-- THEOREM 1: a pointwise norm bound on a bounded linear map implies the
corresponding metric contraction bound. -/
theorem continuousLinearMap_dist_contract_of_pointwise_bound
    (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (X : Type v) (Y : Type w)
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (f : X →L[𝕜] Y) (q : ℝ)
    (hpoint : ∀ x : X, ‖f x‖ ≤ q * ‖x‖) :
    ∀ x y : X, dist (f x) (f y) ≤ q * dist x y := by
  intro x y
  calc
    dist (f x) (f y) = ‖f x - f y‖ := by
      rw [dist_eq_norm]
    _ = ‖f (x - y)‖ := by
      rw [map_sub]
    _ ≤ q * ‖x - y‖ := hpoint (x - y)
    _ = q * dist x y := by
      rw [dist_eq_norm]

/-- THEOREM 2: an operator-norm bound on a bounded linear map implies the
corresponding metric contraction bound. -/
theorem continuousLinearMap_dist_contract_of_norm_le
    (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (X : Type v) (Y : Type w)
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (f : X →L[𝕜] Y) (q : ℝ)
    (hnorm : ‖f‖ ≤ q) :
    ∀ x y : X, dist (f x) (f y) ≤ q * dist x y := by
  apply continuousLinearMap_dist_contract_of_pointwise_bound 𝕜 X Y f q
  intro x
  calc
    ‖f x‖ ≤ ‖f‖ * ‖x‖ := f.le_opNorm x
    _ ≤ q * ‖x‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg x)

/-! ## Sigma-zero metric contraction transport -/

/-- THEOREM 3: a metric contraction bound is preserved and reflected by
sigma-zero bounded-operator lifting. -/
@[simp] theorem sigmaZeroLiftContinuousLinearMap_dist_contract_iff
    (K : Type u) [Zero K] (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (X : Type v) (Y : Type w) (HX : Type x) (HY : Type y)
    [Inhabited HX] [Inhabited HY]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (f : X →L[𝕜] Y) (q : ℝ) :
    letI := sigmaZeroRelaxedAddCommGroupInst K X HX
    letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
    letI := sigmaZeroRelaxedNormedAddCommGroupInst K X HX
    letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X HX
    letI := sigmaZeroRelaxedAddCommGroupInst K Y HY
    letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
    letI := sigmaZeroRelaxedNormedAddCommGroupInst K Y HY
    letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 Y HY
    (∀ z w : SigmaRelaxedObject K X HX (0 : K),
        dist (sigmaZeroLiftContinuousLinearMap K 𝕜 X Y HX HY f z)
          (sigmaZeroLiftContinuousLinearMap K 𝕜 X Y HX HY f w) ≤
            q * dist z w) ↔
      ∀ x y : X, dist (f x) (f y) ≤ q * dist x y := by
  letI := sigmaZeroRelaxedAddCommGroupInst K X HX
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
  letI := sigmaZeroRelaxedNormedAddCommGroupInst K X HX
  letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X HX
  letI := sigmaZeroRelaxedAddCommGroupInst K Y HY
  letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
  letI := sigmaZeroRelaxedNormedAddCommGroupInst K Y HY
  letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 Y HY
  constructor
  · intro h x y
    have hxy := h
      (sigmaZeroEmbed (K := K) (X := X) (H := HX) x)
      (sigmaZeroEmbed (K := K) (X := X) (H := HX) y)
    simpa [sigmaZeroRelaxed_dist_eq_normed,
      sigmaZeroForget_liftContinuousLinearMap] using hxy
  · intro h z w
    calc
      dist (sigmaZeroLiftContinuousLinearMap K 𝕜 X Y HX HY f z)
          (sigmaZeroLiftContinuousLinearMap K 𝕜 X Y HX HY f w) =
          dist
            (f (sigmaZeroForget (K := K) (X := X) (H := HX) z))
            (f (sigmaZeroForget (K := K) (X := X) (H := HX) w)) := by
            rw [sigmaZeroRelaxed_dist_eq_normed]
            simp [sigmaZeroForget_liftContinuousLinearMap]
      _ ≤ q *
          dist
            (sigmaZeroForget (K := K) (X := X) (H := HX) z)
            (sigmaZeroForget (K := K) (X := X) (H := HX) w) := by
            exact h _ _
      _ = q * dist z w := by
            rw [sigmaZeroRelaxed_dist_eq_normed]

/-- THEOREM 4: if the original bounded operator has norm at most `q`, then
its sigma-zero lift is a metric contraction with the same constant. -/
theorem sigmaZeroLiftContinuousLinearMap_dist_contract_of_norm_le
    (K : Type u) [Zero K] (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (X : Type v) (Y : Type w) (HX : Type x) (HY : Type y)
    [Inhabited HX] [Inhabited HY]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (f : X →L[𝕜] Y) (q : ℝ)
    (hnorm : ‖f‖ ≤ q) :
    letI := sigmaZeroRelaxedAddCommGroupInst K X HX
    letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
    letI := sigmaZeroRelaxedNormedAddCommGroupInst K X HX
    letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X HX
    letI := sigmaZeroRelaxedAddCommGroupInst K Y HY
    letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
    letI := sigmaZeroRelaxedNormedAddCommGroupInst K Y HY
    letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 Y HY
    ∀ z w : SigmaRelaxedObject K X HX (0 : K),
      dist (sigmaZeroLiftContinuousLinearMap K 𝕜 X Y HX HY f z)
        (sigmaZeroLiftContinuousLinearMap K 𝕜 X Y HX HY f w) ≤
          q * dist z w := by
  letI := sigmaZeroRelaxedAddCommGroupInst K X HX
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
  letI := sigmaZeroRelaxedNormedAddCommGroupInst K X HX
  letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X HX
  letI := sigmaZeroRelaxedAddCommGroupInst K Y HY
  letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
  letI := sigmaZeroRelaxedNormedAddCommGroupInst K Y HY
  letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 Y HY
  exact (sigmaZeroLiftContinuousLinearMap_dist_contract_iff K 𝕜 X Y HX HY f q).2
    (continuousLinearMap_dist_contract_of_norm_le 𝕜 X Y f q hnorm)

/-- A compact certificate that sigma-zero bounded-operator lifting preserves
metric contraction constants. -/
structure SigmaZeroMetricContractionTransportCertificate
    (K : Type u) [Zero K] (𝕜 : Type*) [NontriviallyNormedField 𝕜] where
  dist_contract_iff :
    ∀ (X : Type v) (Y : Type w) (HX : Type x) (HY : Type y)
      [Inhabited HX] [Inhabited HY]
      [NormedAddCommGroup X] [NormedSpace 𝕜 X]
      [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
      (f : X →L[𝕜] Y) (q : ℝ),
      letI := sigmaZeroRelaxedAddCommGroupInst K X HX
      letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
      letI := sigmaZeroRelaxedNormedAddCommGroupInst K X HX
      letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X HX
      letI := sigmaZeroRelaxedAddCommGroupInst K Y HY
      letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
      letI := sigmaZeroRelaxedNormedAddCommGroupInst K Y HY
      letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 Y HY
      (∀ z w : SigmaRelaxedObject K X HX (0 : K),
          dist (sigmaZeroLiftContinuousLinearMap K 𝕜 X Y HX HY f z)
            (sigmaZeroLiftContinuousLinearMap K 𝕜 X Y HX HY f w) ≤
              q * dist z w) ↔
        ∀ x y : X, dist (f x) (f y) ≤ q * dist x y
  dist_contract_of_norm_le :
    ∀ (X : Type v) (Y : Type w) (HX : Type x) (HY : Type y)
      [Inhabited HX] [Inhabited HY]
      [NormedAddCommGroup X] [NormedSpace 𝕜 X]
      [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
      (f : X →L[𝕜] Y) (q : ℝ),
      ‖f‖ ≤ q →
      letI := sigmaZeroRelaxedAddCommGroupInst K X HX
      letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
      letI := sigmaZeroRelaxedNormedAddCommGroupInst K X HX
      letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X HX
      letI := sigmaZeroRelaxedAddCommGroupInst K Y HY
      letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
      letI := sigmaZeroRelaxedNormedAddCommGroupInst K Y HY
      letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 Y HY
      ∀ z w : SigmaRelaxedObject K X HX (0 : K),
        dist (sigmaZeroLiftContinuousLinearMap K 𝕜 X Y HX HY f z)
          (sigmaZeroLiftContinuousLinearMap K 𝕜 X Y HX HY f w) ≤
            q * dist z w

/-- THEOREM 5: the canonical metric-contraction transport certificate. -/
theorem sigmaZeroMetricContractionTransportCertificate
    (K : Type u) [Zero K] (𝕜 : Type*) [NontriviallyNormedField 𝕜] :
    SigmaZeroMetricContractionTransportCertificate K 𝕜 where
  dist_contract_iff := by
    intro X Y HX HY _ _ _ _ _ _ f q
    exact sigmaZeroLiftContinuousLinearMap_dist_contract_iff K 𝕜 X Y HX HY f q
  dist_contract_of_norm_le := by
    intro X Y HX HY _ _ _ _ _ _ f q hnorm
    exact sigmaZeroLiftContinuousLinearMap_dist_contract_of_norm_le K 𝕜 X Y HX HY f q hnorm


end AffineRelaxation
end SaturationMonoid
