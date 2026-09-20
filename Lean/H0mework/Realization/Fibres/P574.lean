import H0mework.Realization.Fibres.P573

/-!
# Proposition 574: sigma-zero bounded lifts preserve contraction certificates

P573 proved that sigma-zero bounded-operator lifts preserve the operator norm.
This file packages that equality in the exact forms used by dynamics:

* an operator-norm upper bound is transported iff it held before lifting;
* a strict contraction bound is transported iff it held before lifting;
* the corresponding pointwise Lipschitz-style inequality is transported iff it
  held before lifting.

Thus a Jacobian, Lyapunov, Hamiltonian, or reducer certificate proved on the
standard carrier can be moved through the sigma-zero carrier without weakening
or adding a hidden scale factor.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

universe u v w x y

/-! ## Operator-norm bound transport -/

/-- THEOREM 1: a non-strict operator-norm bound is preserved and reflected by
sigma-zero bounded-operator lifting. -/
@[simp] theorem sigmaZeroLiftContinuousLinearMap_norm_le_iff
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
    ‖sigmaZeroLiftContinuousLinearMap K 𝕜 X Y HX HY f‖ ≤ q ↔ ‖f‖ ≤ q := by
  letI := sigmaZeroRelaxedAddCommGroupInst K X HX
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
  letI := sigmaZeroRelaxedNormedAddCommGroupInst K X HX
  letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X HX
  letI := sigmaZeroRelaxedAddCommGroupInst K Y HY
  letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
  letI := sigmaZeroRelaxedNormedAddCommGroupInst K Y HY
  letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 Y HY
  rw [sigmaZeroLiftContinuousLinearMap_norm]

/-- THEOREM 2: a strict operator-norm bound is preserved and reflected by
sigma-zero bounded-operator lifting. -/
@[simp] theorem sigmaZeroLiftContinuousLinearMap_norm_lt_iff
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
    ‖sigmaZeroLiftContinuousLinearMap K 𝕜 X Y HX HY f‖ < q ↔ ‖f‖ < q := by
  letI := sigmaZeroRelaxedAddCommGroupInst K X HX
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
  letI := sigmaZeroRelaxedNormedAddCommGroupInst K X HX
  letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X HX
  letI := sigmaZeroRelaxedAddCommGroupInst K Y HY
  letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
  letI := sigmaZeroRelaxedNormedAddCommGroupInst K Y HY
  letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 Y HY
  rw [sigmaZeroLiftContinuousLinearMap_norm]

/-- THEOREM 3: strict contraction (`‖f‖ < 1`) is preserved and reflected by
sigma-zero bounded-operator lifting. -/
@[simp] theorem sigmaZeroLiftContinuousLinearMap_strictContraction_iff
    (K : Type u) [Zero K] (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (X : Type v) (Y : Type w) (HX : Type x) (HY : Type y)
    [Inhabited HX] [Inhabited HY]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (f : X →L[𝕜] Y) :
    letI := sigmaZeroRelaxedAddCommGroupInst K X HX
    letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
    letI := sigmaZeroRelaxedNormedAddCommGroupInst K X HX
    letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X HX
    letI := sigmaZeroRelaxedAddCommGroupInst K Y HY
    letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
    letI := sigmaZeroRelaxedNormedAddCommGroupInst K Y HY
    letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 Y HY
    ‖sigmaZeroLiftContinuousLinearMap K 𝕜 X Y HX HY f‖ < 1 ↔ ‖f‖ < 1 := by
  letI := sigmaZeroRelaxedAddCommGroupInst K X HX
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
  letI := sigmaZeroRelaxedNormedAddCommGroupInst K X HX
  letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X HX
  letI := sigmaZeroRelaxedAddCommGroupInst K Y HY
  letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
  letI := sigmaZeroRelaxedNormedAddCommGroupInst K Y HY
  letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 Y HY
  exact sigmaZeroLiftContinuousLinearMap_norm_lt_iff K 𝕜 X Y HX HY f 1

/-! ## Pointwise contraction-bound transport -/

/-- THEOREM 4: the pointwise Lipschitz-style bound
`‖f x‖ ≤ q * ‖x‖` is preserved and reflected by sigma-zero
bounded-operator lifting. -/
@[simp] theorem sigmaZeroLiftContinuousLinearMap_pointwise_bound_iff
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
    (∀ z : SigmaRelaxedObject K X HX (0 : K),
        ‖sigmaZeroLiftContinuousLinearMap K 𝕜 X Y HX HY f z‖ ≤ q * ‖z‖) ↔
      ∀ x : X, ‖f x‖ ≤ q * ‖x‖ := by
  letI := sigmaZeroRelaxedAddCommGroupInst K X HX
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
  letI := sigmaZeroRelaxedNormedAddCommGroupInst K X HX
  letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X HX
  letI := sigmaZeroRelaxedAddCommGroupInst K Y HY
  letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
  letI := sigmaZeroRelaxedNormedAddCommGroupInst K Y HY
  letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 Y HY
  constructor
  · intro h x
    have hx := h (sigmaZeroEmbed (K := K) (X := X) (H := HX) x)
    simpa [sigmaZeroLiftContinuousLinearMap_norm_apply,
      sigmaZeroRelaxed_norm_eq] using hx
  · intro h z
    calc
      ‖sigmaZeroLiftContinuousLinearMap K 𝕜 X Y HX HY f z‖ =
          ‖f (sigmaZeroForget (K := K) (X := X) (H := HX) z)‖ := by
            rw [sigmaZeroLiftContinuousLinearMap_norm_apply]
      _ ≤ q * ‖sigmaZeroForget (K := K) (X := X) (H := HX) z‖ := by
            exact h _
      _ = q * ‖z‖ := by
            rw [sigmaZeroRelaxed_norm_eq]

/-- A compact certificate that sigma-zero lifting preserves the quantitative
operator bounds used by contraction arguments. -/
structure SigmaZeroContractionTransportCertificate
    (K : Type u) [Zero K] (𝕜 : Type*) [NontriviallyNormedField 𝕜] where
  norm_le_iff :
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
      ‖sigmaZeroLiftContinuousLinearMap K 𝕜 X Y HX HY f‖ ≤ q ↔ ‖f‖ ≤ q
  norm_lt_iff :
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
      ‖sigmaZeroLiftContinuousLinearMap K 𝕜 X Y HX HY f‖ < q ↔ ‖f‖ < q
  pointwise_bound_iff :
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
      (∀ z : SigmaRelaxedObject K X HX (0 : K),
          ‖sigmaZeroLiftContinuousLinearMap K 𝕜 X Y HX HY f z‖ ≤ q * ‖z‖) ↔
        ∀ x : X, ‖f x‖ ≤ q * ‖x‖

/-- THEOREM 5: the canonical contraction-transport certificate. -/
theorem sigmaZeroContractionTransportCertificate
    (K : Type u) [Zero K] (𝕜 : Type*) [NontriviallyNormedField 𝕜] :
    SigmaZeroContractionTransportCertificate K 𝕜 where
  norm_le_iff := by
    intro X Y HX HY _ _ _ _ _ _ f q
    exact sigmaZeroLiftContinuousLinearMap_norm_le_iff K 𝕜 X Y HX HY f q
  norm_lt_iff := by
    intro X Y HX HY _ _ _ _ _ _ f q
    exact sigmaZeroLiftContinuousLinearMap_norm_lt_iff K 𝕜 X Y HX HY f q
  pointwise_bound_iff := by
    intro X Y HX HY _ _ _ _ _ _ f q
    exact sigmaZeroLiftContinuousLinearMap_pointwise_bound_iff K 𝕜 X Y HX HY f q


end AffineRelaxation
end SaturationMonoid
