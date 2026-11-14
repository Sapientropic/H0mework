/-
  Proposition 127: finite population single-rate residual.

  P128 proves the two-rate anti-single-exponential theorem.  This file fills
  the finite-population algebraic step just before it.  For any finite mixture
  of fixed-rate geometric/exponential residuals, the first-three-point moment
  residual

      A₀ A₂ - A₁²

  must vanish for a single-rate geometric explanation.  Homogeneous finite
  populations satisfy this identity automatically.  Therefore a nonzero
  residual is already a finite, executable obstruction to a single-rate
  explanation before any stronger power-law or continuous rate-distribution
  claim is made.
-/

import H0mework.Realization.Observation.Saturation

/-! ## Finite population moments -/

/-- Finite population aggregate `Aₙ = Σᵢ aᵢ kᵢⁿ`. -/
def finitePopulationAggregate
    {Agent α : Type*} [Fintype Agent] [CommSemiring α]
    (amplitude keep : Agent -> α) (n : Nat) : α :=
  ∑ agent, amplitude agent * keep agent ^ n

/-- The first-three-point moment residual that vanishes for any single
geometric sequence. -/
def finitePopulationMomentResidual
    {Agent α : Type*} [Fintype Agent] [CommRing α]
    (amplitude keep : Agent -> α) : α :=
  finitePopulationAggregate amplitude keep 0 *
      finitePopulationAggregate amplitude keep 2 -
    (finitePopulationAggregate amplitude keep 1) ^ 2

/-! ## Single-rate boundary -/

/-- THEOREM 1: a finite population whose keep-rates are all equal has zero
moment residual.  Homogeneous populations therefore preserve the single-rate
geometric first-three-point identity. -/
theorem finitePopulationMomentResidual_zero_of_same_keep
    {Agent α : Type*} [Fintype Agent] [CommRing α]
    (amplitude : Agent -> α) (keep : α) :
    finitePopulationMomentResidual amplitude (fun _ => keep) = 0 := by
  classical
  have h1 :
      (∑ agent, amplitude agent * keep) =
        (∑ agent, amplitude agent) * keep := by
    exact (Finset.sum_mul Finset.univ amplitude keep).symm
  have h2 :
      (∑ agent, amplitude agent * (keep ^ 2)) =
        (∑ agent, amplitude agent) * (keep ^ 2) := by
    exact (Finset.sum_mul Finset.univ amplitude (keep ^ 2)).symm
  unfold finitePopulationMomentResidual finitePopulationAggregate
  simp only [pow_zero, pow_one, mul_one, h1, h2]
  ring

/-- THEOREM 2: for any first-three-point single-geometric fit, the finite
population moment residual is zero. -/
theorem finitePopulationMomentResidual_zero_of_single_geometric_fit
    {Agent α : Type*} [Fintype Agent] [CommRing α]
    {amplitude keep : Agent -> α}
    {C K : α}
    (h0 : finitePopulationAggregate amplitude keep 0 = C)
    (h1 : finitePopulationAggregate amplitude keep 1 = C * K)
    (h2 : finitePopulationAggregate amplitude keep 2 = C * K ^ 2) :
    finitePopulationMomentResidual amplitude keep = 0 := by
  simp [finitePopulationMomentResidual, h0, h1, h2]
  ring

/-- THEOREM 3: contrapositive form useful for executable checks: a nonzero
finite-population moment residual rules out every first-three-point
single-geometric fit. -/
theorem finitePopulationMomentResidual_nonzero_refutes_single_geometric_fit
    {Agent α : Type*} [Fintype Agent] [CommRing α]
    {amplitude keep : Agent -> α}
    (hres : finitePopulationMomentResidual amplitude keep ≠ 0) :
    ¬ (exists C K : α,
      finitePopulationAggregate amplitude keep 0 = C /\
      finitePopulationAggregate amplitude keep 1 = C * K /\
      finitePopulationAggregate amplitude keep 2 = C * K ^ 2) := by
  rintro ⟨_C, _K, h0, h1, h2⟩
  exact hres
    (finitePopulationMomentResidual_zero_of_single_geometric_fit
      h0 h1 h2)

/-! ## Non-uniform observation times in log space -/

/-- Cross-multiplied adjacent-slope residual for three log-observations at
possibly non-uniform observation times.  It avoids division, so it can be used
over any commutative ring once the observed values have already been moved into
log space. -/
def nonuniformLogAffineThreePointResidual
    {α : Type*} [CommRing α]
    (t0 t1 t2 y0 y1 y2 : α) : α :=
  (y1 - y0) * (t2 - t1) - (y2 - y1) * (t1 - t0)

/-- A first-three-point log-linear fit at arbitrary observation times.  This is
the log-space form of a single exponential model; the logarithm itself is not
formalized here, only the affine geometry of the transformed observations. -/
def FitsNonuniformLogAffineFirstThree
    {α : Type*} [CommRing α]
    (t0 t1 t2 y0 y1 y2 : α) : Prop :=
  exists base slope : α,
    y0 = base + slope * t0 /\
    y1 = base + slope * t1 /\
    y2 = base + slope * t2

/-- THEOREM 4: any affine/log-linear three-point fit has zero cross-multiplied
adjacent-slope residual, even when the observation times are not equally
spaced. -/
theorem nonuniformLogAffineThreePointResidual_zero_of_fit
    {α : Type*} [CommRing α]
    {t0 t1 t2 y0 y1 y2 : α}
    (hfit : FitsNonuniformLogAffineFirstThree t0 t1 t2 y0 y1 y2) :
    nonuniformLogAffineThreePointResidual t0 t1 t2 y0 y1 y2 = 0 := by
  rcases hfit with ⟨base, slope, h0, h1, h2⟩
  rw [h0, h1, h2]
  simp [nonuniformLogAffineThreePointResidual]
  ring

/-- THEOREM 5: executable contrapositive for non-uniform time samples.  A
nonzero cross-multiplied log-slope residual rules out every three-point
log-linear / single-exponential fit at those observation times. -/
theorem nonuniformLogAffineThreePointResidual_nonzero_refutes_fit
    {α : Type*} [CommRing α]
    {t0 t1 t2 y0 y1 y2 : α}
    (hres :
      nonuniformLogAffineThreePointResidual t0 t1 t2 y0 y1 y2 ≠ 0) :
    Not (FitsNonuniformLogAffineFirstThree t0 t1 t2 y0 y1 y2) := by
  intro hfit
  exact hres (nonuniformLogAffineThreePointResidual_zero_of_fit hfit)

/-!
  Summary:
  - Finite population residuals give a first-three-point obstruction to a
    single-rate geometric/exponential explanation.
  - Homogeneous populations have zero residual.
  - A nonzero residual refutes every single-rate fit before making any stronger
    power-law or gamma-mixture claim.
  - For non-uniform observation times, the executable obstruction moves to
    log space: nonzero cross-multiplied adjacent-slope residual refutes every
    first-three-point log-linear / single-exponential fit.

  Boundary:
  - This is finite-population algebra.  Exact Murre-Chessa gamma-mixture
    power laws require the continuous rate-distribution / Laplace-transform
    theorem; that is not proved here.
  - The non-uniform theorem assumes observed values have already been
    transformed into a log-like affine coordinate.  It does not formalize
    analytic logarithms or positivity.
-/
