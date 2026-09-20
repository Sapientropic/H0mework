/-
  Proposition 128: heterogeneous saturation rates are not a single exponential.

  The empirical "power-law forgetting from many rates" conjecture needs a
  careful mathematical first step.  A finite population with different
  saturation keep-rates is a finite mixture of geometric/exponential decays;
  exact power laws require an additional rate-distribution model.  What *is*
  immediate and important is the anti-single-exponential theorem:

    single fixed keep-rate        -> geometric decay;
    homogeneous population        -> still geometric decay;
    two nonzero different rates   -> not one geometric decay.

  The last statement is proved from the moment identity

    A₀ A₂ - A₁² = a b (k₁ - k₂)²

  for the aggregate `Aₙ = a k₁ⁿ + b k₂ⁿ`.  Thus any nonzero heterogeneous
  two-rate aggregate already violates the first-three-point test for a single
  exponential/geometric curve.
-/

import H0mework.Realization.Observation.Saturation

/-! ## Single-rate and population aggregate decay -/

/-- Residual after `n` steps with fixed keep-rate `keep`. -/
def saturationResidualAfter {α : Type*} [Monoid α]
    (keep initial : α) (n : Nat) : α :=
  keep ^ n * initial

/-- Finite population aggregate with per-agent amplitudes and keep-rates. -/
def populationSaturationAggregate
    {Agent α : Type*} [Fintype Agent] [CommSemiring α]
    (amplitude keep : Agent -> α) (n : Nat) : α :=
  ∑ agent, amplitude agent * keep agent ^ n

/-- THEOREM 1: a homogeneous population is still a single geometric decay. -/
theorem populationSaturationAggregate_homogeneous
    {Agent α : Type*} [Fintype Agent] [CommSemiring α]
    (amplitude : Agent -> α) (keep : α) (n : Nat) :
    populationSaturationAggregate amplitude (fun _ => keep) n =
      (∑ agent, amplitude agent) * keep ^ n := by
  simp [populationSaturationAggregate, Finset.sum_mul]

/-! ## Two-rate aggregate and the moment identity -/

/-- Two-agent aggregate `Aₙ = a k₁ⁿ + b k₂ⁿ`.  The amplitudes `a,b` may
already include initial residuals and population weights. -/
def twoRateAggregate {α : Type*} [CommSemiring α]
    (a b k₁ k₂ : α) (n : Nat) : α :=
  a * k₁ ^ n + b * k₂ ^ n

/-- THEOREM 2: if two keep-rates are equal, the two-agent aggregate collapses
to a single geometric decay. -/
theorem twoRateAggregate_same_rate
    {α : Type*} [CommSemiring α]
    (a b k : α) (n : Nat) :
    twoRateAggregate a b k k n = (a + b) * k ^ n := by
  simp [twoRateAggregate]
  ring

/-- THEOREM 3: the two-rate aggregate has a closed second-moment residual.
This is the algebraic witness that rate heterogeneity cannot be represented by
one geometric curve unless a weight is zero or the rates coincide. -/
theorem twoRateAggregate_moment_identity
    {α : Type*} [CommRing α]
    (a b k₁ k₂ : α) :
    twoRateAggregate a b k₁ k₂ 0 *
        twoRateAggregate a b k₁ k₂ 2 -
      (twoRateAggregate a b k₁ k₂ 1) ^ 2 =
        a * b * (k₁ - k₂) ^ 2 := by
  simp [twoRateAggregate]
  ring

/-- A sequence's first three points fit a single geometric curve when there are
`C,K` such that `A₀=C`, `A₁=C*K`, and `A₂=C*K²`. -/
def FitsSingleGeometricFirstThree
    {α : Type*} [Semiring α] (A : Nat -> α) : Prop :=
  exists C K : α, A 0 = C /\ A 1 = C * K /\ A 2 = C * K ^ 2

/-- THEOREM 4: any first-three-point single-geometric fit has zero moment
residual `A₀ A₂ - A₁²`. -/
theorem moment_zero_of_fitsSingleGeometricFirstThree
    {α : Type*} [CommRing α] {A : Nat -> α}
    (hfit : FitsSingleGeometricFirstThree A) :
    A 0 * A 2 - (A 1) ^ 2 = 0 := by
  rcases hfit with ⟨C, K, h0, h1, h2⟩
  rw [h0, h1, h2]
  ring

/-- THEOREM 5: two nonzero amplitudes with different keep-rates cannot fit any
single geometric curve even at the first three time points. -/
theorem twoRateAggregate_not_single_geometric_first_three
    {α : Type*} [Field α]
    {a b k₁ k₂ : α}
    (ha : a ≠ 0) (hb : b ≠ 0) (hk : k₁ ≠ k₂) :
    Not (FitsSingleGeometricFirstThree
      (fun n => twoRateAggregate a b k₁ k₂ n)) := by
  intro hfit
  have hzero :=
    moment_zero_of_fitsSingleGeometricFirstThree hfit
  rw [twoRateAggregate_moment_identity] at hzero
  have hrate : (k₁ - k₂) ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 (sub_ne_zero.mpr hk)
  have hne : a * b * (k₁ - k₂) ^ 2 ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero ha hb) hrate
  exact hne hzero

/-!
  Summary:
  - Fixed-rate saturation residuals are geometric.
  - Homogeneous populations remain geometric after aggregation.
  - Heterogeneous nonzero two-rate populations already fail the
    first-three-point test for any single geometric/exponential curve.

  Boundary:
  - This does not yet prove an exact power law.  Exact power laws require a
    rate-distribution theorem, such as a continuous or suitably structured
    mixture of exponentials/geometric rates.  P128 proves the algebraic
    anti-single-exponential base that such an empirical test needs.
-/
