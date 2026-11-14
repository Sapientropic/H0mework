/-
  Proposition 141: finite multichannel residual decomposes into pairwise
  heterogeneity.

  P128 proved the two-rate identity

      A₀ A₂ - A₁² = a b (k₁ - k₂)².

  The forgetting-track correction needs the finite multichannel version: an
  individual system may already contain many internal channels / traces / rates,
  so "individual vs group" is not the mathematical boundary.  The boundary is
  homogeneous single-rate vs heterogeneous multi-rate aggregation.

  This file proves the finite ordered-double-sum identity

      2 * (A₀ A₂ - A₁²)
        = Σᵢ Σⱼ aᵢ aⱼ (kᵢ - kⱼ)².

  Boundary: this is still finite algebra.  It does not prove the continuous
  Murre-Chessa gamma-mixture / Laplace-transform theorem.  It supplies the
  finite multichannel obstruction that such a theorem should refine.
-/

import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.Proposition127

open Finset

/-! ## Pairwise residual decomposition -/

/-- THEOREM 1: a finite multichannel geometric aggregate has a pairwise
heterogeneity decomposition.  The ordered double sum counts each unordered
pair twice and has zero diagonal terms, hence the factor `2` on the moment
residual. -/
theorem finitePopulationMomentResidual_pairwise_double_sum
    {Agent α : Type*} [Fintype Agent] [CommRing α]
    (amplitude keep : Agent -> α) :
    (2 : α) * finitePopulationMomentResidual amplitude keep =
      ∑ i : Agent, ∑ j : Agent,
        amplitude i * amplitude j * (keep i - keep j) ^ 2 := by
  classical
  have hA0A2 :
      (∑ x : Agent, amplitude x) *
          (∑ y : Agent, amplitude y * keep y ^ 2) =
        ∑ x : Agent, ∑ y : Agent,
          amplitude x * amplitude y * keep y ^ 2 := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _hx
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _hy
    ring
  have hA1sq :
      (∑ x : Agent, amplitude x * keep x) ^ 2 =
        ∑ x : Agent, ∑ y : Agent,
          amplitude x * amplitude y * keep x * keep y := by
    rw [sq]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _hx
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _hy
    ring
  have hswap :
      (∑ i : Agent, ∑ j : Agent,
          amplitude i * amplitude j * keep i ^ 2) =
        ∑ i : Agent, ∑ j : Agent,
          amplitude i * amplitude j * keep j ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _hi
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  have hRhsExpanded :
      (∑ i : Agent, ∑ j : Agent,
          amplitude i * amplitude j * (keep i - keep j) ^ 2) =
        (∑ i : Agent, ∑ j : Agent,
          amplitude i * amplitude j * keep i ^ 2) +
        (∑ i : Agent, ∑ j : Agent,
          amplitude i * amplitude j * keep j ^ 2) -
        (2 : α) * (∑ i : Agent, ∑ j : Agent,
          amplitude i * amplitude j * keep i * keep j) := by
    have hterm :
        (∑ i : Agent, ∑ j : Agent,
            amplitude i * amplitude j * (keep i - keep j) ^ 2) =
          ∑ i : Agent, ∑ j : Agent,
            (amplitude i * amplitude j * keep i ^ 2 +
              amplitude i * amplitude j * keep j ^ 2 -
              2 * (amplitude i * amplitude j * keep i * keep j)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    have hScalar :
        (∑ i : Agent, ∑ j : Agent,
            (2 : α) * (amplitude i * amplitude j * keep i * keep j)) =
          (2 : α) * (∑ i : Agent, ∑ j : Agent,
            amplitude i * amplitude j * keep i * keep j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.mul_sum]
    rw [hterm]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [hScalar]
  unfold finitePopulationMomentResidual finitePopulationAggregate
  simp only [pow_zero, pow_one, mul_one]
  rw [hA0A2, hA1sq]
  rw [hRhsExpanded]
  rw [← hswap]
  ring_nf

/-! ## Executable obstruction form -/

/-- THEOREM 2: any first-three-point single-geometric fit forces the pairwise
heterogeneity double-sum to vanish. -/
theorem finitePopulationPairwiseResidual_zero_of_single_geometric_fit
    {Agent α : Type*} [Fintype Agent] [CommRing α]
    {amplitude keep : Agent -> α}
    {C K : α}
    (h0 : finitePopulationAggregate amplitude keep 0 = C)
    (h1 : finitePopulationAggregate amplitude keep 1 = C * K)
    (h2 : finitePopulationAggregate amplitude keep 2 = C * K ^ 2) :
    (∑ i : Agent, ∑ j : Agent,
        amplitude i * amplitude j * (keep i - keep j) ^ 2) = 0 := by
  rw [← finitePopulationMomentResidual_pairwise_double_sum]
  rw [finitePopulationMomentResidual_zero_of_single_geometric_fit h0 h1 h2]
  ring

/-- THEOREM 3: a nonzero pairwise heterogeneity residual rules out every
first-three-point single-geometric fit. -/
theorem finitePopulationPairwiseResidual_nonzero_refutes_single_geometric_fit
    {Agent α : Type*} [Fintype Agent] [CommRing α]
    {amplitude keep : Agent -> α}
    (hpair :
      (∑ i : Agent, ∑ j : Agent,
        amplitude i * amplitude j * (keep i - keep j) ^ 2) ≠ 0) :
    ¬ (exists C K : α,
      finitePopulationAggregate amplitude keep 0 = C /\
      finitePopulationAggregate amplitude keep 1 = C * K /\
      finitePopulationAggregate amplitude keep 2 = C * K ^ 2) := by
  rintro ⟨_C, _K, h0, h1, h2⟩
  exact hpair
    (finitePopulationPairwiseResidual_zero_of_single_geometric_fit h0 h1 h2)

/-- THEOREM 4: homogeneous finite populations have zero pairwise residual.
This is the finite-channel version of "no rate heterogeneity, no pairwise
obstruction." -/
theorem finitePopulationPairwiseResidual_zero_of_same_keep
    {Agent α : Type*} [Fintype Agent] [CommRing α]
    (amplitude : Agent -> α) (keep : α) :
    (∑ i : Agent, ∑ j : Agent,
        amplitude i * amplitude j * (keep - keep) ^ 2) = 0 := by
  rw [← finitePopulationMomentResidual_pairwise_double_sum
    (amplitude := amplitude) (keep := fun _ : Agent => keep)]
  rw [finitePopulationMomentResidual_zero_of_same_keep]
  ring

/-!
  Summary:
  - The finite-population first-three residual is not a black-box statistic.
    It is exactly half of the ordered pairwise heterogeneity sum.
  - A single-geometric fit forces this pairwise residual to vanish.
  - Therefore a nonzero pairwise residual is an executable obstruction to a
    single-rate explanation.

  Boundary:
  - This is finite multichannel algebra.  Exact power-law tails still require
    a continuous or otherwise structured rate-distribution theorem.
  - Positivity statements over ordered fields can turn "some positive
    heterogeneous pair" into "nonzero pairwise residual", but the algebraic
    obstruction itself is the double-sum identity above.
-/
