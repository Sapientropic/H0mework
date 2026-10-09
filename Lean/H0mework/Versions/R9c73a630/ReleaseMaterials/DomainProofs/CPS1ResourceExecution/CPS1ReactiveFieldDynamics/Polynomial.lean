import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deformation.Variation

/-!
Finite coefficient algebra for the complete reactive field. The kernels are arbitrary;
the source consumer supplies its actual primitive kernels. Density indices follow
`CPS1Deformation.FiniteVariation`: `density q p = ∑ i, C q i * star (C p i)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 100000

namespace CPS1ReactiveFieldDynamics.Polynomial
noncomputable section
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open CPS1Deformation.FiniteVariation
variable {n m : Type*} [Fintype n] [Fintype m]

def occupiedEnergy (core : Matrix n n ℂ) (tensor : n → n → n → n → ℂ)
    (coefficients : Matrix n m ℂ) : ℝ :=
  (∑ i, ∑ p, ∑ q, star (coefficients p i) * coefficients q i * core p q).re +
    (1 / 2) * (∑ i, ∑ j, ∑ p, ∑ q, ∑ r, ∑ s,
      (star (coefficients p i) * coefficients q i *
        star (coefficients r j) * coefficients s j) *
        (tensor p r q s - tensor p r s q)).re

def occupiedTwoBody (tensor : n → n → n → n → ℂ) (coefficients : Matrix n m ℂ)
    (i j k l : m) : ℂ :=
  ∑ p, ∑ q, ∑ r, ∑ s,
    (star (coefficients p i) * coefficients q k *
      star (coefficients r j) * coefficients s l) * tensor p r q s

omit [Fintype m] in
theorem occupied_exchange (tensor : n → n → n → n → ℂ)
    (coefficients : Matrix n m ℂ) (i j : m) :
    occupiedTwoBody tensor coefficients i j j i =
      ∑ p, ∑ q, ∑ r, ∑ s,
        (star (coefficients p i) * coefficients q i *
          star (coefficients r j) * coefficients s j) * tensor p r s q := by
  rw [occupiedTwoBody]
  apply Finset.sum_congr rfl
  intro p _
  calc
    _ = ∑ r, ∑ q, ∑ s,
        (star (coefficients p i) * coefficients q j *
          star (coefficients r j) * coefficients s i) * tensor p r q s := by
      rw [Finset.sum_comm]
    _ = ∑ r, ∑ s, ∑ q,
        (star (coefficients p i) * coefficients q j *
          star (coefficients r j) * coefficients s i) * tensor p r q s := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_comm]
    _ = ∑ s, ∑ r, ∑ q,
        (star (coefficients p i) * coefficients q j *
          star (coefficients r j) * coefficients s i) * tensor p r q s := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q _
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro s _
      ring

omit [Fintype m] in
theorem occupied_direct_exchange (tensor : n → n → n → n → ℂ)
    (coefficients : Matrix n m ℂ) (i j : m) :
    occupiedTwoBody tensor coefficients i j i j - occupiedTwoBody tensor coefficients i j j i =
      ∑ p, ∑ q, ∑ r, ∑ s,
        (star (coefficients p i) * coefficients q i *
          star (coefficients r j) * coefficients s j) *
          (tensor p r q s - tensor p r s q) := by
  rw [occupied_exchange, occupiedTwoBody]
  simp only [mul_sub, Finset.sum_sub_distrib]

theorem occupied_one_body (core : Matrix n n ℂ) (coefficients : Matrix n m ℂ) :
    (∑ i, ∑ p, ∑ q, star (coefficients p i) * coefficients q i * core p q) =
      Matrix.trace (core * (coefficients * coefficients.conjTranspose)) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem occupied_pair (tensor : n → n → n → n → ℂ)
    (coefficients : Matrix n m ℂ) :
    (∑ i, ∑ j, ∑ p, ∑ q, ∑ r, ∑ s,
      (star (coefficients p i) * coefficients q i *
        star (coefficients r j) * coefficients s j) *
        interaction tensor p r q s) =
      ∑ p, ∑ r, ∑ q, ∑ s,
        (coefficients * coefficients.conjTranspose) q p *
          (coefficients * coefficients.conjTranspose) s r * interaction tensor p r q s := by
  classical
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul, Finset.mul_sum]
  calc
    _ = ∑ i, ∑ p, ∑ j, ∑ q, ∑ r, ∑ s,
        (star (coefficients p i) * coefficients q i *
          star (coefficients r j) * coefficients s j) * interaction tensor p r q s := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ p, ∑ i, ∑ j, ∑ q, ∑ r, ∑ s,
        (star (coefficients p i) * coefficients q i *
          star (coefficients r j) * coefficients s j) * interaction tensor p r q s := by
      rw [Finset.sum_comm]
    _ = ∑ p, ∑ q, ∑ i, ∑ j, ∑ r, ∑ s,
        (star (coefficients p i) * coefficients q i *
          star (coefficients r j) * coefficients s j) * interaction tensor p r q s := by
      apply Finset.sum_congr rfl
      intro p _
      calc
        _ = ∑ i, ∑ q, ∑ j, ∑ r, ∑ s,
            (star (coefficients p i) * coefficients q i *
              star (coefficients r j) * coefficients s j) * interaction tensor p r q s := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_comm]
        _ = _ := by rw [Finset.sum_comm]
    _ = ∑ p, ∑ q, ∑ r, ∑ i, ∑ j, ∑ s,
        (star (coefficients p i) * coefficients q i *
          star (coefficients r j) * coefficients s j) * interaction tensor p r q s := by
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      calc
        _ = ∑ i, ∑ r, ∑ j, ∑ s,
            (star (coefficients p i) * coefficients q i *
              star (coefficients r j) * coefficients s j) * interaction tensor p r q s := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_comm]
        _ = _ := by rw [Finset.sum_comm]
    _ = ∑ p, ∑ r, ∑ q, ∑ s, ∑ i, ∑ j,
        (star (coefficients p i) * coefficients q i *
          star (coefficients r j) * coefficients s j) * interaction tensor p r q s := by
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro q _
      calc
        _ = ∑ i, ∑ s, ∑ j,
            (star (coefficients p i) * coefficients q i *
              star (coefficients r j) * coefficients s j) * interaction tensor p r q s := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_comm]
        _ = _ := by rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro q _
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- The actual occupied contractions equal the density polynomial, with no kernel symmetry. -/
theorem occupied_energy_eq_density_energy (core : Matrix n n ℂ)
    (tensor : n → n → n → n → ℂ) (coefficients : Matrix n m ℂ) :
    occupiedEnergy core tensor coefficients =
      densityEnergy core tensor (coefficients * coefficients.conjTranspose) := by
  rw [occupiedEnergy, densityEnergy, occupied_one_body]
  congr 2
  exact congrArg Complex.re (occupied_pair tensor coefficients)

theorem differentiable_density_energy (core : Matrix n n ℂ)
    (tensor : n → n → n → n → ℂ) :
    Differentiable ℝ (fun coefficients : Matrix n m ℂ =>
      densityEnergy core tensor (coefficients * coefficients.conjTranspose)) := by
  classical
  intro coefficients
  simp only [densityEnergy, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  fun_prop

theorem continuous_density_energy (core : Matrix n n ℂ)
    (tensor : n → n → n → n → ℂ) :
    Continuous (fun coefficients : Matrix n m ℂ =>
      densityEnergy core tensor (coefficients * coefficients.conjTranspose)) :=
  (differentiable_density_energy core tensor).continuous

theorem continuous_occupied_energy (core : Matrix n n ℂ)
    (tensor : n → n → n → n → ℂ) :
    Continuous (occupiedEnergy core tensor : Matrix n m ℂ → ℝ) := by
  change Continuous (fun coefficients : Matrix n m ℂ => occupiedEnergy core tensor coefficients)
  simpa only [occupied_energy_eq_density_energy] using
    (continuous_density_energy (m := m) core tensor)

/-- The coefficient differential is generated by the finite density polynomial. -/
def occupiedDifferential (core : Matrix n n ℂ) (tensor : n → n → n → n → ℂ)
    (coefficients : Matrix n m ℂ) : Matrix n m ℂ →L[ℝ] ℝ :=
  fderiv ℝ (fun next : Matrix n m ℂ =>
    densityEnergy core tensor (next * next.conjTranspose)) coefficients

theorem occupied_hasFDerivAt (core : Matrix n n ℂ)
    (tensor : n → n → n → n → ℂ) (coefficients : Matrix n m ℂ) :
    HasFDerivAt (fun next : Matrix n m ℂ =>
      densityEnergy core tensor (next * next.conjTranspose))
      (occupiedDifferential core tensor coefficients) coefficients :=
  (differentiable_density_energy core tensor coefficients).hasFDerivAt

theorem occupied_differential_apply (core : Matrix n n ℂ)
    (tensor : n → n → n → n → ℂ) (coefficients direction : Matrix n m ℂ) :
    occupiedDifferential core tensor coefficients direction =
      densityEnergyRate core tensor (coefficients * coefficients.conjTranspose)
        (densityRate coefficients direction) := by
  have line : HasDerivAt (fun time : ℝ => coefficients + time • direction) direction 0 := by
    simpa only [one_smul, zero_add] using!
      (hasDerivAt_const (0 : ℝ) coefficients).add
        ((hasDerivAt_id (0 : ℝ)).smul_const direction)
  have atCurve : HasFDerivAt (fun next : Matrix n m ℂ =>
      densityEnergy core tensor (next * next.conjTranspose))
      (occupiedDifferential core tensor coefficients) (coefficients + (0 : ℝ) • direction) := by
    simpa only [zero_smul, add_zero] using occupied_hasFDerivAt core tensor coefficients
  have actual := atCurve.comp_hasDerivAt (0 : ℝ) line
  have derivative : HasDerivAt (fun time : ℝ => densityEnergy core tensor
      ((coefficients + time • direction) * (coefficients + time • direction).conjTranspose))
      (occupiedDifferential core tensor coefficients direction) 0 := by
    simpa only [Function.comp_def] using! actual
  exact derivative.unique (density_energy_line core tensor coefficients direction)

theorem occupied_energy_hasFDerivAt (core : Matrix n n ℂ)
    (tensor : n → n → n → n → ℂ) (coefficients : Matrix n m ℂ) :
    HasFDerivAt (occupiedEnergy core tensor : Matrix n m ℂ → ℝ)
      (occupiedDifferential core tensor coefficients) coefficients := by
  change HasFDerivAt (fun next : Matrix n m ℂ => occupiedEnergy core tensor next)
    (occupiedDifferential core tensor coefficients) coefficients
  simpa only [occupied_energy_eq_density_energy] using
    occupied_hasFDerivAt core tensor coefficients

end
end CPS1ReactiveFieldDynamics.Polynomial
