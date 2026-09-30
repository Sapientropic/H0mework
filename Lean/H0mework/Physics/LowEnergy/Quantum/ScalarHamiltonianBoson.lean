import H0mework.Physics.LowEnergy.Quantum.ScalarCCR

/-! Finite canonical quadratic Hamiltonians on the polynomial domain.
The symmetric Hessian is an explicit input to this algebraic consumer. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SourceScalarHamiltonian
open SourceScalarCCR
open scoped BigOperators
noncomputable section
variable {σ : Type*}

def read (X : BosonEnd σ) : BosonEnd σ →ₗ[ℂ] BosonEnd σ :=
  Complex.I • (LinearMap.mulRight ℂ X - LinearMap.mulLeft ℂ X)

theorem read_apply (X H : BosonEnd σ) : read X H = Complex.I • (H * X - X * H) := rfl

theorem read_product (X A B : BosonEnd σ) :
    read X (A * B) = A * read X B + read X A * B := by
  simp only [read_apply, mul_smul_comm, smul_mul_assoc, ← smul_add]
  congr 1
  simp only [mul_sub, sub_mul, mul_assoc]
  abel

theorem position_position_read (a b : σ) : read (position a) (position b) = 0 := by
  rw [read_apply, position_position b a, sub_self, smul_zero]

theorem momentum_momentum_read (a b : σ) : read (momentum a) (momentum b) = 0 := by
  rw [read_apply, momentum_momentum b a, sub_self, smul_zero]

theorem position_momentum_read [DecidableEq σ] (a b : σ) :
    read (position a) (momentum b) = (if a = b then 1 else 0 : ℂ) • (1 : BosonEnd σ) := by
  have reversed : momentum b * position a - position a * momentum b =
      -(position a * momentum b - momentum b * position a) := by abel
  rw [read_apply, reversed, position_momentum]
  by_cases same : a = b
  · simp only [if_pos same, smul_neg, smul_smul, Complex.I_mul_I]
    module
  · simp only [if_neg same, zero_smul, neg_zero, smul_zero]

theorem momentum_position_read [DecidableEq σ] (a b : σ) :
    read (momentum a) (position b) = (if b = a then -1 else 0 : ℂ) • (1 : BosonEnd σ) := by
  rw [read_apply, position_momentum]
  by_cases same : b = a
  · simp only [if_pos same, smul_smul, Complex.I_mul_I]
  · simp only [if_neg same, zero_smul, smul_zero]

def phase : σ ⊕ σ → BosonEnd σ := Sum.elim position momentum

def quadratic [Fintype σ] (K : Matrix (σ ⊕ σ) (σ ⊕ σ) ℝ) : BosonEnd σ :=
  (1 / 2 : ℂ) • ∑ i, ∑ j, (K i j : ℂ) • (phase i * phase j)

private theorem half_double (A : BosonEnd σ) : (1 / 2 : ℂ) • (A + A) = A := by module

theorem quadratic_read [Fintype σ] {ι : Type*} [Fintype ι]
    (K : Matrix ι ι ℂ) (symmetric : ∀ i j, K i j = K j i)
    (Z : ι → BosonEnd σ) (X : BosonEnd σ) (d : ι → ℂ)
    (canonical : ∀ i, read X (Z i) = d i • (1 : BosonEnd σ)) :
    read X ((1 / 2 : ℂ) • ∑ i, ∑ j, K i j • (Z i * Z j)) =
      ∑ i, ∑ j, (K i j * d j) • Z i := by
  simp only [map_smul, map_sum, read_product, canonical, mul_smul_comm,
    smul_mul_assoc, mul_one, one_mul, smul_add, smul_smul, Finset.sum_add_distrib]
  have exchanged : (∑ i, ∑ j, (K i j * d i) • Z j) =
      ∑ i, ∑ j, (K i j * d j) • Z i := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [symmetric j i]
  rw [exchanged, ← smul_add]
  exact half_double _

theorem quadratic_position [Fintype σ] [DecidableEq σ]
    (K : Matrix (σ ⊕ σ) (σ ⊕ σ) ℝ) (symmetric : ∀ i j, K i j = K j i) (a : σ) :
    read (position a) (quadratic K) =
      ∑ j : σ ⊕ σ, (K (Sum.inr a) j : ℂ) • phase j := by
  let d : σ ⊕ σ → ℂ := Sum.elim (fun _ => 0) (fun b => if a = b then 1 else 0)
  have canonical (i : σ ⊕ σ) : read (position a) (phase i) = d i • (1 : BosonEnd σ) := by
    cases i with
    | inl b => simpa only [phase, d, Sum.elim_inl, zero_smul] using position_position_read a b
    | inr b => exact position_momentum_read a b
  rw [quadratic, quadratic_read (fun i j => (K i j : ℂ)) (by
    intro i j; exact congrArg Complex.ofReal (symmetric i j)) phase (position a) d canonical]
  have row (i : σ ⊕ σ) :
      (∑ j, ((K i j : ℂ) * d j) • phase i) =
        (K i (Sum.inr a) : ℂ) • phase i := by
    simp [Fintype.sum_sum_type, d]
  simp_rw [row]
  apply Finset.sum_congr rfl
  intro i _
  rw [symmetric i (Sum.inr a)]

theorem quadratic_momentum [Fintype σ] [DecidableEq σ]
    (K : Matrix (σ ⊕ σ) (σ ⊕ σ) ℝ) (symmetric : ∀ i j, K i j = K j i) (a : σ) :
    read (momentum a) (quadratic K) =
      -(∑ j : σ ⊕ σ, (K (Sum.inl a) j : ℂ) • phase j) := by
  let d : σ ⊕ σ → ℂ := Sum.elim (fun b => if b = a then -1 else 0) (fun _ => 0)
  have canonical (i : σ ⊕ σ) : read (momentum a) (phase i) = d i • (1 : BosonEnd σ) := by
    cases i with
    | inl b => exact momentum_position_read a b
    | inr b => simpa only [phase, d, Sum.elim_inr, zero_smul] using momentum_momentum_read a b
  rw [quadratic, quadratic_read (fun i j => (K i j : ℂ)) (by
    intro i j; exact congrArg Complex.ofReal (symmetric i j)) phase (momentum a) d canonical]
  have row (i : σ ⊕ σ) :
      (∑ j, ((K i j : ℂ) * d j) • phase i) =
        -((K i (Sum.inl a) : ℂ) • phase i) := by
    simp [Fintype.sum_sum_type, d]
    exact neg_smul (K i (Sum.inl a) : ℂ) (phase i)
  simp_rw [row]
  rw [Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [symmetric i (Sum.inl a)]

end
end SourceScalarHamiltonian
