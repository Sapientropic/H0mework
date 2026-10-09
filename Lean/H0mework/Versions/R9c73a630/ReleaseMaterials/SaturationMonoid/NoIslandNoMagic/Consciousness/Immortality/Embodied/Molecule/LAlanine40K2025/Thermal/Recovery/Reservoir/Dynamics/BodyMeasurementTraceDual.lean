import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Tactic
import H0mework.Chemistry.LAlanineThermalDynamics.PartialSwapEnergyPopulation

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Measurement

open scoped Matrix
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def traceDual (read : Matrix ι ι ℂ →ₗ[ℂ] ℂ) : Matrix ι ι ℂ :=
  fun i j => read (Matrix.single j i 1)

theorem traceDual_read (read : Matrix ι ι ℂ →ₗ[ℂ] ℂ) (rho : Matrix ι ι ℂ) :
    (traceDual read * rho).trace = read rho := by
  conv_rhs => rw [Matrix.matrix_eq_sum_single rho]
  simp only [map_sum]
  change (∑ i, ∑ j, traceDual read i j * rho j i) = _
  simp only [traceDual]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have single : Matrix.single i j (rho i j) = (rho i j) • Matrix.single i j (1 : ℂ) := by
    ext a b
    simp [Matrix.single, Matrix.smul_apply, smul_eq_mul]
  rw [single, map_smul]
  simp [mul_comm]

omit [Fintype ι] in
theorem traceDual_hermitian (read : Matrix ι ι ℂ →ₗ[ℂ] ℂ)
    (faithful : ∀ rho, read (star rho) = star (read rho)) :
    (traceDual read).IsHermitian := by
  ext i j
  change star (read (Matrix.single i j 1)) = read (Matrix.single j i 1)
  rw [← faithful]
  congr 1
  simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_single]

def traceFunctional (O : Matrix ι ι ℂ) : Matrix ι ι ℂ →ₗ[ℂ] ℂ where
  toFun rho := (O * rho).trace
  map_add' left right := by simp [Matrix.mul_add, Matrix.trace_add]
  map_smul' c rho := by simp [Matrix.trace_smul]

theorem traceFunctional_star (O : Matrix ι ι ℂ) (hermitian : O.IsHermitian)
    (rho : Matrix ι ι ℂ) :
    traceFunctional O (star rho) = star (traceFunctional O rho) := by
  change (O * star rho).trace = star ((O * rho).trace)
  rw [← Matrix.trace_conjTranspose]
  rw [Matrix.conjTranspose_mul, hermitian.eq]
  exact Matrix.trace_mul_comm _ _

def inverseTraceObservable (L : Matrix ι ι ℂ ≃ₗ[ℂ] Matrix ι ι ℂ) (O : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  traceDual ((traceFunctional O).comp L.symm.toLinearMap)

theorem inverseTraceObservable_hermitian (L : Matrix ι ι ℂ ≃ₗ[ℂ] Matrix ι ι ℂ)
    (starTransport : ∀ rho, L.symm (star rho) = star (L.symm rho))
    (O : Matrix ι ι ℂ) (hermitian : O.IsHermitian) :
    (inverseTraceObservable L O).IsHermitian := by
  apply traceDual_hermitian
  intro rho
  change traceFunctional O (L.symm (star rho)) = star (traceFunctional O (L.symm rho))
  rw [starTransport, traceFunctional_star O hermitian]

theorem inverseTraceObservable_read (L : Matrix ι ι ℂ ≃ₗ[ℂ] Matrix ι ι ℂ) (O rho : Matrix ι ι ℂ) :
    (inverseTraceObservable L O * L rho).trace = (O * rho).trace := by
  rw [inverseTraceObservable, traceDual_read]
  change traceFunctional O (L.symm (L rho)) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

theorem inverseTraceObservable_energy (L : Matrix ι ι ℂ ≃ₗ[ℂ] Matrix ι ι ℂ) (O rho : Matrix ι ι ℂ) :
    Collision.energy (inverseTraceObservable L O) (L rho) = Collision.energy O rho :=
  congrArg Complex.re (inverseTraceObservable_read L O rho)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Measurement
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
