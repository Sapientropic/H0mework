import H0mework.Chemistry.LAlanineThermalDynamics.PartialSwapReducedState
import Mathlib.Tactic

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.BodyKernel

open Collision
open scoped Matrix
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem systemNext_trace (rho tau : SystemMatrix ι) (c s : ℝ)
    (circle : c ^ 2 + s ^ 2 = 1) (normalized : tau.trace = 1) :
    (systemNext rho tau c s).trace = rho.trace := by
  rw [systemNext, systemReduce_trace, jointNext_trace rho tau c s circle, normalized, mul_one]

def entryCoefficient (c s a b : ℝ) : ℂ :=
  (c : ℂ) ^ 2 + (Complex.I * (c : ℂ) * (s : ℂ)) * ((b : ℂ) - a)

theorem entryCoefficient_nonzero (c s a b : ℝ) (nonzero : c ≠ 0) :
    entryCoefficient c s a b ≠ 0 := by
  intro zero
  have realPart := congrArg Complex.re zero
  have square : c ^ 2 = 0 := by
    simpa [entryCoefficient, Complex.mul_re, pow_two] using realPart
  exact (pow_ne_zero 2 nonzero) square

theorem systemNext_diagonal_injective (weights : ι → ℝ) (c s : ℝ)
    (normalized : (Matrix.diagonal (fun i => (weights i : ℂ))).trace = 1)
    (circle : c ^ 2 + s ^ 2 = 1) (nonzero : c ≠ 0) :
    Function.Injective (fun rho : SystemMatrix ι => systemNext rho (Matrix.diagonal (fun i => (weights i : ℂ))) c s) := by
  intro left right same
  have traces : left.trace = right.trace := by
    have read := congrArg Matrix.trace same
    simpa only [systemNext_trace _ _ c s circle normalized] using read
  ext i j
  have entry := congrArg (fun M : SystemMatrix ι => M i j) same
  simp only [systemNext_full, normalized, one_smul, traces, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.mul_diagonal, Matrix.diagonal_mul] at entry
  apply mul_left_cancel₀ (entryCoefficient_nonzero c s (weights i) (weights j) nonzero)
  unfold entryCoefficient
  linear_combination entry

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.BodyKernel
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
