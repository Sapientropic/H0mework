import H0mework.Chemistry.LAlanineJointNext.DynamicsRealRestriction
import Mathlib.Analysis.Matrix.Order

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.JointNext.RealRestriction.Counterexample

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section

def amplitude (sign : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; Complex.I * (sign : ℂ), 0]
def state (sign : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℝ) • (amplitude sign * (amplitude sign)ᴴ)

theorem state_positive (sign : ℝ) : (state sign).PosSemidef :=
  (Matrix.posSemidef_self_mul_conjTranspose (amplitude sign)).smul (by norm_num : (0 : ℝ) ≤ 1 / 2)

theorem plus_explicit : state 1 = !![1 / 2, -Complex.I / 2; Complex.I / 2, 1 / 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [state, amplitude, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Matrix.conjTranspose_apply, Fin.sum_univ_two, Complex.real_smul] <;> ring

theorem minus_explicit : state (-1) = !![1 / 2, Complex.I / 2; -Complex.I / 2, 1 / 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [state, amplitude, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Matrix.conjTranspose_apply, Fin.sum_univ_two, Complex.real_smul] <;> ring

theorem plus_normalized : (state 1).trace = 1 := by rw [plus_explicit]; norm_num [Matrix.trace, Fin.sum_univ_two]
theorem minus_normalized : (state (-1)).trace = 1 := by rw [minus_explicit]; norm_num [Matrix.trace, Fin.sum_univ_two]

theorem same_realPart : realPart (state 1) = realPart (state (-1)) := by
  rw [plus_explicit, minus_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [realPart, Complex.div_re]

theorem distinct_full_states : state 1 ≠ state (-1) := by
  intro same
  have entry := congrArg (fun D : Matrix (Fin 2) (Fin 2) ℂ => (D 0 1).im) same
  rw [plus_explicit, minus_explicit] at entry
  norm_num at entry

theorem all_real_operators_agree (A : Matrix (Fin 2) (Fin 2) ℝ) :
    (complexify A * state 1).trace.re = (complexify A * state (-1)).trace.re := by
  rw [scalar_trace_restriction, scalar_trace_restriction, same_realPart]

theorem no_realPart_state_recovery :
    ¬∃ recover : Matrix (Fin 2) (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℂ,
      ∀ D, D.PosSemidef → D.trace = 1 → recover (realPart D) = D := by
  rintro ⟨recover, reads⟩
  apply distinct_full_states
  rw [← reads (state 1) (state_positive 1) plus_normalized,
    ← reads (state (-1)) (state_positive (-1)) minus_normalized, same_realPart]

end
end LAlanine40K2025.JointNext.RealRestriction.Counterexample
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
