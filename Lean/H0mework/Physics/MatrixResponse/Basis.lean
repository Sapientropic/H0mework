import H0mework.Physics.Helicity.Transform
import Mathlib.LinearAlgebra.CrossProduct

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.MatrixResponse

open Matrix Stage9C.Material.SpinPair SU7MotherLieAlgebra SU7MotherGaugeTheory
open StageNineP286GaugeAuxiliaryVariation StageNineP286GaugeConnectionVariation Helicity
open scoped Matrix

noncomputable section

abbrev Coefficients := Matrix (Fin 3) (Fin 3) ℝ

def color (v : Fin 3 → ℝ) : P286LieBlockData :=
  v 0 • sourceColorP286Generator 0 + v 1 • sourceColorP286Generator 1 +
    v 2 • sourceColorP286Generator 2

theorem color_bracket (u v : Fin 3 → ℝ) :
    p286LieBracket (color u) (color v) = color (-(u ⨯₃ v)) := by
  simp [color, p286LieBracket_add_left, p286LieBracket_add_right,
    p286LieBracket_smul_left, p286LieBracket_smul_right,
    sourceColorP286Generator_bracket, cross_apply]
  module

theorem color_neg (v : Fin 3 → ℝ) : color (-v) = -color v := by
  simp [color]
  module

theorem color_sub (u v : Fin 3 → ℝ) : color (u-v) = color u - color v := by
  simp [color]
  module

def mother (v : Fin 3 → ℝ) : MotherMatrix := p286LieBlockEmbed (color v)

theorem mother_sub (u v : Fin 3 → ℝ) : mother (u-v) = mother u - mother v := by
  simp [mother, color_sub, p286LieBlockEmbed_sub]

theorem mother_bracket (u v : Fin 3 → ℝ) :
    bracket (mother u) (mother v) = mother (-(u ⨯₃ v)) := by
  change (suLieBracket (p286LieBlockEmbed (color u)) (p286LieBlockEmbed (color v)) :
    MotherMatrix) = mother (-(u ⨯₃ v))
  rw [← p286LieBlockEmbed_bracket, color_bracket]
  rfl

theorem generator_trace_pair (i j : Fin 3) :
    ((p286LieBlockEmbed (sourceColorP286Generator i) : MotherMatrix) *
      (p286LieBlockEmbed (sourceColorP286Generator j) : MotherMatrix)).trace =
      if i=j then -1/2 else 0 := by
  change (rawP286LieBlock (sourceColorP286Generator i) *
    rawP286LieBlock (sourceColorP286Generator j)).trace = _
  fin_cases i <;> fin_cases j <;>
    norm_num [rawP286LieBlock, weakHyperchargeLieBlock, hyperchargeLieBlock, scalarLieBlock,
      sourceColorP286Generator_color, sourceColorP286Generator_weak_zero,
      sourceColorP286Generator_hypercharge_zero, Matrix.fromBlocks_multiply,
      Matrix.trace, Matrix.mul_apply, sourceColorRaw, Fin.sum_univ_three]
  all_goals ring_nf; simp [Complex.I_sq, div_eq_mul_inv]

theorem mother_trace_pair (u v : Fin 3 → ℝ) :
    (mother u * mother v).trace = (-(u ⬝ᵥ v)/2 : ℝ) := by
  simp only [mother, color, p286LieBlockEmbed_add, p286LieBlockEmbed_real_smul,
    Submodule.coe_add, Submodule.coe_smul, Matrix.add_mul, Matrix.mul_add,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul,
    generator_trace_pair, Complex.real_smul]
  norm_num [dotProduct, Fin.sum_univ_three]
  push_cast
  ring


end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.MatrixResponse
