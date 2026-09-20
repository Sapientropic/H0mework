import H0mework.Physics.Helicity.Source

/-! The actual source is purely in the P286 SU3 color block. Its color
fundamental trace agrees with the full mother fundamental trace. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Helicity

open Matrix ProofFreeRicherAnholonomicSource StageNineHolonomicField
open SU7MotherLieAlgebra Stage9C.Material.SpinPair

noncomputable section

def colorValue (point : BasePoint) : ℂ :=
  ∑ axis : Fin 3,
    (((magnetic point axis).1 : Matrix (Fin 3) (Fin 3) ℂ) *
      ((covariantCurl point axis).1 : Matrix (Fin 3) (Fin 3) ℂ)).trace

theorem colorGenerator_trace_square (axis : Fin 3) :
    (((sourceColorP286Generator axis).1 : Matrix (Fin 3) (Fin 3) ℂ) *
      ((sourceColorP286Generator axis).1 : Matrix (Fin 3) (Fin 3) ℂ)).trace = -1 / 2 := by
  rw [sourceColorP286Generator_color]
  fin_cases axis <;> norm_num [sourceColorRaw, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals ring_nf; simp [Complex.I_sq, div_eq_mul_inv]

theorem colorValue_eq (point : BasePoint) : colorValue point = (3 * gaugeScale ^ 5 : ℝ) := by
  unfold colorValue
  simp_rw [magnetic_eq, covariantCurl_eq]
  simp only [Prod.smul_fst, SetLike.val_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Matrix.trace_smul, colorGenerator_trace_square, Fin.sum_univ_three, Complex.real_smul]
  push_cast
  ring

theorem fullMother_eq_color (point : BasePoint) : value point = colorValue point := by
  rw [value_eq, colorValue_eq]

theorem colorValue_nonzero (point : BasePoint) : colorValue point ≠ 0 := by
  rw [← fullMother_eq_color]
  exact value_nonzero point

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Helicity
