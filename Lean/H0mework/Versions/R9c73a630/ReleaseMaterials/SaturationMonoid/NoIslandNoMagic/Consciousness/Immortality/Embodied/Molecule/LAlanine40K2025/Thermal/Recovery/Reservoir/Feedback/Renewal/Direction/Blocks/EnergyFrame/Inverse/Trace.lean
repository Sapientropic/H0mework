import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Error
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Formula

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
open Collision
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem complex_trace_norm_mass (O rho : Matrix ι ι ℂ) (positive : rho.PosSemidef) :
    ‖(O*rho).trace‖ ≤ ‖O‖*rho.trace.re := by
  let z := (O*rho).trace
  by_cases zero : z=0
  · change ‖z‖ ≤ _
    rw [zero,norm_zero]
    exact mul_nonneg (norm_nonneg _) (Complex.nonneg_iff.mp positive.trace_nonneg).1
  let phase : ℂ := star z/(‖z‖ : ℝ)
  have normPositive : 0 < ‖z‖ := norm_pos_iff.mpr zero
  have phaseNorm : ‖phase‖ = 1 := by
    dsimp only [phase]
    rw [norm_div,norm_star,Complex.norm_real,Real.norm_eq_abs,abs_of_pos normPositive]
    exact div_self normPositive.ne'
  have product : phase*z = (‖z‖ : ℝ) := by
    dsimp only [phase]
    rw [div_mul_eq_mul_div,Complex.star_def,← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]
    push_cast
    field_simp
  have read : energy (phase • O) rho = ‖z‖ := by
    simp only [energy,Matrix.smul_mul,Matrix.trace_smul,smul_eq_mul]
    change (phase*z).re = _
    rw [product,Complex.ofReal_re]
  have bound := energy_norm_mass (phase • O) rho positive
  rw [read,abs_of_pos normPositive,norm_smul,phaseNorm,one_mul] at bound
  exact bound

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
