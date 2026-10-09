import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Phase.Polynomial
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.PCNorm

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Phase
open Propagation.Interface Propagation.Producer Load.Source Powered.Dynamics
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
theorem clock_positive : (0 : ℝ) < (nativeClockStep : ℝ) := by exact_mod_cast nativeClockStep_positive

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def flowPolynomial (H : Matrix ι ι ℂ) (time : ℝ) : Matrix ι ι ℂ := polynomial (time • (-Complex.I • H)) 14

theorem source_short_flow_error (H : Matrix ι ι ℂ) (time : ℝ)
    (size : ‖H‖ ≤ 100) (clock : |time| ≤ 4*(nativeClockStep : ℝ)) :
    ‖hamiltonianFlow H time-flowPolynomial H time‖ ≤ (1/10^18 : ℝ) := by
  have input : ‖time • (-Complex.I • H)‖ ≤ (1/5 : ℝ) := by
    simp only [norm_smul,Real.norm_eq_abs,norm_neg,Complex.norm_I,one_mul]
    have paid := mul_le_mul clock size (norm_nonneg H) (mul_nonneg (by norm_num) clock_positive.le)
    apply paid.trans
    rw [nativeClockStep_exact]
    norm_num
  have paid := polynomial_error (time • (-Complex.I • H)) (1/5) (by norm_num) (by norm_num) input 14
  apply paid.trans
  norm_num [Nat.factorial]

def pcPolynomial : Matrix PairController PairController ℂ := flowPolynomial (sourcePCH E) (nativeClockStep : ℝ)
def environmentPolynomial : Matrix (Fin 2) (Fin 2) ℂ := flowPolynomial (controllerHamiltonian 2) (nativeClockStep : ℝ)

theorem pc_polynomial_error : ‖(numericPCFree : Matrix PairController PairController ℂ)-pcPolynomial‖ ≤ (1/10^18 : ℝ) := by
  exact source_short_flow_error (sourcePCH E) _ (numeric_PC_norm.trans (by norm_num))
    (by rw [abs_of_pos clock_positive]; linarith [clock_positive])

theorem environment_polynomial_error :
    ‖(Load.Recovery.Control.environmentUnitary (nativeClockStep : ℝ) : Matrix (Fin 2) (Fin 2) ℂ)-environmentPolynomial‖ ≤ (1/10^18 : ℝ) := by
  exact source_short_flow_error (controllerHamiltonian 2) _
    (Load.Producer.StrictThermal.controllerHamiltonian_norm_le.trans (by norm_num))
    (by rw [abs_of_pos clock_positive]; linarith [clock_positive])

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Phase
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
