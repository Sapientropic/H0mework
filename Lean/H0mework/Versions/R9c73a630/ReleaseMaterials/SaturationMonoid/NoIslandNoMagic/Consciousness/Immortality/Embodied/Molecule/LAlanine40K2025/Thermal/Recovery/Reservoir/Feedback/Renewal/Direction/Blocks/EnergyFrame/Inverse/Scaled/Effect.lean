import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.FiniteGain

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled
open Collision Measurement
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Scaling transports the original regularizing constant along with its source observable. -/
def scaledEffect (tau : ℝ) (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  ((1/2 : ℝ) : ℂ) • 1+((1/(2*(tau+‖A‖)) : ℝ) : ℂ) • A

theorem original_scaled_effect (tau : ℝ) (positive : 0 < tau) (A : Matrix ι ι ℂ) :
    boundedEffect A=scaledEffect tau ((tau : ℂ) • A) := by
  have magnitude : ‖(tau : ℂ) • A‖=tau*‖A‖ := by
    rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos positive]
  have scalar : (1/(2*(tau+tau*‖A‖)) : ℝ)*tau=1/(2*measurementScale A) := by
    have nonzero := (measurementScale_pos A).ne'
    unfold measurementScale at nonzero ⊢
    field_simp
  unfold scaledEffect boundedEffect
  rw [magnitude,smul_smul]
  congr 1
  simpa only [Complex.ofReal_mul] using congrArg (fun r : ℝ => (r : ℂ) • A) scalar.symm

theorem scaled_effect_conjugation (tau : ℝ) (U : Matrix.unitaryGroup ι ℂ) (A : Matrix ι ι ℂ) :
    Quantum.conjugation U (scaledEffect tau A)=scaledEffect tau (Quantum.conjugation U A) := by
  have one : Quantum.conjugation U (1 : Matrix ι ι ℂ)=1 := map_one (Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U)
  have same : ‖Quantum.conjugation U A‖=‖A‖ := StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U) _
  simp only [scaledEffect,map_add,map_smul,one,same]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
