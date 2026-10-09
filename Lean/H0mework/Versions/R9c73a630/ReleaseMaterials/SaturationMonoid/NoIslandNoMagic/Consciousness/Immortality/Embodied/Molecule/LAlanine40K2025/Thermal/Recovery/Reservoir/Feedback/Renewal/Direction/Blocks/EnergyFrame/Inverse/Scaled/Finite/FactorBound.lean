import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.RationalResidual
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Bounds

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite
open RationalMatrix
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem norm_from_rational_factors (r i l m u v : Matrix ι ι ℚ) (mu delta : ℚ)
    (hermitian : (cast r i).IsHermitian) (hm : 0 ≤ mu) (hd : 0 ≤ delta)
    (minus : squareSum (residualReal r l m mu delta (-1)) (residualImag i l m (-1)) ≤ delta^2)
    (plus : squareSum (residualReal r u v mu delta 1) (residualImag i u v 1) ≤ delta^2) :
    ‖cast r i‖ ≤ (mu : ℝ) := by
  have scalar : ((mu-delta : ℚ) : ℂ) • (1 : Matrix ι ι ℂ)=((mu : ℝ)-(delta : ℝ)) • (1 : Matrix ι ι ℂ) := by
    ext a b
    simp [Matrix.smul_apply,Complex.real_smul,Rat.cast_sub]
  apply norm_bound_from_gram_factors (cast r i) (cast l m) (cast u v) hermitian (mu : ℝ) (delta : ℝ) (by exact_mod_cast hm)
  · have paid := residual_norm r i l m mu delta (-1) hd minus
    rw [scalar] at paid
    simpa only [Rat.cast_neg,Rat.cast_one,neg_one_smul,sub_eq_add_neg] using paid
  · have paid := residual_norm r i u v mu delta 1 hd plus
    rw [scalar] at paid
    simpa only [Rat.cast_one,one_smul] using paid

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
