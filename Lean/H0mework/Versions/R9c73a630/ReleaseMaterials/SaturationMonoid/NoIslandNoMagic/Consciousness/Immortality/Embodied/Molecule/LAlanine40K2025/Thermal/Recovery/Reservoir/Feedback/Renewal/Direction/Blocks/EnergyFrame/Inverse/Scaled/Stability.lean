import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Effect

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem scaled_effect_stability (tau sigma : ℝ) (positiveTau : 0 < tau) (positiveSigma : 0 < sigma)
    (A B : Matrix ι ι ℂ) :
    ‖scaledEffect tau A-scaledEffect sigma B‖ ≤
      (2*‖A-B‖+|tau-sigma|)/(2*(tau+‖A‖)) := by
  let a := tau+‖A‖
  let b := sigma+‖B‖
  have ap : 0 < a := by dsimp only [a]; positivity
  have bp : 0 < b := by dsimp only [b]; positivity
  have diff : |b-a| ≤ |tau-sigma|+‖A-B‖ := by
    have split : b-a=(sigma-tau)+(‖B‖-‖A‖) := by dsimp only [a,b]; ring
    rw [split]
    exact (abs_add_le _ _).trans (add_le_add (by rw [abs_sub_comm]) (by
      simpa only [norm_sub_rev] using abs_norm_sub_norm_le B A))
  have inverse : |1/(2*a)-1/(2*b)|=|b-a|/(2*a*b) := by
    have same : 1/(2*a)-1/(2*b)=(b-a)/(2*a*b) := by field_simp
    rw [same,abs_div,abs_of_pos (by positivity : (0 : ℝ) < 2*a*b)]
  have second : |1/(2*a)-1/(2*b)| * ‖B‖ ≤ (|tau-sigma|+‖A-B‖)/(2*a) := by
    rw [inverse,div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2*a*b)).mpr
    have size : ‖B‖ ≤ b := by dsimp only [b]; linarith
    have bound := mul_le_mul diff size (norm_nonneg B) (by positivity : 0 ≤ |tau-sigma|+‖A-B‖)
    calc
      _ ≤ (|tau-sigma|+‖A-B‖)*b := bound
      _ = _ := by field_simp
  have split : scaledEffect tau A-scaledEffect sigma B=
      ((1/(2*a) : ℝ) : ℂ) • (A-B)+((1/(2*a)-1/(2*b) : ℝ) : ℂ) • B := by
    simp only [scaledEffect,a,b,Complex.ofReal_sub,smul_sub,sub_smul]
    abel
  rw [split]
  apply (norm_add_le _ _).trans
  simp only [norm_smul,Complex.norm_real,Real.norm_eq_abs]
  rw [abs_of_pos (by positivity : (0 : ℝ) < 1/(2*a))]
  calc
    _ ≤ (1/(2*a))*‖A-B‖+(|tau-sigma|+‖A-B‖)/(2*a) := add_le_add le_rfl second
    _ = _ := by dsimp only [a]; field_simp; ring

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
