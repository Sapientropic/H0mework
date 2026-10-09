import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Polynomial

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled
open Collision Load.Source Load.Producer.StrictThermal
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def rationalCore : LoadedJoint := numericLoadHamiltonian-(sineHat : ℂ)^2 •
    Matrix.kronecker (1 : Matrix PairController PairController ℂ) numericEnvironmentRead+
    (-(sineHat : ℂ)^2-Complex.I*cosineHat*sineHat) • (numericProjector*loadInteraction)+
    (-(sineHat : ℂ)^2+Complex.I*cosineHat*sineHat) • (loadInteraction*numericProjector)

def squareError : ℂ := (Real.sin BasisInverse.actualAngle : ℂ)^2-(sineHat : ℂ)^2
def productError : ℂ := Complex.I*(Real.cos BasisInverse.actualAngle*Real.sin BasisInverse.actualAngle-cosineHat*sineHat)

theorem square_error_norm : ‖squareError‖ ≤ (3/10^18 : ℝ) := by
  unfold squareError
  rw [← Complex.ofReal_pow,← Complex.ofReal_pow,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  exact sine_square_error

theorem product_error_norm : ‖productError‖ ≤ (3/10^18 : ℝ) := by
  unfold productError
  rw [norm_mul,Complex.norm_I,one_mul,← Complex.ofReal_mul,← Complex.ofReal_mul,← Complex.ofReal_sub,
    Complex.norm_real,Real.norm_eq_abs]
  exact sine_cosine_error

attribute [local irreducible] numericProjector loadInteraction numericEnvironmentRead numericLoadHamiltonian

theorem rational_core_error : ‖core-rationalCore‖ ≤ (1/10^16 : ℝ) := by
  have delta : core-rationalCore=(-squareError) • Matrix.kronecker (1 : Matrix PairController PairController ℂ) numericEnvironmentRead+
      (-squareError-productError) • (numericProjector*loadInteraction)+
      (-squareError+productError) • (loadInteraction*numericProjector) := by
    ext i j
    simp only [core,rationalCore,squareError,productError,Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
    ring
  have env : ‖Matrix.kronecker (1 : Matrix PairController PairController ℂ) numericEnvironmentRead‖ ≤ 12 :=
    (NonUnitalStarAlgHom.norm_apply_le (tensorRight (ι := PairController) (κ := Fin 2)) _).trans numeric_environment_norm
  have pv : ‖numericProjector*loadInteraction‖ ≤ 1 := (norm_mul_le numericProjector loadInteraction).trans
    (by nlinarith [numeric_projector_norm,actual_load_interaction_norm,norm_nonneg numericProjector,norm_nonneg loadInteraction])
  have vp : ‖loadInteraction*numericProjector‖ ≤ 1 := (norm_mul_le loadInteraction numericProjector).trans
    (by nlinarith [numeric_projector_norm,actual_load_interaction_norm,norm_nonneg numericProjector,norm_nonneg loadInteraction])
  have first : ‖-squareError-productError‖ ≤ (6/10^18 : ℝ) :=
    (norm_sub_le _ _).trans (by rw [norm_neg]; linarith [square_error_norm,product_error_norm])
  have second : ‖-squareError+productError‖ ≤ (6/10^18 : ℝ) :=
    (norm_add_le _ _).trans (by rw [norm_neg]; linarith [square_error_norm,product_error_norm])
  rw [delta]
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_add_le _ _) le_rfl).trans
  simp only [norm_smul,norm_neg]
  have e := mul_le_mul square_error_norm env (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 3/10^18)
  have l := mul_le_mul first pv (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 6/10^18)
  have r := mul_le_mul second vp (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 6/10^18)
  linarith

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
