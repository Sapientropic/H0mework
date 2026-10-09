import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Dense.Matrices

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Dense
open Spectral Propagation.Interface Propagation.Source
open scoped Matrix BigOperators
noncomputable section

def computedField : Matrix Basis Basis ℂ := (1/10^42 : ℂ) • Cast.complexMatrix fieldInt

def computedBase : Matrix Basis Basis ℂ :=
  (1/((densitySquaredMass : ℂ)*10^30)) • Cast.complexMatrix densityGramInt

theorem original_field_exact : Input.rawFieldHamiltonian=computedField := by
  have product := Cast.complexMatrix_gram h0Int frame fieldAppliedInt fieldInt
    original_field_times_frame original_field_full_product
  rw [Input.rawFieldHamiltonian,original_field_off_matrix,Q]
  simp only [star_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul,Matrix.star_eq_conjTranspose]
  rw [product]
  norm_num [computedField]

theorem original_amplitude_exact : initialDensityMatrix electronicSource*Q=
    (1/10^27 : ℂ) • Cast.complexMatrix densityAppliedInt := by
  rw [original_density_matrix,Q,Matrix.smul_mul,Matrix.mul_smul,smul_smul,
    ← Cast.complexMatrix_mul,original_density_times_frame]
  norm_num

theorem original_mass_exact : Preparation.gramMass (initialDensityMatrix electronicSource)=
    (densitySquaredMass : ℝ)/10^24 := by
  rw [original_density_matrix]
  have cast : (1/10^12 : ℂ)=((1/10^12 : ℝ) : ℂ) := by norm_num
  rw [cast,gram_mass_real_smul,gram_mass_real_int d0Int densitySquaredMass density_mass_is_trace]
  ring

theorem original_base_exact : Input.rawBaseSystem=computedBase := by
  rw [Input.rawBaseSystem,Input.baseSystem,normalized_gram_factor]
  have densityStar : star (initialDensityMatrix electronicSource)=initialDensityMatrix electronicSource :=
    Propagation.Dynamics.initialDensityMatrix_hermitian electronicSource
  rw [densityStar,original_amplitude_exact,original_mass_exact,star_smul,
    Matrix.smul_mul,Matrix.mul_smul,smul_smul,Matrix.star_eq_conjTranspose,
    ← Cast.complexMatrix_transpose,← Cast.complexMatrix_mul,original_density_full_gram]
  have complexScale (a : ℝ) (b : ℂ) (M : Matrix Basis Basis ℂ) : a • (b • M)=((a : ℂ)*b) • M := by
    ext i j
    simp only [Matrix.smul_apply,Complex.real_smul,smul_eq_mul,mul_assoc]
  rw [complexScale]
  unfold computedBase
  congr 1
  push_cast
  norm_num
  ring

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Dense
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
