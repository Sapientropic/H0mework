import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.Collision
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Phase.Scalar

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
open Collision Propagation.Interface Propagation.Producer Load.Producer.StrictThermal
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def initialPhase : ℂ := (Thermal.Source.exchangeCosine : ℂ)-Complex.I*(Thermal.Source.exchangeSine : ℂ)
def finiteCouplingPhase : ℂ := initialPhase*Phase.pointerPhase
def finiteCosine : ℝ := finiteCouplingPhase.re
def finiteSine : ℝ := -finiteCouplingPhase.im

theorem initial_phase_norm : ‖initialPhase‖=1 := by
  norm_num [initialPhase,Thermal.Source.exchangeCosine,Thermal.Source.exchangeSine,Complex.norm_def,Complex.normSq_apply]

theorem source_phase_real : (freePhase (nativeClockStep : ℝ) : ℂ).re=Real.cos (2*(nativeClockStep : ℝ)) := by
  rw [Phase.original_phase_components]
  simp only [Complex.sub_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,Complex.I_im,Complex.ofReal_im,mul_zero,zero_mul,sub_zero,
    BasisInverse.actualAngle,Real.sin_pi_div_two_sub,Real.cos_pi_div_two_sub,Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq (nativeClockStep : ℝ)]

theorem source_phase_imag : (freePhase (nativeClockStep : ℝ) : ℂ).im=-Real.sin (2*(nativeClockStep : ℝ)) := by
  rw [Phase.original_phase_components]
  simp only [Complex.sub_im,Complex.ofReal_im,Complex.mul_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,mul_zero,zero_add,one_mul,zero_sub,
    BasisInverse.actualAngle,Real.sin_pi_div_two_sub,Real.cos_pi_div_two_sub,Real.sin_two_mul]

theorem merged_phase_read : initialPhase*(freePhase (nativeClockStep : ℝ) : ℂ)=
    (mergedCosine : ℂ)-Complex.I*(mergedSine : ℂ) := by
  apply Complex.ext <;>
    simp only [initialPhase,Complex.mul_re,Complex.mul_im,Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,mul_zero,zero_mul,one_mul,zero_add,zero_sub,sub_zero,source_phase_real,source_phase_imag,mergedCosine,mergedSine] <;> ring

theorem merged_phase_error : ‖((mergedCosine : ℂ)-Complex.I*(mergedSine : ℂ))-finiteCouplingPhase‖ ≤ (12/10^18 : ℝ) := by
  rw [← merged_phase_read,finiteCouplingPhase,← mul_sub,norm_mul,initial_phase_norm,one_mul]
  exact Phase.original_phase_error

theorem finite_coupling_coefficients : |mergedCosine-finiteCosine| ≤ (12/10^18 : ℝ) ∧
    |mergedSine-finiteSine| ≤ (12/10^18 : ℝ) := by
  have realPart := (Complex.abs_re_le_norm (((mergedCosine : ℂ)-Complex.I*(mergedSine : ℂ))-finiteCouplingPhase)).trans merged_phase_error
  have imaginary := (Complex.abs_im_le_norm (((mergedCosine : ℂ)-Complex.I*(mergedSine : ℂ))-finiteCouplingPhase)).trans merged_phase_error
  constructor
  · simpa [finiteCosine] using realPart
  · have same : mergedSine-finiteSine=-(((mergedCosine : ℂ)-Complex.I*(mergedSine : ℂ))-finiteCouplingPhase).im := by simp [finiteSine]; ring
    rw [same,abs_neg]
    exact imaginary

def finiteCollisionMatrix : JointMatrix Basis := partialSwap finiteCosine finiteSine

theorem finite_collision_matrix_error : ‖(mergedUnitary : JointMatrix Basis)-finiteCollisionMatrix‖ ≤ (3/10^17 : ℝ) := by
  have read : (mergedUnitary : JointMatrix Basis)=partialSwap mergedCosine mergedSine := merged_collision_matrix
  have split : partialSwap mergedCosine mergedSine-finiteCollisionMatrix=
      ((mergedCosine-finiteCosine : ℝ) : ℂ) • (1 : JointMatrix Basis)-
        (Complex.I*((mergedSine-finiteSine : ℝ) : ℂ)) • swapOperator := by
    ext i j
    simp only [finiteCollisionMatrix,partialSwap,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
    push_cast
    ring
  rw [read,split]
  apply (norm_sub_le _ _).trans
  simp only [norm_smul,norm_one,swap_norm,mul_one,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs]
  linarith [finite_coupling_coefficients.1,finite_coupling_coefficients.2]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
