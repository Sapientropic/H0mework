import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.RawCoordinates

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Dense
open Spectral Propagation.Interface
open scoped Matrix BigOperators
noncomputable section
variable {ι : Type*} [Fintype ι]

theorem read_ofFn (f : Basis → Int) (i : Basis) : Rows.read (List.ofFn f) i=f i := by
  change (List.ofFn f)[i.val]! = f i
  rw [getElem!_pos _ _ (by rw [List.length_ofFn]; exact i.isLt),List.getElem_ofFn]

theorem gram_mass_real_int (D : Matrix ι ι Int) (m : Int) (mass : (D*D.transpose).trace=m) :
    Preparation.gramMass (Cast.complexMatrix D)=(m : ℝ) := by
  unfold Preparation.gramMass Preparation.gram
  rw [← Cast.complexMatrix_transpose,← Cast.complexMatrix_mul]
  have trace : (Cast.complexMatrix (D*D.transpose)).trace=(m : ℂ) := by
    rw [← mass]
    simp only [Matrix.trace,Matrix.diag,Cast.complexMatrix,Int.cast_sum]
  rw [trace,Complex.intCast_re]

theorem normalized_gram_factor (D Q : Matrix ι ι ℂ) :
    star Q*Preparation.normalizedGram D*Q=
      ((Preparation.gramMass D)⁻¹ : ℝ) • (star (star D*Q)*(star D*Q)) := by
  simp only [Preparation.normalizedGram,Preparation.gram,← Matrix.star_eq_conjTranspose,
    mul_smul_comm,smul_mul_assoc,star_mul,star_star,mul_assoc]

theorem gram_mass_real_smul (D : Matrix ι ι ℂ) (c : ℝ) :
    Preparation.gramMass ((c : ℂ) • D)=c^2*Preparation.gramMass D := by
  rw [Preparation.gramMass,Preparation.gram,Matrix.conjTranspose_smul,
    Matrix.smul_mul,Matrix.mul_smul,smul_smul,Matrix.trace_smul]
  change (((c : ℂ)*star (c : ℂ))*(D*D.conjTranspose).trace).re=_
  rw [Complex.star_def,Complex.conj_ofReal]
  simp only [← Complex.ofReal_mul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero]
  change c*c*Preparation.gramMass D=c^2*Preparation.gramMass D
  ring

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Dense
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
