import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Field.States
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts.Complex

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts
open Spectral Propagation.Interface
open scoped Matrix BigOperators Matrix.Norms.L2Operator
noncomputable section

def fieldRe : Matrix Basis Basis Int := Field.termInt 0-Field.termInt 2+Field.termInt 4-Field.termInt 6

def fieldIm : Matrix Basis Basis Int := -Field.termInt 1+Field.termInt 3-Field.termInt 5+Field.termInt 7

private theorem phased_eight {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Nat → Matrix ι ι ℂ) :
    Field.phasedSum M 8=(M 0-M 2+M 4-M 6)+Complex.I • (-M 1+M 3-M 5+M 7) := by
  ext i j
  norm_num [Field.phasedSum,Finset.sum_range_succ,Matrix.smul_apply,Matrix.add_apply,Matrix.sub_apply,smul_eq_mul,pow_succ,Complex.I_mul_I]
  ring

theorem original_field_values : Field.computedPolynomial=scaledMatrix fieldRe fieldIm (10^24) := by
  rw [Field.computedPolynomial,phased_eight]
  ext i j
  simp only [Field.termMatrix,scaledMatrix,fieldRe,fieldIm,complexMatrix,Cast.complexMatrix,
    Matrix.add_apply,Matrix.sub_apply,Matrix.neg_apply,Matrix.smul_apply,smul_eq_mul,
    Int.cast_sub,Int.cast_add,Int.cast_neg,Int.cast_pow,Int.cast_ofNat]
  ring

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
