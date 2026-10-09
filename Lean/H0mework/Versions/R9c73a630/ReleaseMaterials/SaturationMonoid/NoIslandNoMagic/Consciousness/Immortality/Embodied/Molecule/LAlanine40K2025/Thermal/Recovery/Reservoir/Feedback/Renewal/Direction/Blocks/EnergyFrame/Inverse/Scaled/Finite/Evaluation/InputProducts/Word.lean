import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts.FieldSource
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts.Diagonal
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts.Scaling

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts
open Spectral Propagation.Interface
open scoped Matrix BigOperators Matrix.Norms.L2Operator
noncomputable section

def wordRe : Matrix Basis Basis Int := fieldRe*Matrix.diagonal activeRe-fieldIm*Matrix.diagonal activeIm

def wordIm : Matrix Basis Basis Int := fieldRe*Matrix.diagonal activeIm+fieldIm*Matrix.diagonal activeRe

def baseDenominator : Int := Dense.densitySquaredMass*10^30

theorem original_system_word_integer : Field.computedSystemWord=scaledMatrix wordRe wordIm (10^48) := by
  rw [Field.computedSystemWord,original_field_values,original_active_integer,scaledMatrix_mul]
  norm_num only [show (10^24 : Int)*(10^24)=10^48 by norm_num]
  rfl

theorem original_base_integer : Dense.computedBase=scaledMatrix Dense.densityGramInt 0 baseDenominator := by
  rw [scaledMatrix,complexMatrix_real,Dense.computedBase]
  unfold baseDenominator
  norm_num only [Int.cast_mul,Int.cast_pow,Int.cast_ofNat,one_div]

theorem word_real_entry (i j : Basis) : wordRe i j=fieldRe i j*activeRe j-fieldIm i j*activeIm j := by
  simp only [wordRe,Matrix.sub_apply,Matrix.mul_diagonal]

theorem word_imag_entry (i j : Basis) : wordIm i j=fieldRe i j*activeIm j+fieldIm i j*activeRe j := by
  simp only [wordIm,Matrix.add_apply,Matrix.mul_diagonal]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
