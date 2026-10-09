import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.Algebra
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.Environment

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface
open scoped Matrix BigOperators

def fromIntegers {α β : Type*} (R I : Matrix α β Int) (d : Int) : MatrixQ α β :=
  fun i j => ((R i j : ℚ)/(d : ℚ),(I i j : ℚ)/(d : ℚ))

theorem fromIntegers_value {α : Type*} (R I : Matrix α α Int) (d : Int) :
    qvalue (fromIntegers R I d)=InputProducts.scaledMatrix R I d := by
  ext i j
  simp only [qvalue,fromIntegers,Scalar.value,Rat.cast_div,Rat.cast_intCast,
    InputProducts.scaledMatrix,InputProducts.complexMatrix,Matrix.smul_apply,smul_eq_mul]
  ring

def systemQ : MatrixQ Basis Basis := fromIntegers InputProducts.systemR InputProducts.systemI (10^24)
def bathQ : MatrixQ Basis Basis := fromIntegers InputProducts.bathR InputProducts.bathI (10^24)

theorem systemQ_value : qvalue systemQ=InputProducts.system := fromIntegers_value _ _ _
theorem bathQ_value : qvalue bathQ=InputProducts.bath := fromIntegers_value _ _ _

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
