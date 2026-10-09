import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.ConcreteDiagonal.Pointer

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface
open scoped Matrix BigOperators

def literalDiagonalRoot (F G : Matrix (Fin 4) (Fin 4) ℚ) :
    MatrixQ (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  (qmultiply (fun i j => (F i j,G i j))
    (qadjoint (fun i j => (F i j,G i j)))).submatrix
      SquareRoot.Full.pairIndex SquareRoot.Full.pairIndex

def firstSixPlus : Fin 6 → Matrix (Fin 4) (Fin 4) ℚ :=
  ![SquareRoot.Full.Factors.D000.factor0Plus,
    SquareRoot.Full.Factors.D000.factor1Plus,
    SquareRoot.Full.Factors.D000.factor2Plus,
    SquareRoot.Full.Factors.D000.factor3Plus,
    SquareRoot.Full.Factors.D000.factor4Plus,
    SquareRoot.Full.Factors.D000.factor5Plus]

def firstSixMinus : Fin 6 → Matrix (Fin 4) (Fin 4) ℚ :=
  ![SquareRoot.Full.Factors.D000.factor0Minus,
    SquareRoot.Full.Factors.D000.factor1Minus,
    SquareRoot.Full.Factors.D000.factor2Minus,
    SquareRoot.Full.Factors.D000.factor3Minus,
    SquareRoot.Full.Factors.D000.factor4Minus,
    SquareRoot.Full.Factors.D000.factor5Minus]

def firstSixDiagonal (a : Fin 6) : Fin 97 := ⟨a.val,by omega⟩

def firstSixRootQ (a : Fin 6) : MatrixQ (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  literalDiagonalRoot (firstSixPlus a) 0
def firstSixComplementQ (a : Fin 6) : MatrixQ (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  literalDiagonalRoot (firstSixMinus a) 0

def literalDonorRootQ : MatrixQ (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  literalDiagonalRoot SquareRoot.Full.Factors.Donor.realPlus
    SquareRoot.Full.Factors.Donor.imagPlus
def literalDonorComplementQ : MatrixQ (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  literalDiagonalRoot SquareRoot.Full.Factors.Donor.realMinus
    SquareRoot.Full.Factors.Donor.imagMinus

theorem first_six_root_source (a : Fin 6) :
    rootDiagonalQ (firstSixDiagonal a) = firstSixRootQ a := by
  fin_cases a <;> rfl

theorem first_six_complement_source (a : Fin 6) :
    complementDiagonalQ (firstSixDiagonal a) = firstSixComplementQ a := by
  fin_cases a <;> rfl

theorem donor_root_source : rootDonorQ = literalDonorRootQ := rfl
theorem donor_complement_source : complementDonorQ = literalDonorComplementQ := rfl

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
