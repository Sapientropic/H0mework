import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Polynomial
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Contraction.Dynamics
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Order.Fibers

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive
open Propagation.Interface Load.Source Propagation.Producer
open scoped Matrix
noncomputable section

def ordinaryPC (a b : Basis) (time : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Phase.flowPolynomial (scalarHpc (Donor.calculatedEnergy a) (Donor.calculatedEnergy b)) time

def diagonalPC (a : Basis) (time : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Phase.flowPolynomial (diagonalHpc (Donor.calculatedEnergy a)) time

def ordinaryLoad (a b : Basis) (time : ℝ) : Matrix ((Fin 2 × Fin 2) × Fin 2) ((Fin 2 × Fin 2) × Fin 2) ℂ :=
  Phase.flowPolynomial (Scaled.Order.smallLoaded (Donor.calculatedEnergy a) (Donor.calculatedEnergy b)) time

def diagonalLoad (a : Basis) (time : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Phase.flowPolynomial (Scaled.Order.diagonalLoaded (Donor.calculatedEnergy a)) time

theorem ordinary_pc_original (a b : Basis) (distinct : a ≠ b) (time : ℝ) :
    (Phase.flowPolynomial (sourcePCH E) time).submatrix (orbitPC a b) (orbitPC a b)=ordinaryPC a b time := by
  have exact := original_flow_restriction Contraction.numeric_pc_preserves s(a,b) (offDiagonalEquiv a b distinct) time
  have h : ((restrict pcOrbit s(a,b) (sourcePCH E)).submatrix (offDiagonalEquiv a b distinct) (offDiagonalEquiv a b distinct))=
      scalarHpc (Donor.calculatedEnergy a) (Donor.calculatedEnergy b) := Scaled.Order.numeric_hpc_block a b distinct
  rw [h] at exact
  exact exact

theorem diagonal_pc_original (a : Basis) (time : ℝ) :
    (Phase.flowPolynomial (sourcePCH E) time).submatrix (fun c : Fin 2 => ((a,a),c)) (fun c : Fin 2 => ((a,a),c))=diagonalPC a time := by
  have exact := original_flow_restriction Contraction.numeric_pc_preserves s(a,a) (diagonalEquiv a) time
  have h : ((restrict pcOrbit s(a,a) (sourcePCH E)).submatrix (diagonalEquiv a) (diagonalEquiv a))=
      diagonalHpc (Donor.calculatedEnergy a) := Scaled.Order.numeric_diagonal_PC a
  rw [h] at exact
  exact exact

theorem ordinary_load_original (a b : Basis) (distinct : a ≠ b) (time : ℝ) :
    (Phase.flowPolynomial numericLoadHamiltonian time).submatrix (Scaled.Order.orbitPCE a b) (Scaled.Order.orbitPCE a b)=ordinaryLoad a b time := by
  have exact := original_flow_restriction Contraction.numeric_load_preserves s(a,b) (Scaled.Order.offDiagonalPCEEquiv a b distinct) time
  have h : ((restrict pceOrbit s(a,b) numericLoadHamiltonian).submatrix (Scaled.Order.offDiagonalPCEEquiv a b distinct)
      (Scaled.Order.offDiagonalPCEEquiv a b distinct))=Scaled.Order.smallLoaded (Donor.calculatedEnergy a) (Donor.calculatedEnergy b) :=
    Scaled.Order.original_numeric_load_block a b distinct
  rw [h] at exact
  exact exact

theorem diagonal_load_original (a : Basis) (time : ℝ) :
    (Phase.flowPolynomial numericLoadHamiltonian time).submatrix (Scaled.Order.diagonalPCE a) (Scaled.Order.diagonalPCE a)=diagonalLoad a time := by
  have exact := original_flow_restriction Contraction.numeric_load_preserves s(a,a) (Scaled.Order.diagonalPCEEquiv a) time
  have h : ((restrict pceOrbit s(a,a) numericLoadHamiltonian).submatrix (Scaled.Order.diagonalPCEEquiv a) (Scaled.Order.diagonalPCEEquiv a))=
      Scaled.Order.diagonalLoaded (Donor.calculatedEnergy a) := Scaled.Order.numeric_diagonal_load a
  rw [h] at exact
  exact exact

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
