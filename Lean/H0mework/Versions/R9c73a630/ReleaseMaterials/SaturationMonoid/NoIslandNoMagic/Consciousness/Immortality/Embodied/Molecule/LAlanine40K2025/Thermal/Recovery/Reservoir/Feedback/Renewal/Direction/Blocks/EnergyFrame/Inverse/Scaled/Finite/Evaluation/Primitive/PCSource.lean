import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.PCAlgebra
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.LocalFlows

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive
open Propagation.Interface Propagation.Producer Load.Source
open scoped Matrix
noncomputable section

def ordinaryPCValues (a b : Basis) (time : ℝ) : Fin 4 → ℂ :=
  fun n => scalarPolynomial (((time : ℂ)*(-Complex.I))*pcValues (Donor.calculatedEnergy a) (Donor.calculatedEnergy b) n) 14

def sharedOrdinaryPC (a b : Basis) (time : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (pcAssembly (ordinaryPCValues a b time)).submatrix finProdFinEquiv finProdFinEquiv

theorem original_pc_shared (a b : Basis) (distinct : a ≠ b) (time : ℝ) :
    (Phase.flowPolynomial (sourcePCH E) time).submatrix (orbitPC a b) (orbitPC a b)=sharedOrdinaryPC a b time := by
  rw [ordinary_pc_original a b distinct,ordinaryPC,scalarHpc,← flow_reindex,pc_flow_resolution]
  rfl

theorem original_free_pc_shared (a b : Basis) (distinct : a ≠ b) :
    Phase.pcPolynomial.submatrix (orbitPC a b) (orbitPC a b)=sharedOrdinaryPC a b (nativeClockStep : ℝ) :=
  original_pc_shared a b distinct _

theorem original_parent_pc_shared (a b : Basis) (distinct : a ≠ b) :
    Actions.parentPCPolynomial.submatrix (orbitPC a b) (orbitPC a b)=sharedOrdinaryPC a b (2*(nativeClockStep : ℝ)) :=
  original_pc_shared a b distinct _

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
