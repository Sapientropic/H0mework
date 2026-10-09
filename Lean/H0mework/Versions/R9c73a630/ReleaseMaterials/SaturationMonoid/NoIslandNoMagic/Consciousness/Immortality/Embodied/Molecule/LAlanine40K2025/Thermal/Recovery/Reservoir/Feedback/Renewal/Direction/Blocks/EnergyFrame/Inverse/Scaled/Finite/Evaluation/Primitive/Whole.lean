import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Ordinary
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Diagonal
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.FiberMaterial

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive
open Propagation.Interface Load.Source
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
local instance : Fintype (Sym2 Basis) := Fintype.ofFinite _

def sourcePCFamily (k : Sym2 Basis) : FiberMaterial k := by
  let pair := Sym2.sortEquiv k
  have source : s(pair.val.1,pair.val.2)=k := Sym2.sortEquiv.symm_apply_apply k
  have material : FiberMaterial s(pair.val.1,pair.val.2) := by
    by_cases same : pair.val.1=pair.val.2
    · rw [← same]
      exact diagonalFiberMaterial pair.val.1 (allDiagonal pair.val.1)
    · exact ordinaryFiberMaterial pair.val.1 pair.val.2 same
        (allOrdinary pair.val.1 pair.val.2 (lt_of_le_of_ne pair.property same))
  exact source ▸ material

def computedPC : Matrix PairController PairController ℂ := SquareRoot.Full.assemble pcOrbit (fun k => (sourcePCFamily k).one)
def computedParentPC : Matrix PairController PairController ℂ := SquareRoot.Full.assemble pcOrbit (fun k => (sourcePCFamily k).two)
def computedRecoveryPC : Matrix PairController PairController ℂ := SquareRoot.Full.assemble pcOrbit (fun k => (sourcePCFamily k).three)

theorem original_computed_PC : ‖Phase.pcPolynomial-computedPC‖ ≤ (4/10^24 : ℝ) :=
  SquareRoot.Full.assemble_error pcOrbit _ Contraction.pc_polynomial_preserves _ _ (by norm_num)
    (fun k => (sourcePCFamily k).one_error)

theorem original_computed_parent_PC : ‖Actions.parentPCPolynomial-computedParentPC‖ ≤ (4/10^24 : ℝ) :=
  SquareRoot.Full.assemble_error pcOrbit _ (Contraction.flow_polynomial_preserves Contraction.numeric_pc_preserves _) _ _ (by norm_num)
    (fun k => (sourcePCFamily k).two_error)

theorem original_computed_recovery_PC : ‖Actions.recoveryPCPolynomial-computedRecoveryPC‖ ≤ (4/10^24 : ℝ) :=
  SquareRoot.Full.assemble_error pcOrbit _ (Contraction.flow_polynomial_preserves (Contraction.diagonal_reverse_preserves _) _) _ _ (by norm_num)
    (fun k => (sourcePCFamily k).three_error)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
