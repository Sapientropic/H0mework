import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Contraction.Dynamics
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Post.Pointer
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Sectors.Dynamics

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Contraction
open Propagation.Interface Load.Source Collision
open scoped Matrix
noncomputable section

theorem local_matrix_preserves (U : LoadedJoint) (V : Matrix PairController PairController ℂ)
    (left : Preserves pceOrbit U) (right : Preserves pcOrbit V) :
    Preserves Sectors.reservoirOrbit (Post.localMatrix U V) := by
  intro i j separated
  change U (i.1.1,i.2) (j.1.1,j.2)*V i.1.2 j.1.2=0
  by_cases same : pcOrbit i.1.1=pcOrbit j.1.1
  · rw [right _ _ (fun other => separated (by simp only [Sectors.reservoirOrbit,same,other])),mul_zero]
  · rw [left (i.1.1,i.2) (j.1.1,j.2) same,zero_mul]

theorem full_load_preserves : Preserves Sectors.reservoirOrbit Post.fullLoadPolynomial :=
  local_matrix_preserves _ _ load_polynomial_preserves pc_polynomial_preserves

theorem partial_swap_preserves (a b : ℝ) :
    Preserves (fun p : PairController × PairController => s(pcOrbit p.1,pcOrbit p.2)) (partialSwap a b) :=
  preserves_sub (preserves_smul (preserves_one _) _) (preserves_smul Sectors.pair_swap_preserves _)

theorem shared_pc_preserves :
    Preserves (fun p : PairController × PairController => s(pcOrbit p.1,pcOrbit p.2)) Supply.sharedPCPolynomial :=
  preserves_relabel (preserves_tensor pc_polynomial_preserves pc_polynomial_preserves)
    (fun p : Sym2 Basis × Sym2 Basis => s(p.1,p.2))

theorem full_supply_preserves : Preserves Sectors.reservoirOrbit Supply.fullSupplyPolynomial :=
  preserves_tensor_left (preserves_mul shared_pc_preserves (partial_swap_preserves _ _)) _

theorem full_weak_preserves : Preserves Sectors.reservoirOrbit Post.fullWeakPolynomial :=
  preserves_tensor_left (preserves_mul shared_pc_preserves (partial_swap_preserves _ _)) _

theorem pointer_load_preserves : Preserves Sectors.pointerOrbit Post.pointerLoadPolynomial :=
  Sectors.fromBlocks_preserves _ _ _ _ full_load_preserves (preserves_zero _) (preserves_zero _)
    (preserves_smul full_load_preserves _)

theorem pointer_feedback_preserves : Preserves Sectors.pointerOrbit Post.pointerFeedbackPolynomial :=
  Sectors.fromBlocks_preserves _ _ _ _ full_load_preserves (preserves_zero _) (preserves_zero _)
    (preserves_smul full_supply_preserves _)

theorem pointer_weak_preserves : Preserves Sectors.pointerOrbit Post.pointerWeakPolynomial :=
  Sectors.fromBlocks_preserves _ _ _ _ full_load_preserves (preserves_zero _) (preserves_zero _)
    (preserves_smul full_weak_preserves _)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Contraction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
