import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Contraction.Full
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Contraction.Roots
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Post.SourceRead

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Contraction
open Propagation.Interface Load.Source Collision
open scoped Matrix
noncomputable section

theorem rotated_root_preserves (R : LoadedJoint) (kept : Preserves pceOrbit R) :
    Preserves pceOrbit (Post.rotatedRoot R) :=
  preserves_mul (preserves_mul free_polynomial_preserves kept) (preserves_star free_polynomial_preserves)

theorem finite_pointer_preserves : Preserves Sectors.pointerOrbit Post.finiteSourcePointer := by
  have root := Sectors.bodyObservable_preserves _ (rotated_root_preserves _ finite_root_preserves)
  have complement := Sectors.bodyObservable_preserves _ (rotated_root_preserves _ finite_complement_preserves)
  rw [Post.finiteSourcePointer,SquareRoot.raw_dilation_read]
  exact Sectors.fromBlocks_preserves _ _ _ _ root (preserves_neg complement) complement root

theorem finite_pc_observable_preserves : Preserves Sectors.pointerOrbit Post.finitePCObservable := by
  have pc : Preserves Sectors.reservoirOrbit (Post.pcLift (sourcePCH E)) :=
    preserves_tensor_left (preserves_relabel (preserves_tensor numeric_pc_preserves (preserves_one pcOrbit))
      (fun p : Sym2 Basis × Sym2 Basis => s(p.1,p.2))) _
  exact Sectors.fromBlocks_preserves _ _ _ _ pc (preserves_zero _) (preserves_zero _) pc

theorem finite_nine_preserves : Preserves Sectors.pointerOrbit Post.ninePolynomial :=
  preserves_mul (preserves_mul pointer_load_preserves pointer_feedback_preserves) pointer_feedback_preserves

theorem finite_eleven_preserves : Preserves Sectors.pointerOrbit Post.elevenPolynomial :=
  preserves_mul (preserves_mul pointer_load_preserves pointer_weak_preserves) finite_nine_preserves

theorem finite_net_observable_preserves : Preserves Sectors.pointerOrbit Post.finiteNetObservable :=
  preserves_sub (sandwich_preserves finite_eleven_preserves finite_pc_observable_preserves)
    (sandwich_preserves finite_nine_preserves finite_pc_observable_preserves)

theorem finite_root_net_preserves : Preserves Sectors.pointerOrbit Post.finiteRootNet :=
  sandwich_preserves finite_pointer_preserves finite_net_observable_preserves

theorem pointer_readout_preserves (O : PointerJoint) (kept : Preserves Sectors.pointerOrbit O) :
    Preserves Sectors.reservoirOrbit (Prepared.pointerReadout O) :=
  fun i j separated => kept (Sum.inl i) (Sum.inl j) separated

theorem fixed_donor_injective {α : Type*} (d : α) : Function.Injective (fun a : α => s(a,d)) := by
  intro a b same
  rcases Sym2.eq_iff.mp same with h | h
  · exact h.1
  · exact h.1.trans h.2

theorem donor_slice_preserves (O : Current.FullJoint) (kept : Preserves Sectors.reservoirOrbit O) :
    Preserves pceOrbit (Supply.donorSlice O) := by
  intro i j separated
  apply kept ((i.1,Supply.donorIndex),i.2) ((j.1,Supply.donorIndex),j.2)
  intro same
  exact separated (fixed_donor_injective (pcOrbit Supply.donorIndex) same)

theorem finite_net_preserves : Preserves pceOrbit Post.finiteLoadedNet :=
  donor_slice_preserves _ (sandwich_preserves full_supply_preserves
    (pointer_readout_preserves _ finite_root_net_preserves))

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Contraction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
