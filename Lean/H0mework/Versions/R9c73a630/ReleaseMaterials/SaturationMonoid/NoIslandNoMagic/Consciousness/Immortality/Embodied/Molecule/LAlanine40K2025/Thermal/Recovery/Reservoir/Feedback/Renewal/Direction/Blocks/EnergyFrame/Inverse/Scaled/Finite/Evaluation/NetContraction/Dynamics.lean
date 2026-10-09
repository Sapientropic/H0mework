import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts.Consumer
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Contraction.Observable

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction
open Propagation.Interface Load.Source Collision Contraction
open scoped Matrix
noncomputable section
local instance : Fintype (Sym2 Basis) := Fintype.ofFinite _

theorem pc_preserves : Preserves pcOrbit Primitive.computedPC := assemble_preserves _ _
theorem parent_pc_preserves : Preserves pcOrbit Primitive.computedParentPC := assemble_preserves _ _
theorem recovery_pc_preserves : Preserves pcOrbit Primitive.computedRecoveryPC := assemble_preserves _ _
theorem load_preserves : Preserves pceOrbit LoadPrimitive.computedLoad := assemble_preserves _ _

theorem free_preserves : Preserves pceOrbit PCExecution.free := preserves_tensor_left pc_preserves _
theorem parent_preserves : Preserves pceOrbit PCExecution.parent := preserves_tensor_left parent_pc_preserves _
theorem recovery_preserves : Preserves pceOrbit PCExecution.recovery := preserves_tensor_left recovery_pc_preserves _
theorem received_preserves : Preserves pceOrbit LoadExecution.receivedWord :=
  preserves_mul (preserves_mul recovery_preserves load_preserves) parent_preserves

theorem shared_preserves :
    Preserves (fun p : PairController × PairController => s(pcOrbit p.1,pcOrbit p.2)) PCExecution.sharedPC :=
  preserves_relabel (preserves_tensor pc_preserves pc_preserves)
    (fun p : Sym2 Basis × Sym2 Basis => s(p.1,p.2))

theorem supply_preserves : Preserves Sectors.reservoirOrbit PCExecution.supply :=
  preserves_tensor_left (preserves_mul shared_preserves (partial_swap_preserves _ _)) _

theorem weak_preserves : Preserves Sectors.reservoirOrbit PCExecution.weak :=
  preserves_tensor_left (preserves_mul shared_preserves (partial_swap_preserves _ _)) _

theorem full_load_preserves : Preserves Sectors.reservoirOrbit LoadExecution.load :=
  local_matrix_preserves _ _ load_preserves pc_preserves

theorem pointer_load_preserves : Preserves Sectors.pointerOrbit LoadExecution.pointerLoad :=
  Sectors.fromBlocks_preserves _ _ _ _ full_load_preserves (preserves_zero _) (preserves_zero _)
    (preserves_smul full_load_preserves _)

theorem pointer_supply_preserves : Preserves Sectors.pointerOrbit LoadExecution.pointerSupply :=
  Sectors.fromBlocks_preserves _ _ _ _ full_load_preserves (preserves_zero _) (preserves_zero _)
    (preserves_smul supply_preserves _)

theorem pointer_weak_preserves : Preserves Sectors.pointerOrbit LoadExecution.pointerWeak :=
  Sectors.fromBlocks_preserves _ _ _ _ full_load_preserves (preserves_zero _) (preserves_zero _)
    (preserves_smul weak_preserves _)

theorem rotated_preserves (R : LoadedJoint) (kept : Preserves pceOrbit R) :
    Preserves pceOrbit (PCExecution.rotatedRoot R) :=
  preserves_mul (preserves_mul free_preserves kept) (preserves_star free_preserves)

theorem pointer_preserves : Preserves Sectors.pointerOrbit PCExecution.pointer := by
  have root := Sectors.bodyObservable_preserves _ (rotated_preserves _ finite_root_preserves)
  have complement := Sectors.bodyObservable_preserves _ (rotated_preserves _ finite_complement_preserves)
  rw [PCExecution.pointer,SquareRoot.raw_dilation_read]
  exact Sectors.fromBlocks_preserves _ _ _ _ root (preserves_neg complement) complement root

theorem nine_preserves : Preserves Sectors.pointerOrbit LoadExecution.nine :=
  preserves_mul (preserves_mul pointer_load_preserves pointer_supply_preserves) pointer_supply_preserves

theorem eleven_preserves : Preserves Sectors.pointerOrbit LoadExecution.eleven :=
  preserves_mul (preserves_mul pointer_load_preserves pointer_weak_preserves) nine_preserves

theorem net_observable_preserves : Preserves Sectors.pointerOrbit LoadExecution.netObservable :=
  preserves_sub (sandwich_preserves eleven_preserves finite_pc_observable_preserves)
    (sandwich_preserves nine_preserves finite_pc_observable_preserves)

theorem root_net_preserves : Preserves Sectors.pointerOrbit LoadExecution.rootNet :=
  sandwich_preserves pointer_preserves net_observable_preserves

theorem net_preserves : Preserves pceOrbit LoadExecution.loadedNet :=
  donor_slice_preserves _ (sandwich_preserves supply_preserves
    (pointer_readout_preserves _ root_net_preserves))

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
