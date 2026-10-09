import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Post.Net
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Post.Pullback

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Post
open Collision Load.Source
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def calculatedRootNet : PointerJoint := star calculatedSourcePointer*calculatedNetObservable*calculatedSourcePointer
def finiteRootNet : PointerJoint := star finiteSourcePointer*finiteNetObservable*finiteSourcePointer

theorem original_root_net_coordinates : Quantum.conjugation Supply.installedFullFrame (Prepared.pointerReadout Prepared.finiteRootGain)=
    Prepared.pointerReadout calculatedRootNet := by
  rw [corner_conjugation]
  change Prepared.pointerReadout (Quantum.conjugation pointerFrame
    (star SquareRoot.Full.sourcePointer*(gainObservable Sectors.pointerPCObservable)*SquareRoot.Full.sourcePointer))=_
  rw [raw_pullback_covariance]
  rfl

def calculatedLoadedNet : LoadedJoint := Supply.donorSlice
  (star Supply.fullSupplyPolynomial*(Prepared.pointerReadout calculatedRootNet)*Supply.fullSupplyPolynomial)

def finiteLoadedNet : LoadedJoint := Supply.donorSlice
  (star Supply.fullSupplyPolynomial*(Prepared.pointerReadout finiteRootNet)*Supply.fullSupplyPolynomial)

def finiteNetGain : ℝ := energy finiteLoadedNet Actions.finiteReceivedBody

theorem source_supply_net_coordinates : Supply.finiteSupplyNetGain=energy calculatedLoadedNet Actions.finiteReceivedBody := by
  rw [Supply.finite_supply_addressed]
  have same : Quantum.conjugation Supply.installedFullFrame Supply.finiteSuppliedNetObservable=
      star Supply.fullSupplyPolynomial*(Prepared.pointerReadout calculatedRootNet)*Supply.fullSupplyPolynomial := by
    rw [Supply.finiteSuppliedNetObservable,raw_pullback_covariance,Supply.restoredSupply,Supply.conjugation_undo,
      original_root_net_coordinates]
  rw [same]
  rfl

theorem calculated_net_hermitian : calculatedNetObservable.IsHermitian :=
  Prepared.conjugation_hermitian pointerFrame _ Prepared.original_net_hermitian

theorem calculated_net_norm : ‖calculatedNetObservable‖ ≤ 1 := by
  have same : ‖calculatedNetObservable‖=‖gainObservable Sectors.pointerPCObservable‖ :=
    StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ PointerJoint pointerFrame) _
  rw [same]
  exact original_net_PC_norm.trans (by norm_num)

theorem calculated_root_net_hermitian : calculatedRootNet.IsHermitian :=
  Supply.raw_pullback_hermitian _ _ calculated_net_hermitian

theorem finite_root_net_hermitian : finiteRootNet.IsHermitian :=
  Supply.raw_pullback_hermitian _ _ finite_net_hermitian

theorem calculated_loaded_net_hermitian : calculatedLoadedNet.IsHermitian :=
  donor_slice_hermitian _ (Supply.raw_pullback_hermitian _ _ (Prepared.pointer_readout_hermitian _ calculated_root_net_hermitian))

theorem finite_loaded_net_hermitian : finiteLoadedNet.IsHermitian :=
  donor_slice_hermitian _ (Supply.raw_pullback_hermitian _ _ (Prepared.pointer_readout_hermitian _ finite_root_net_hermitian))

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Post
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
