import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Prepared.NetCore
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Prepared.Supply

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Prepared
open Collision Load.Source
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def loadedNetObservable : LoadedJoint := supplyReadout (pointerReadout finiteRootGain)
def pairedNetObservable : JointMatrix Propagation.Interface.Basis := receivedObservable loadedNetObservable
def pairedNetGain : ℝ := energy pairedNetObservable Input.finitePair

theorem loaded_net_hermitian : loadedNetObservable.IsHermitian :=
  supply_readout_hermitian _ (pointer_readout_hermitian _ finite_root_gain_hermitian)

theorem loaded_net_norm : ‖loadedNetObservable‖ ≤ (124/1000 : ℝ) :=
  (supply_readout_norm _ (pointer_readout_hermitian _ finite_root_gain_hermitian)).trans
    ((pointer_readout_norm _ finite_root_gain_hermitian).trans finite_root_gain_norm)

theorem source_loaded_net_read :
    Resource.pcEnergyOf (bodyRead SquareRoot.Full.sourceEleven)-Resource.pcEnergyOf (bodyRead SquareRoot.Full.sourceNine)=
      energy loadedNetObservable Source.received.joint := by
  rw [source_root_gain_read,sourceInitial,pointer_readout_energy,supply_readout_energy]
  rfl

theorem source_paired_input_cost :
    |(Resource.pcEnergyOf (bodyRead SquareRoot.Full.sourceEleven)-Resource.pcEnergyOf (bodyRead SquareRoot.Full.sourceNine))-
      pairedNetGain| ≤ (7/10^7 : ℝ) := by
  rw [source_loaded_net_read]
  have paid := source_received_finite_energy_error loadedNetObservable loaded_net_hermitian
  apply paid.trans
  have bound := mul_le_mul_of_nonneg_left loaded_net_norm (show (0 : ℝ) ≤ 51/10^7 by norm_num)
  exact bound.trans (by norm_num)

theorem original_paired_net_gain_error :
    |(Resource.pcEnergyOf (bodyRead Weak.execution.joint)-Resource.pcEnergyOf (bodyRead Weak.origin.joint))-
      pairedNetGain| ≤ (78/10^7 : ℝ) := by
  have triangle := abs_sub_le
    (Resource.pcEnergyOf (bodyRead Weak.execution.joint)-Resource.pcEnergyOf (bodyRead Weak.origin.joint))
    (Resource.pcEnergyOf (bodyRead SquareRoot.Full.sourceEleven)-Resource.pcEnergyOf (bodyRead SquareRoot.Full.sourceNine))
    pairedNetGain
  linarith [SquareRoot.Full.source_original_PC_gain_error,source_paired_input_cost]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Prepared
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
