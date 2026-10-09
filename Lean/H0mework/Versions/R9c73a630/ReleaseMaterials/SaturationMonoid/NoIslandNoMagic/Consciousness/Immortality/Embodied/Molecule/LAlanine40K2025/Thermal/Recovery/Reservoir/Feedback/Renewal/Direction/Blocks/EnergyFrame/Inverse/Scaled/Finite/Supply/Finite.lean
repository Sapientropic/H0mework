import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Supply.Pulse
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Supply.Readout
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Supply.DonorConsumer

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Supply
open Collision Propagation.Interface Propagation.Producer Load.Source
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def restoredSupply : Current.FullJoint := Quantum.conjugation (star installedFullFrame) fullSupplyPolynomial

theorem restored_supply_error : ‖(Current.pulse (nativeClockStep : ℝ) : Current.FullJoint)-restoredSupply‖ ≤ (112/10^15 : ℝ) := by
  have norm := StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ Current.FullJoint installedFullFrame)
    ((Current.pulse (nativeClockStep : ℝ) : Current.FullJoint)-restoredSupply)
  change ‖Quantum.conjugation installedFullFrame ((Current.pulse (nativeClockStep : ℝ) : Current.FullJoint)-restoredSupply)‖=_ at norm
  rw [map_sub,restoredSupply,conjugation_undo] at norm
  have paid : ‖Quantum.conjugation installedFullFrame (Current.pulse (nativeClockStep : ℝ) : Current.FullJoint)-fullSupplyPolynomial‖ ≤ (112/10^15 : ℝ) := original_supply_polynomial_error
  exact norm ▸ paid

theorem restored_supply_norm : ‖restoredSupply‖ ≤ 1+(112/10^15 : ℝ) :=
  Input.approximated_unitary_norm _ _ _ restored_supply_error

def finiteSuppliedNetObservable : Current.FullJoint :=
  star restoredSupply*(Prepared.pointerReadout Prepared.finiteRootGain)*restoredSupply

def finiteSupplyLoadedObservable : LoadedJoint := finiteDonorReadout finiteSuppliedNetObservable

theorem finite_supplied_net_hermitian : finiteSuppliedNetObservable.IsHermitian :=
  raw_pullback_hermitian _ _ (Prepared.pointer_readout_hermitian _ Prepared.finite_root_gain_hermitian)

theorem finite_supplied_net_error : ‖suppliedNetObservable-finiteSuppliedNetObservable‖ ≤ (3/10^14 : ℝ) := by
  have paid := raw_pullback_error (Current.pulse (nativeClockStep : ℝ)) restoredSupply (Prepared.pointerReadout Prepared.finiteRootGain)
  have observed : ‖Prepared.pointerReadout Prepared.finiteRootGain‖ ≤ (124/1000 : ℝ) :=
    (Prepared.pointer_readout_norm _ Prepared.finite_root_gain_hermitian).trans Prepared.finite_root_gain_norm
  apply paid.trans
  exact (mul_le_mul (mul_le_mul (add_le_add le_rfl restored_supply_norm) observed (norm_nonneg _) (by norm_num))
    restored_supply_error (norm_nonneg _) (by norm_num)).trans (by norm_num)

theorem finite_supply_loaded_error : ‖finiteLoadedNetObservable-finiteSupplyLoadedObservable‖ ≤ (3/10^14 : ℝ) :=
  (finite_donor_readout_difference suppliedNetObservable finiteSuppliedNetObservable supplied_net_hermitian
    finite_supplied_net_hermitian).trans finite_supplied_net_error

theorem finite_received_body_norm : ‖Actions.finiteReceivedBody‖ ≤ 4 := by
  have first : ‖Quantum.conjugation Actions.calculatedReceivedWord Actions.preparedInput‖ ≤ 3 :=
    (StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ LoadedJoint Actions.calculatedReceivedWord) Actions.preparedInput).le.trans Actions.prepared_input_norm
  have triangle := norm_sub_le_norm_sub_add_norm_sub Actions.finiteReceivedBody
    (Quantum.conjugation Actions.calculatedReceivedWord Actions.preparedInput) 0
  simp only [sub_zero] at triangle
  have paid := Actions.finite_received_body_error
  rw [norm_sub_rev] at paid
  linarith

def finiteSupplyNetGain : ℝ :=
  energy (Quantum.conjugation installedLoadFrame finiteSupplyLoadedObservable) Actions.finiteReceivedBody

set_option maxRecDepth 4096 in
theorem finite_supply_energy_cost : |finiteDonorNetGain-finiteSupplyNetGain| ≤ (5/10^9 : ℝ) := by
  have read : finiteDonorNetGain-finiteSupplyNetGain=
      energy (Quantum.conjugation installedLoadFrame (finiteLoadedNetObservable-finiteSupplyLoadedObservable)) Actions.finiteReceivedBody := by
    simp only [finiteDonorNetGain,finiteSupplyNetGain,energy,map_sub,Matrix.sub_mul,Matrix.trace_sub,Complex.sub_re]
  rw [read]
  have bound := Input.energy_dimension_norm (Quantum.conjugation installedLoadFrame (finiteLoadedNetObservable-finiteSupplyLoadedObservable)) Actions.finiteReceivedBody
  have same : ‖Quantum.conjugation installedLoadFrame (finiteLoadedNetObservable-finiteSupplyLoadedObservable)‖=
      ‖finiteLoadedNetObservable-finiteSupplyLoadedObservable‖ :=
    StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ LoadedJoint installedLoadFrame) _
  rw [same] at bound
  have cardinal : Fintype.card (PairController × Fin 2)=38416 := by norm_num [PairController,Basis]
  rw [cardinal] at bound
  norm_num only [Nat.cast_ofNat] at bound
  have scaled := mul_le_mul_of_nonneg_left finite_supply_loaded_error (show (0 : ℝ) ≤ 38416 by norm_num)
  have product := mul_le_mul scaled finite_received_body_norm (norm_nonneg Actions.finiteReceivedBody)
    (show (0 : ℝ) ≤ 38416*(3/10^14) by norm_num)
  exact bound.trans (product.trans (by norm_num))

theorem original_finite_supply_net_error :
    |(Resource.pcEnergyOf (bodyRead Weak.execution.joint)-Resource.pcEnergyOf (bodyRead Weak.origin.joint))-
      finiteSupplyNetGain| ≤ (103/10^7 : ℝ) := by
  have triangle := abs_sub_le
    (Resource.pcEnergyOf (bodyRead Weak.execution.joint)-Resource.pcEnergyOf (bodyRead Weak.origin.joint)) finiteDonorNetGain finiteSupplyNetGain
  linarith [original_finite_donor_net_error,finite_supply_energy_cost]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Supply
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
