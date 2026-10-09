import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.BlockProgram

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Collision
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

theorem calculated_net_norm_sharp : ‖Post.calculatedNetObservable‖ ≤ (123/1000 : ℝ) :=
  (StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ PointerJoint Post.pointerFrame)
    (gainObservable Sectors.pointerPCObservable)).le.trans original_net_PC_norm

theorem source_net_norm_sharp : ‖LoadExecution.netObservable‖ ≤ (124/1000 : ℝ) := by
  have finite := PCExecution.close_norm Post.calculatedNetObservable Post.finiteNetObservable
    (123/1000) (5/10^10) calculated_net_norm_sharp Post.original_finite_net_observable_error
  have pc := PCExecution.close_norm Post.finiteNetObservable PCExecution.netObservable
    _ _ finite PCExecution.net_observable_error
  have load := PCExecution.close_norm PCExecution.netObservable LoadExecution.netObservable
    _ _ pc LoadExecution.net_observable_error
  linarith

theorem source_pointer_norm_sharp : ‖PCExecution.pointer‖ ≤ (2001/1000 : ℝ) := by
  have h := PCExecution.close_norm Post.finiteSourcePointer PCExecution.pointer
    _ _ Post.finite_source_pointer_norm PCExecution.pointer_error
  linarith

theorem source_supply_norm_sharp : ‖PCExecution.supply‖ ≤ (2001/1000 : ℝ) := by
  have h := PCExecution.close_norm Supply.fullSupplyPolynomial PCExecution.supply
    _ _ Post.finite_full_supply_norm PCExecution.supply_error
  linarith

theorem source_root_net_norm_sharp : ‖LoadExecution.rootNet‖ ≤ (497/1000 : ℝ) := by
  have h := Prepared.sandwich_norm PCExecution.pointer LoadExecution.netObservable
  rw [LoadExecution.rootNet]
  apply h.trans
  calc
    ‖PCExecution.pointer‖^2*‖LoadExecution.netObservable‖ ≤
      (2001/1000 : ℝ)^2*(124/1000 : ℝ) := by
        gcongr
        · exact source_pointer_norm_sharp
        · exact source_net_norm_sharp
    _ ≤ 497/1000 := by norm_num

theorem source_loaded_net_norm_two : ‖LoadExecution.loadedNet‖ ≤ (2 : ℝ) := by
  have corner := (Prepared.pointer_readout_norm LoadExecution.rootNet
    LoadExecution.root_net_hermitian).trans source_root_net_norm_sharp
  have hermitian := Supply.raw_pullback_hermitian PCExecution.supply _
    (Prepared.pointer_readout_hermitian _ LoadExecution.root_net_hermitian)
  have h := (Post.donor_slice_norm _ hermitian).trans
    (Prepared.sandwich_norm PCExecution.supply (Prepared.pointerReadout LoadExecution.rootNet))
  rw [LoadExecution.loadedNet]
  apply h.trans
  calc
    ‖PCExecution.supply‖^2*‖Prepared.pointerReadout LoadExecution.rootNet‖ ≤
      (2001/1000 : ℝ)^2*(497/1000 : ℝ) := by
        gcongr
        · exact source_supply_norm_sharp
    _ ≤ 2 := by norm_num

theorem source_received_word_norm_sharp : ‖LoadExecution.receivedWord‖ ≤ (1001/1000 : ℝ) := by
  have finite := Input.approximated_unitary_norm Actions.calculatedReceivedWord
    Actions.finiteReceivedWord _ Actions.original_received_word_polynomial_error
  have pc := PCExecution.close_norm Actions.finiteReceivedWord PCExecution.receivedWord
    _ _ finite PCExecution.received_word_error
  have load := PCExecution.close_norm PCExecution.receivedWord LoadExecution.receivedWord
    _ _ pc LoadExecution.received_word_error
  linarith

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
