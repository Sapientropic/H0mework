import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.UniformGainQuadratic
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.SharpNorm
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Collision Load.Producer.StrictThermal Contraction
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section



/-! Each original ordinary net is a charged restriction of the same loaded observable. -/

private theorem local_readout_norm_two (k : Sym2 Basis) [Nonempty (BodyFiber k)] : ‖localReadout k‖ ≤ (2 : ℝ) := by
  rw [← local_readout_exact]
  exact (submatrix_norm_le LoadExecution.loadedNet
    (Subtype.val : BodyFiber k → _) (Subtype.val : BodyFiber k → _)
    Subtype.val_injective Subtype.val_injective).trans source_loaded_net_norm_two

private theorem local_received_word_norm (k : Sym2 Basis) [Nonempty (BodyFiber k)] :
    ‖localReceivedWord k‖ ≤ (1001/1000 : ℝ) :=
  (submatrix_norm_le LoadExecution.receivedWord
    (Subtype.val : BodyFiber k → _) (Subtype.val : BodyFiber k → _)
    Subtype.val_injective Subtype.val_injective).trans source_received_word_norm_sharp

theorem channel_net_norm_loaded {β δ : Type*} [Fintype β] [Fintype δ]
    [DecidableEq β] [Nonempty β]
    (k : Sym2 Basis) (body : β ≃ BodyFiber k) (full : δ ≃ FullFiber k)
    (insert : β → δ) (incidence : ∀ i, full (insert i)=insertDonor k (body i)) :
    ‖channelNet k body full insert‖ ≤ (2005/1000 : ℝ) := by
  let : Nonempty (BodyFiber k) := Nonempty.map body (inferInstance : Nonempty β)
  rw [← channel_net_exact,← entrance_columns_exact,
    ← coordinate_readout_exact k body full insert incidence]
  have received := (submatrix_norm_le (localReceivedWord k) body body
    body.injective body.injective).trans (local_received_word_norm k)
  have readout := (submatrix_norm_le (localReadout k) body body
    body.injective body.injective).trans (local_readout_norm_two k)
  have pullback := Prepared.sandwich_norm ((localReceivedWord k).submatrix body body)
    ((localReadout k).submatrix body body)
  apply pullback.trans
  calc
    _ ≤ (1001/1000 : ℝ)^2*2 := by gcongr
    _ ≤ 2005/1000 := by norm_num

theorem source_ordinary_qnet_selected (a b : Basis) (ordered : a < b) :
    sourceOrdinaryQNet a b ordered =
      Compact.selectedNet (s(a,b)) (Scaled.Order.offDiagonalPCEEquiv a b ordered.ne)
        (ordinaryFullEquiv a b ordered.ne) ordinaryInjection chargedInjection := by
  simp only [sourceOrdinaryQNet,Compact.selectedNet,qvalue_submatrix,
    ordinary_nine_columns_value,ordinary_eleven_columns_value,ordinary_pc_pointer_value a b ordered]

theorem source_ordinary_qnet_norm_loaded (a b : Basis) (ordered : a < b) :
    ‖sourceOrdinaryQNet a b ordered‖ ≤ (2005/1000 : ℝ) := by
  rw [source_ordinary_qnet_selected,← Compact.selected_net_exact]
  exact (submatrix_norm_le _ chargedInjection chargedInjection
    charged_injection_injective charged_injection_injective).trans
    (channel_net_norm_loaded _ _ _ _ (ordinary_donor_injection a b ordered.ne))

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
