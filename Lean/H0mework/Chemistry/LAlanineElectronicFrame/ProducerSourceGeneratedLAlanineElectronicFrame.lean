import H0mework.Chemistry.LAlanineElectronicFrame.ProducerSourceGeneratedSCFTransportSeparation
import H0mework.Chemistry.LAlanineElectronicFrame.ConsumerSourceGeneratedFrameOperatorReadout

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.ElectronicFrame.Producer

open Propagation.Interface
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section

def presentedMatrix : Matrix Basis Basis ℂ := Source.heldStateTransport heldMatrix

theorem heldMatrix_hermitian : heldMatrix.IsHermitian :=
  Propagation.Dynamics.initialDensityMatrix_hermitian Source.currentElectronicSource

theorem presentedMatrix_hermitian : presentedMatrix.IsHermitian :=
  Source.heldStateTransport_hermitian heldMatrix heldMatrix_hermitian

def frameClosure : Prop :=
  Source.currentElectronicSource = Propagation.Source.electronicSource ∧
  Source.deltaEntryMagnitude = 351148 ∧ Source.symmetricEntryMagnitude = 15264 ∧
  ‖Source.crossMatrix - 1‖ < 1 ∧ ‖star Source.crossMatrix * Source.crossMatrix - 1‖ < (2 : ℝ) / 10 ^ 11 ∧
  (Source.sourceUnitary : Matrix Basis Basis ℂ) * CFC.abs Source.crossMatrix = Source.crossMatrix ∧
  (Source.sourceUnitary : Matrix Basis Basis ℂ) + Source.sourceProjectionResidual = Source.crossMatrix ∧
  ‖Source.sourceProjectionResidual‖ ≤ ‖star Source.crossMatrix * Source.crossMatrix - 1‖ ∧
  (Source.sourceUnitary : Matrix Basis Basis ℂ) ≠ 1 ∧
  heldMatrix.IsHermitian ∧ presentedMatrix.IsHermitian ∧
  star (Source.sourceUnitary : Matrix Basis Basis ℂ) * presentedMatrix * Source.sourceUnitary = heldMatrix ∧
  presentedMatrix.trace = heldMatrix.trace ∧ presentedMatrix.charpoly = heldMatrix.charpoly ∧
  spectrum ℂ presentedMatrix = spectrum ℂ heldMatrix ∧
  Function.Injective Source.heldStateTransport ∧
  ‖heldMatrix‖ ≤ 10 ∧
  (1 : ℝ) / 10 ^ 9 < ‖(Source.crossMatrix * heldMatrix * star Source.crossMatrix - scfBenchmark) 19 19‖ ∧
  ‖presentedMatrix - Source.crossMatrix * heldMatrix * star Source.crossMatrix‖ < (6 : ℝ) / 10 ^ 10 ∧
  presentedMatrix ≠ scfBenchmark ∧
  Observer.targetHamiltonian.IsHermitian ∧ Observer.operatorChange.IsHermitian ∧
  (∀ reader : Matrix Basis Basis ℂ, (presentedMatrix * reader).trace = (heldMatrix * Observer.pull reader).trace) ∧
  (presentedMatrix * Observer.targetHamiltonian).trace - (heldMatrix * Observer.currentHamiltonian).trace =
    (heldMatrix * Observer.operatorChange).trace

/-- The geometry supplies the unitary; the new SCF matrix remains an independent benchmark. -/
theorem sourceGeneratedElectronicFrame : frameClosure :=
  ⟨Source.currentElectronicSource_eq_parent, Source.deltaEntryMagnitude_exact,
    Source.symmetricEntryMagnitude_exact, Source.crossMatrix_close, Source.gram_norm_small,
    Source.sourceUnitary_factorization, Source.sourceProjectionResidual_reconstruction,
    Polar.projectionResidual_norm_le_gram _ Source.crossMatrix_close, Source.sourceUnitary_not_identity,
    heldMatrix_hermitian, presentedMatrix_hermitian, Source.heldStateTransport_faithful heldMatrix,
    Source.heldStateTransport_trace heldMatrix, Source.heldStateTransport_charpoly heldMatrix,
    Source.heldStateTransport_spectrum heldMatrix, Source.heldStateTransport_injective,
    heldMatrix_norm_le_ten, rawProjection_entry_gap, heldTransport_error_small,
    heldState_transport_not_scfReset, Observer.targetHamiltonian_hermitian,
    Observer.operatorChange_hermitian, Observer.trace_commutes heldMatrix,
    Observer.actual_operator_change heldMatrix⟩

end
end LAlanine40K2025.ElectronicFrame.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
