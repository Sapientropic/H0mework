import H0mework.Versions.X.Fock.CopyGraph.Action
import H0mework.Versions.X.Fock.HistoryPolynomial.CopyRecovery

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyGraph

open SourceCopyProgram SourceSuccessorBoundary SourceOwnedObservationHistory.SourceShift
open scoped InnerProductSpace
noncomputable section

abbrev hilbertRecover (depth : Nat) (index : Index depth) := IsometricRetainedTransfer.transfer (hilbertAction depth index)
abbrev hilbertResidual (depth : Nat) (index : Index depth) := IsometricRetainedTransfer.residual (hilbertAction depth index)

theorem recover_coordinate (depth : Nat) (index : Index depth) (value : H) (coordinate : Nat) :
    hilbertRecover depth index value coordinate = value (indexAfter depth index coordinate) := by
  have same : ⟪lp.single 2 coordinate (1 : ℂ), hilbertRecover depth index value⟫_ℂ =
      ⟪lp.single 2 (indexAfter depth index coordinate) (1 : ℂ), value⟫_ℂ := by
    change ⟪lp.single 2 coordinate (1 : ℂ), (hilbertAction depth index).toContinuousLinearMap.adjoint value⟫_ℂ = _
    rw [ContinuousLinearMap.adjoint_inner_right]
    change ⟪hilbertAction depth index (lp.single 2 coordinate (1 : ℂ)), value⟫_ℂ = _
    exact congrArg (fun point : H => inner ℂ point value) (hilbert_single depth index coordinate 1)
  rw [lp.inner_single_left, lp.inner_single_left] at same
  simpa using same

theorem native_hilbert (word : Nat →₀ ℤ) : readWord (SourceClockComplex.ofNative word) = wordRead word :=
  (SourceMassCompletion.firstRead_source (SourceClockComplex.ofNative word)).symm.trans
    ((congrArg SourceMassCompletion.firstRead (SourceClockComplex.joint_native word)).trans
      (SourceMassCompletion.firstRead_native word))

theorem recover_native_source (depth : Nat) (index : Index depth) (word : Nat →₀ ℤ) :
    hilbertRecover depth index (readWord (SourceClockComplex.ofNative word)) =
      readWord (SourceClockComplex.ofNative (SourceCopyProgram.recover depth index word)) := by
  ext coordinate
  rw [recover_coordinate, native_hilbert, native_hilbert, wordRead_coordinate, wordRead_coordinate,
    SourceCopyProgram.recovery_reads]

end
end SourceCopyGraph
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
