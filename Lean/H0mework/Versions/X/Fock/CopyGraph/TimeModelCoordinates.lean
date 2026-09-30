import H0mework.Versions.X.Fock.CopyGraph.TimeModelPacket

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyTimeModel

open SourceCopyProgram (Index scale indexAfter)
open SourceOwnedObservationHistory.SourceShift (H basis)
open scoped Classical InnerProductSpace
noncomputable section

theorem action_coordinate (depth : Nat) (index : Index depth) (value : H) (coordinate : Nat) :
    SourceCopyGraph.hilbertAction depth index value (indexAfter depth index coordinate) = value coordinate := by
  have source := congrArg (fun point : H => point coordinate)
    (IsometricRetainedTransfer.transfer_pullback (SourceCopyGraph.hilbertAction depth index) value)
  change SourceCopyGraph.hilbertRecover depth index (SourceCopyGraph.hilbertAction depth index value) coordinate = _ at source
  rw [SourceCopyGraph.recover_coordinate] at source
  exact source

theorem action_outside (depth : Nat) (index : Index depth) (value : H) (coordinate : Nat)
    (outside : coordinate ∉ Set.range (indexAfter depth index)) : SourceCopyGraph.hilbertAction depth index value coordinate = 0 := by
  have hidden : SourceCopyGraph.hilbertRecover depth index (basis coordinate) = 0 := by
    apply lp.ext
    funext source
    rw [SourceCopyGraph.recover_coordinate]
    have different : indexAfter depth index source ≠ coordinate := fun same => outside ⟨source, same⟩
    simp [basis, lp.single_apply, different]
  have pairing := (SourceCopyGraph.hilbertAction depth index).toContinuousLinearMap.adjoint_inner_left value (basis coordinate)
  change inner ℂ (SourceCopyGraph.hilbertRecover depth index (basis coordinate)) value =
    inner ℂ (basis coordinate) (SourceCopyGraph.hilbertAction depth index value) at pairing
  rw [hidden, inner_zero_left] at pairing
  simpa only [basis, lp.inner_single_left, RCLike.inner_apply, map_one, mul_one] using pairing.symm

theorem projected_coordinate (depth : Nat) (index : Index depth) (value : SourceJointClockGraph.Carrier) (coordinate : Nat) :
    hilbert (SourceCopyGraph.action depth index (SourceCopyGraph.recover depth index value)) coordinate =
      if coordinate ∈ Set.range (indexAfter depth index) then hilbert value coordinate else 0 := by
  change SourceCopyGraph.hilbertAction depth index (SourceCopyGraph.hilbertRecover depth index (hilbert value)) coordinate = _
  by_cases present : coordinate ∈ Set.range (indexAfter depth index)
  · rw [if_pos present]
    rcases present with ⟨source, rfl⟩
    rw [action_coordinate, SourceCopyGraph.recover_coordinate]
  · rw [if_neg present]
    exact action_outside depth index _ coordinate present

open Fin.NatCast

def phaseAt (depth : Nat) (index : Index depth) (coordinate : Nat) : Fin (index.val + 1) :=
  -(↑(coordinate + 1) : Fin (index.val + 1))

theorem phase_range (depth : Nat) (index : Index depth) (coordinate : Nat) (phase : Fin (index.val + 1)) :
    coordinate + phase.val ∈ Set.range (indexAfter depth index) ↔ phase = phaseAt depth index coordinate := by
  rw [SourceCopyProgram.index_range, SourceCopyProgram.scale_source, ← Fin.natCast_eq_zero]
  have source : (↑(coordinate + phase.val + 1) : Fin (index.val + 1)) =
      (↑(coordinate + 1) : Fin (index.val + 1)) + phase := by
    simp only [Nat.cast_add, Fin.cast_val_eq_self]
    abel
  rw [source, add_comm (↑(coordinate + 1) : Fin (index.val + 1)) phase]
  exact add_eq_zero_iff_eq_neg

end
end SourceCopyTimeModel
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
