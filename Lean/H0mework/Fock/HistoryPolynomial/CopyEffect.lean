import H0mework.Fock.HistoryPolynomial.CopyRecovery
import H0mework.Fock.HistoryPolynomial.CopyModel
import H0mework.Fock.PrimeField.RecoveryMaterial

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyProgram

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceGeneratedActionWords SourcePrimeHistoryRecovery SourceCyclicModule
open NoIslandNoMagic.CanonicalArithmeticState NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open ArithmeticGeneration
noncomputable section

theorem whole_injective : Function.Injective whole := by
  rw [whole_is_source]
  apply Finsupp.mapDomain_injective
  intro left right same
  have generated := (finiteVisit_current left).symm.trans (same.trans (finiteVisit_current right))
  have counts := congrArg UnitHistory.cardinalShadow generated
  rw [UnitHistory.cardinalShadow_generate, UnitHistory.cardinalShadow_generate] at counts
  exact Nat.succ.inj counts

theorem rebase_injective (step : Current → Current) :
    Function.Injective (fun word => FullMap.map nativeStep step id (FullProjection.Fock.bridge word)) := by
  intro left right same
  have words := congrArg (FullWord.word step) same
  rw [FullMap.map_word, FullMap.map_word, Finsupp.lmapDomain_id, LinearMap.id_apply, LinearMap.id_apply] at words
  exact whole_injective words

theorem actual_field_fibre (depth : Nat) (index : Index depth)
    (target proposal : SourceOperationNative.Carrier process) :
    FullMap.map nativeStep (NativeCopy.copyStep (NativeCopy.Fock.material depth index))
        (NativeCopy.copy (NativeCopy.Fock.material depth index)) (FullProjection.Fock.bridge proposal) =
      FullMap.map nativeStep (NativeCopy.copyStep (NativeCopy.Fock.material depth index)) id
        (FullProjection.Fock.bridge target) ↔
      proposal = recover depth index target ∧ residual depth index target = 0 := by
  rw [original_field_action, (rebase_injective _).eq_iff]
  exact original_fibre depth index target proposal

theorem actual_field_reconstruction (depth : Nat) (index : Index depth)
    (target : SourceOperationNative.Carrier process) :
    FullMap.map nativeStep (NativeCopy.copyStep (NativeCopy.Fock.material depth index))
        (NativeCopy.copy (NativeCopy.Fock.material depth index)) (FullProjection.Fock.bridge (recover depth index target)) +
      FullMap.map nativeStep (NativeCopy.copyStep (NativeCopy.Fock.material depth index)) id
        (FullProjection.Fock.bridge (residual depth index target)) =
      FullMap.map nativeStep (NativeCopy.copyStep (NativeCopy.Fock.material depth index)) id
        (FullProjection.Fock.bridge target) := by
  rw [original_field_action, ← map_add, ← map_add, reconstruct]

theorem complete_reconstruction (depth : Nat) (index : Index depth)
    (target : SourceOperationNative.Carrier process) :
    Fock.Complete.action depth (.inr index) (complete depth (recover depth index target)) +
        complete depth (residual depth index target) = complete depth target := by
  have source := complete_word depth [.inr index] (recover depth index target)
  change Fock.Complete.action depth (.inr index) (complete depth (recover depth index target)) =
    complete depth (action depth index (recover depth index target)) at source
  rw [source, ← map_add, reconstruct]

theorem prime_copy_recovers (depth : Nat) (index : Index depth) (p : Polynomial ℤ) (coordinate : Nat) :
    selector sourceOwner (indexAfter depth index coordinate) (program (polynomial depth index p)) = p.coeff coordinate := by
  rw [recovers_source_word, polynomial_source, action_coefficient, program_coefficient]

theorem prime_residual_reads (depth : Nat) (index : Index depth)
    (target : SourceOperationNative.Carrier process) (coordinate : Nat) :
    selector sourceOwner coordinate (residual depth index target) =
      if scale depth index ∣ coordinate + 1 then 0 else target coordinate := by
  rw [recovers_source_word]
  split_ifs with inside
  · obtain ⟨prior, rfl⟩ := (index_range depth index coordinate).mpr inside
    exact residual_inside depth index target prior
  · exact residual_outside depth index target coordinate
      (fun member => inside ((index_range depth index coordinate).mp member))

theorem nonunit_root_outside (depth : Nat) (index : Index depth) (nonunit : index.val ≠ 0) :
    0 ∉ Set.range (indexAfter depth index) := by
  intro inside
  have divides := (index_range depth index 0).mp inside
  have scaleOne := Nat.eq_one_of_dvd_one divides
  rw [scale_source] at scaleOne
  omega

theorem nonunit_root_residual (depth : Nat) (index : Index depth) (nonunit : index.val ≠ 0) :
    residual depth index (program 1) = program 1 := by
  have recovered : recover depth index (program 1) = 0 := by
    apply Finsupp.ext
    intro coordinate
    rw [recovery_reads, program_one, original_root]
    change Finsupp.single 0 (1 : ℤ) (indexAfter depth index coordinate) = 0
    exact Finsupp.single_eq_of_ne (fun same => nonunit_root_outside depth index nonunit ⟨coordinate, same⟩)
  change program 1 - action depth index (recover depth index (program 1)) = program 1
  rw [recovered, map_zero, sub_zero]

theorem no_free_root_preimage (depth : Nat) (index : Index depth) (nonunit : index.val ≠ 0) :
    ¬ ∃ proposal : SourceOperationNative.Carrier process, action depth index proposal = program 1 := by
  rintro ⟨proposal, same⟩
  have vanished := (original_fibre depth index (program 1) proposal).mp same |>.2
  rw [nonunit_root_residual depth index nonunit, program_one, original_root] at vanished
  exact one_ne_zero (Finsupp.single_eq_zero.mp vanished)

theorem actual_field_root_residual (depth : Nat) (index : Index depth) (nonunit : index.val ≠ 0) :
    ¬ ∃ proposal : SourceOperationNative.Carrier process,
      FullMap.map nativeStep (NativeCopy.copyStep (NativeCopy.Fock.material depth index))
          (NativeCopy.copy (NativeCopy.Fock.material depth index)) (FullProjection.Fock.bridge proposal) =
        FullMap.map nativeStep (NativeCopy.copyStep (NativeCopy.Fock.material depth index)) id
          (FullProjection.Fock.bridge (program 1)) := by
  rintro ⟨proposal, same⟩
  exact no_free_root_preimage depth index nonunit ⟨proposal,
    (original_fibre depth index (program 1) proposal).mpr ((actual_field_fibre depth index _ _).mp same)⟩

end
end SourceCopyProgram
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
