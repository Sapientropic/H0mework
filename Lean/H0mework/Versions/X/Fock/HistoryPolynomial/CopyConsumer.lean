import H0mework.Versions.X.Fock.HistoryPolynomial.CopyNative

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyProgram

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceGeneratedActionWords SourcePrimeHistoryRecovery SourceCyclicModule
open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def ResidualAt (round : Nat) (index : Index (sourceDepth round)) (target : SourceOperationNative.Carrier process) : Prop :=
    let depth := sourceDepth round
    type_of% (actual_field_reconstruction depth index target) ∧
      type_of% (complete_reconstruction depth index target) ∧
      type_of% (exact_image depth index target) ∧
      (∀ coordinate : Nat, type_of% (prime_residual_reads depth index target coordinate)) ∧
      type_of% (residual_program depth index target) ∧
      type_of% (original_program_consumed round (coefficients.symm (residual depth index target))) ∧
      type_of% (complete_previous depth (residual depth index target))

theorem original_residual_consumed (round : Nat) (index : Index (sourceDepth round))
    (target : SourceOperationNative.Carrier process) : ResidualAt round index target := by
  dsimp only [ResidualAt]
  exact ⟨actual_field_reconstruction _ index target, complete_reconstruction _ index target,
    exact_image _ index target, prime_residual_reads _ index target, residual_program _ index target,
    original_program_consumed round (coefficients.symm (residual _ index target)),
    complete_previous _ (residual _ index target)⟩

def RecoveryAt (round : Nat) : Prop :=
    let depth := sourceDepth round
    type_of% (copy_current round) ∧
      (∀ index : Index depth,
        type_of% (scale_source depth index) ∧ type_of% (material_program depth index) ∧
        type_of% (copy_written_program depth index) ∧
        (∀ p : Polynomial ℤ, CopyAt round index p ∧ type_of% (polynomial_native_action depth index p) ∧
          type_of% (old_material_program depth index p)) ∧
        (∀ target : SourceOperationNative.Carrier process, ResidualAt round index target) ∧
        (∀ nonunit : index.val ≠ 0, type_of% (actual_field_root_residual depth index nonunit))) ∧
      (∀ word : List (Fock.Letter depth), ∀ source : SourceOperationNative.Carrier process,
        type_of% (complete_word depth word source)) ∧
      type_of% (coversAt_factorizes (roundRuntime round) .particleWave) ∧
      type_of% (coversAt_factorizes (roundRuntime round).tick.next .particleWave) ∧
      type_of% (sourceGeneratedCyclicModuleRecovery round)

theorem sourceGeneratedCopyRecovery (round : Nat) : RecoveryAt round := by
  dsimp only [RecoveryAt]
  exact ⟨copy_current round,
    (fun index => ⟨scale_source _ index, material_program _ index, copy_written_program _ index,
      (fun p => ⟨original_copy_consumed round index p, polynomial_native_action _ index p, old_material_program _ index p⟩),
      original_residual_consumed round index, actual_field_root_residual _ index⟩),
    complete_word _, coversAt_factorizes (roundRuntime round) .particleWave,
    coversAt_factorizes (roundRuntime round).tick.next .particleWave, sourceGeneratedCyclicModuleRecovery round⟩

end
end SourceCopyProgram
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
