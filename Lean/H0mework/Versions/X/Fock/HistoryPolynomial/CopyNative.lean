import H0mework.Versions.X.Fock.HistoryPolynomial.CopyEffect
import H0mework.Versions.X.Fock.HistoryPolynomial.Consumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyProgram

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceGeneratedActionWords SourcePrimeHistoryRecovery SourceCyclicModule Polynomial
open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem material_program (depth : Nat) (index : Index depth) :
    FullProjection.Fock.bridge (program (X ^ index.val)) =
      fieldPoint nativeStep fullRead (NativeCopy.Fock.material depth index) := by
  have source : program (X ^ index.val) = SourceOperationNative.statePoint process index.val := by
    rw [← monomial_one_right_eq_X_pow, program_monomial]
    rfl
  have material := (window_actor_factorizes depth index).1
  change NativeCopy.Fock.material depth index = (runtimeAt index.val).current.visit.current at material
  have current := material.trans ((runtimeAt_current index.val).trans (finiteVisit_current index.val).symm)
  rw [source, FullProjection.Fock.bridge_statePoint]
  exact congrArg (fieldPoint nativeStep fullRead) current.symm

theorem copy_written_program (depth : Nat) (index : Index depth) :
    FullMap.map nativeStep (NativeCopy.copyStep (NativeCopy.Fock.material depth index))
        (NativeCopy.copy (NativeCopy.Fock.material depth index))
        (FullProjection.Fock.bridge (program (X * X ^ depth))) =
      fieldPoint (NativeCopy.copyStep (NativeCopy.Fock.material depth index)) sourcePoint
        (NativeCopy.copy (NativeCopy.Fock.material depth index) (runtimePayload depth).nativeWrite.target) := by
  have currentProgram := native_program (runtimeAt depth)
  rw [runtimeAt_state] at currentProgram
  have square : FullProjection.Fock.bridge (nativeAction (program (X ^ depth))) =
      fieldAction nativeStep fullRead (FullProjection.Fock.bridge (program (X ^ depth))) :=
    (LinearMap.congr_fun FullProjection.Fock.bridge_action (program (X ^ depth))).symm
  rw [program_X_mul, square, currentProgram, FullProjection.Fock.bridge_point]
  exact NativeCopy.Fock.actual_copy_target depth index

theorem residual_program (depth : Nat) (index : Index depth) (target : SourceOperationNative.Carrier process) :
    program (coefficients.symm (residual depth index target)) = residual depth index target :=
  (program_is_coefficients _).trans (coefficients.apply_symm_apply _)

abbrev sourceDepth (round : Nat) := inventoryBound (roundRuntime round)

theorem copy_current (round : Nat) : runtimeAt (sourceDepth round) = roundRuntime round := by
  change runtimeAt (inventoryBound (roundRuntime round)) = roundRuntime round
  rw [inventory_bound]
  exact (runtime_eq (roundRuntime round)).symm

def CopyAt (round : Nat) (index : Index (sourceDepth round)) (p : Polynomial ℤ) : Prop :=
    let depth := sourceDepth round
    type_of% (polynomial_formula depth index p) ∧
      type_of% (model_copy depth index p) ∧ type_of% (complete_copy depth index p) ∧
      type_of% (actual_field_fibre depth index (program (polynomial depth index p)) (program p)) ∧
      type_of% (recover_source depth index (program p)) ∧
      (∀ coordinate : Nat, type_of% (prime_copy_recovers depth index p coordinate)) ∧
      type_of% (original_program_consumed round (polynomial depth index p)) ∧
      type_of% (NativeCopy.Fock.runtime_copy_factorizes depth index (FullProjection.Fock.bridge (program p)))

theorem original_copy_consumed (round : Nat) (index : Index (sourceDepth round)) (p : Polynomial ℤ) : CopyAt round index p := by
  dsimp only [CopyAt]
  exact ⟨polynomial_formula _ index p, model_copy _ index p, complete_copy _ index p,
    actual_field_fibre _ index _ _, recover_source _ index (program p),
    prime_copy_recovers _ index p, original_program_consumed round (polynomial _ index p),
    NativeCopy.Fock.runtime_copy_factorizes _ index (FullProjection.Fock.bridge (program p))⟩

end
end SourceCopyProgram
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
