import H0mework.Fock.HistoryPolynomial.Presentation
import H0mework.Fock.PrimeFieldCalculation.FixedConsumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCyclicModule

open SourcePrimeHistoryRecovery SourceGeneratedActionObservationHistory
open SourceGeneratedAcquisitionContinuation SourceGeneratedAcquisitionJoint
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open Polynomial
noncomputable section

theorem native_program (runtime : LivingRuntimeState process) :
    program (X ^ runtime.state) = SourceOperationNative.point runtime := by
  rw [← monomial_one_right_eq_X_pow, program_monomial]
  rfl

theorem native_program_next (runtime : LivingRuntimeState process) :
    program (X * X ^ runtime.state) = SourceOperationNative.point runtime.tick.next := by
  rw [program_X_mul, native_program]
  exact SourceOperationNative.sourceAction_point runtime

theorem native_observation (runtime : LivingRuntimeState process) :
    observation (program (X ^ runtime.state)) = rawField runtime.state := by
  rw [native_program]
  exact SourceOperationNative.observer_point (process := process) rawField runtime

def ProgramAt (round : Nat) (polynomial : Polynomial ℤ) : Prop :=
    let word := SourceClockComplex.ofNative (program polynomial)
    type_of% (realization_word round word) ∧
      type_of% (source_round_after round word) ∧
      type_of% (SourceGeneratedJointClockGraph.native_realization_graph round (program polynomial)) ∧
      (∀ future : Nat, ∀ reached : demand round word ≤ future,
        type_of% (SourceGeneratedJointDecoderCofinal.original_word_exact round word future reached)) ∧
      type_of% (coversAt_factorizes (sourceRound round word) .particleWave) ∧
      type_of% (coversAt_factorizes (sourceRound round word).tick.next .particleWave)

theorem original_program_consumed (round : Nat) (polynomial : Polynomial ℤ) : ProgramAt round polynomial := by
  dsimp only [ProgramAt]
  exact ⟨realization_word round _, source_round_after round _,
    SourceGeneratedJointClockGraph.native_realization_graph round (program polynomial),
    SourceGeneratedJointDecoderCofinal.original_word_exact round _,
    coversAt_factorizes (sourceRound round _) .particleWave,
    coversAt_factorizes (sourceRound round _).tick.next .particleWave⟩

end
end SourceCyclicModule
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
