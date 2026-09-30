import H0mework.Probability.EmpiricalRecovery.FiniteError
import H0mework.Fock.SourceHistoryClock.BinomialPrefixConsumer
import H0mework.Fock.HistoryClock.RecoveryInstalled

/-! The original Pascal and pulse sources pay their own finite observation recurrence laws. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceFiniteObservation

open SourceGeneratedActionObservationHistory SourceBinomialClock SourceSuccessorBoundary
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open SourceGeneratedEmpiricalHilbert.Controls

noncomputable section

def coefficients : Fin 3 → ℤ := ![1, -3, 3]

theorem binomial_source_law : second.comp (SourceClockModel.nativeAction ^ (2 + 1)) =
    ∑ index : Fin 3, coefficients index • stageEvaluator SourceClockModel.nativeAction second index.val := by
  apply LinearMap.ext
  intro word
  simp only [LinearMap.comp_apply, Fin.sum_univ_three]
  change second (push ℤ (push ℤ (push ℤ word))) =
    1 * second word + (-3) * second (push ℤ word) + 3 * second (push ℤ (push ℤ word))
  simp only [second_push, SourceClockModel.clock_push, mass_push]
  ring

theorem pulse_source_law :
    (SourceOperationNative.observer process pulse).comp (SourceOperationNative.sourceAction process ^ (0 + 1)) =
      ∑ index : Fin 1, (0 : ℤ) •
        stageEvaluator (SourceOperationNative.sourceAction process) (SourceOperationNative.observer process pulse) index.val := by
  simp only [zero_smul, Finset.sum_const_zero]
  rw [show SourceOperationNative.sourceAction process ^ (0 + 1) = SourceOperationNative.sourceAction process from pow_one _]
  rw [SourceOperationNative.observer_sourceAction]
  apply Finsupp.lhom_ext
  intro state scalar
  change SourceOperationNative.observer process (fun value => pulse (value + 1)) (Finsupp.single state scalar) = 0
  simp [SourceOperationNative.observer, pulse]

private theorem hidden_read (steps : Nat) :
    second ((SourceClockModel.nativeAction ^ steps) Prefix.hiddenWord) = secondRead ((action ^ steps) Prefix.hidden) := by
  rw [Prefix.hidden_is_source, Prefix.iterate_source, secondRead_source]

theorem no_two_read_source_law :
    ¬ ∃ weights : Fin 2 → ℤ, second.comp (SourceClockModel.nativeAction ^ (1 + 1)) =
      ∑ index : Fin 2, weights index • stageEvaluator SourceClockModel.nativeAction second index.val := by
  rintro ⟨weights, sourceLaw⟩
  have falseLaw := LinearMap.congr_fun sourceLaw Prefix.hiddenWord
  simp only [LinearMap.comp_apply, Fin.sum_univ_two] at falseLaw
  change second ((SourceClockModel.nativeAction ^ 2) Prefix.hiddenWord) =
    weights 0 * second ((SourceClockModel.nativeAction ^ 0) Prefix.hiddenWord) +
      weights 1 * second ((SourceClockModel.nativeAction ^ 1) Prefix.hiddenWord) at falseLaw
  rw [hidden_read, hidden_read, hidden_read] at falseLaw
  change secondRead (action (action Prefix.hidden)) =
    weights 0 * secondRead Prefix.hidden + weights 1 * secondRead (action Prefix.hidden) at falseLaw
  simp only [secondRead_action, clockRead_action, Prefix.hidden_moments.1,
    Prefix.hidden_moments.2.1, Prefix.hidden_moments.2.2] at falseLaw
  norm_num at falseLaw

end
end SourceFiniteObservation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
