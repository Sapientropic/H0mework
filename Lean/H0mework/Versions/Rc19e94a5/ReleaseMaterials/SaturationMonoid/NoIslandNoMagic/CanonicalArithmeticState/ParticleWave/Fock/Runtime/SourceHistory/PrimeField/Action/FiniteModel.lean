import H0mework.Versions.Rc19e94a5.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.SourceHistory.PrimeField.Action.Saturation

/-! The source-generated finite window reads and recovers the original
single-prime future Model on its exact realizable image. Its action is the
restriction of the original Model action, not a submitted target dynamics. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeActionSaturation

open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open SourcePrimeHistoryRecovery SourcePrimeCompletion
open SourceGeneratedActionObservationHistory SourceGeneratedScalarDifferentialResidual

noncomputable section

def modelWindowRead (prime : Nat.Primes) : Model nativeAction (originalRead prime) →ₗ[ℤ]
    PrefixCarrier ℤ (cut prime) :=
  (LinearMap.ker (sourceMap nativeAction (originalRead prime))).liftQ
    (prefixEvaluator nativeAction (originalRead prime) (cut prime))
    (finite_prefix_kernel_eq_full prime).ge

theorem modelWindowRead_source (prime : Nat.Primes) (word : SourceOperationNative.Carrier process) :
    modelWindowRead prime (projection nativeAction (originalRead prime) word) =
      prefixEvaluator nativeAction (originalRead prime) (cut prime) word := rfl

theorem modelWindowRead_injective (prime : Nat.Primes) : Function.Injective (modelWindowRead prime) := by
  intro left right same
  obtain ⟨leftWord, rfl⟩ := Submodule.mkQ_surjective (LinearMap.ker (sourceMap nativeAction (originalRead prime))) left
  obtain ⟨rightWord, rfl⟩ := Submodule.mkQ_surjective (LinearMap.ker (sourceMap nativeAction (originalRead prime))) right
  exact (finite_prefix_fibre_iff_model prime leftWord rightWord).mp same

theorem model_window_action (prime : Nat.Primes) :
    (modelWindowRead prime).comp (modelAction nativeAction (originalRead prime)) =
      (FiniteRecurrence.advance (cut prime) (coefficients prime)).comp (modelWindowRead prime) := by
  apply LinearMap.ext
  intro model
  obtain ⟨word, rfl⟩ := Submodule.mkQ_surjective (LinearMap.ker (sourceMap nativeAction (originalRead prime))) model
  change modelWindowRead prime (modelAction nativeAction (originalRead prime)
    (projection nativeAction (originalRead prime) word)) = _
  rw [modelAction_source, modelWindowRead_source]
  exact (LinearMap.congr_fun (finite_prefix_action prime) word).symm

def recoverWindow (prime : Nat.Primes) :
    LinearMap.range (prefixEvaluator nativeAction (originalRead prime) (cut prime)) →ₗ[ℤ]
      Model nativeAction (originalRead prime) :=
  ((LinearMap.ker (prefixEvaluator nativeAction (originalRead prime) (cut prime))).liftQ
    (projection nativeAction (originalRead prime)) (by
      intro word invisible
      exact (canonicalResidual_eq_zero_iff (sourceMap nativeAction (originalRead prime)) word).mpr
        ((finite_prefix_kernel_eq_full prime).le invisible))).comp
    (residualEquivRange (prefixEvaluator nativeAction (originalRead prime) (cut prime))).symm.toLinearMap

theorem recoverWindow_source (prime : Nat.Primes) (word : SourceOperationNative.Carrier process) :
    recoverWindow prime (rangeMap (prefixEvaluator nativeAction (originalRead prime) (cut prime)) word) =
      projection nativeAction (originalRead prime) word := by
  unfold recoverWindow
  rw [LinearMap.comp_apply]
  change (LinearMap.ker (prefixEvaluator nativeAction (originalRead prime) (cut prime))).liftQ _ _
    ((residualEquivRange (prefixEvaluator nativeAction (originalRead prime) (cut prime))).symm
      ((residualEquivRange (prefixEvaluator nativeAction (originalRead prime) (cut prime)))
        (canonicalResidual (prefixEvaluator nativeAction (originalRead prime) (cut prime)) word))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

def modelWindowValue (prime : Nat.Primes) : Model nativeAction (originalRead prime) →ₗ[ℤ]
    LinearMap.range (prefixEvaluator nativeAction (originalRead prime) (cut prime)) :=
  (modelWindowRead prime).codRestrict _ (by
    intro model
    obtain ⟨word, rfl⟩ := Submodule.mkQ_surjective (LinearMap.ker (sourceMap nativeAction (originalRead prime))) model
    exact ⟨word, rfl⟩)

theorem recoverWindow_modelWindowValue (prime : Nat.Primes)
    (model : Model nativeAction (originalRead prime)) :
    recoverWindow prime (modelWindowValue prime model) = model := by
  obtain ⟨word, rfl⟩ := Submodule.mkQ_surjective (LinearMap.ker (sourceMap nativeAction (originalRead prime))) model
  exact recoverWindow_source prime word

end
end SourcePrimeActionSaturation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
