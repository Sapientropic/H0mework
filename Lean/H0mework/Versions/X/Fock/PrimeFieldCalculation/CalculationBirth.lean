import H0mework.Versions.X.Fock.PrimeFieldCalculation.CalculationQuery

/-! Each recovery coefficient is the original source-born action at one exact recorded stage. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeCalculation

open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime
open SourcePrimeHistoryRecovery

noncomputable section

def operationCell (bound : Nat) (index actor : Fin (bound + 1)) : Fin (completionDepth sourceOwner bound + 1) :=
  cell sourceOwner bound actor (offset sourceOwner bound index).succ

def birthCoefficient (bound : Nat) (index actor : Fin (bound + 1)) : ℤ :=
  primeRead (selectedPrime sourceOwner (bound + 1))
    (SourceFactorizationAction.Fock.birth (runtimeAt (operationCell bound index actor).val).current.visit.current)

theorem recorded_coefficient_is_birth (bound : Nat) (index actor : Fin (bound + 1)) :
    coefficient sourceOwner bound index (recordedQuery bound actor) = birthCoefficient bound index actor := by
  let step := operationCell bound index actor
  have generated := ((realization bound).operationAt step).2.2.1
  change rawField (step.val + 1) = rawField step.val +
    SourceFactorizationAction.Fock.birth (runtimeAt step.val).current.visit.current at generated
  rw [recorded_is_query]
  change primeRead (selectedPrime sourceOwner (bound + 1))
    (observe sourceOwner bound actor (offset sourceOwner bound index).succ -
      observe sourceOwner bound actor (offset sourceOwner bound index).castSucc) = _
  rw [SourcePrimeHistoryRecovery.query_value, SourcePrimeHistoryRecovery.query_value]
  have before : actor.val + 1 + (offset sourceOwner bound index).castSucc.val = step.val := by
    simp only [step, operationCell, cell, Fin.val_castSucc, Fin.val_succ]
    omega
  have after : actor.val + 1 + (offset sourceOwner bound index).succ.val = step.val + 1 := by
    simp only [step, operationCell, cell, Fin.val_succ]
    omega
  rw [before, after, generated, add_sub_cancel_left]
  rfl

theorem birth_coefficient_is_delta (bound : Nat) (index actor : Fin (bound + 1)) :
    birthCoefficient bound index actor = if actor = index then 1 else 0 := by
  rw [← recorded_coefficient_is_birth, recorded_is_query, coefficient_query]

def sourceAnswer (bound : Nat) (task : Fin (bound + 1) → ℂ) (actor : Fin (bound + 1)) : ℂ :=
  ∑ index : Fin (bound + 1), (birthCoefficient bound index actor : ℂ) * task index

theorem source_answer_is_recorded (bound : Nat) (task : Fin (bound + 1) → ℂ) (actor : Fin (bound + 1)) :
    sourceAnswer bound task actor = decoder sourceOwner bound task (recordedQuery bound actor) := by
  unfold sourceAnswer decoder
  apply Finset.sum_congr rfl
  intro index _
  rw [recorded_coefficient_is_birth]

theorem source_answer_recovers (bound : Nat) (task : Fin (bound + 1) → ℂ) (actor : Fin (bound + 1)) :
    sourceAnswer bound task actor = task actor :=
  (source_answer_is_recorded bound task actor).trans (recorded_recovers bound task actor)

end
end SourcePrimeCalculation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
