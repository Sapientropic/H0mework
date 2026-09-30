import H0mework.Fock.SourceHistoryClock.Core

/-! The existing one-clock model recovers mass from its own generated next observation. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceClockModel

open SourceSuccessorBoundary

noncomputable section

abbrev nativeAction := SourceOperationNative.sourceAction
  NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime.process

abbrev Model := SourceGeneratedActionObservationHistory.Model nativeAction clock

abbrev projection : (Nat →₀ ℤ) →ₗ[ℤ] Model :=
  SourceGeneratedActionObservationHistory.projection nativeAction clock

abbrev action : Model →ₗ[ℤ] Model :=
  SourceGeneratedActionObservationHistory.modelAction nativeAction clock

abbrev clockRead : Model →ₗ[ℤ] ℤ :=
  SourceGeneratedActionObservationHistory.modelReadout nativeAction clock

def massRead : Model →ₗ[ℤ] ℤ := clockRead.comp action - clockRead

theorem clockRead_source (word : Nat →₀ ℤ) : clockRead (projection word) = clock word :=
  SourceGeneratedActionObservationHistory.modelReadout_projection nativeAction clock word

theorem action_source (word : Nat →₀ ℤ) : action (projection word) = projection (push ℤ word) := by
  have generated := SourceGeneratedActionObservationHistory.modelAction_source nativeAction clock word
  exact generated.trans (congrArg projection (show nativeAction word = push ℤ word from rfl))

theorem massRead_source (word : Nat →₀ ℤ) : massRead (projection word) = mass ℤ word := by
  change clockRead (action (projection word)) - clockRead (projection word) = mass ℤ word
  rw [action_source, clockRead_source, clockRead_source, clock_push, add_sub_cancel_left]

theorem massRead_action (value : Model) : massRead (action value) = massRead value := by
  refine Submodule.Quotient.induction_on _ value fun word => ?_
  change massRead (action (projection word)) = massRead (projection word)
  rw [action_source, massRead_source, massRead_source, mass_push]

theorem clockRead_action (value : Model) :
    clockRead (action value) = clockRead value + massRead value := by
  change clockRead (action value) = clockRead value + (clockRead (action value) - clockRead value)
  abel

theorem projection_fibre_iff (left right : Nat →₀ ℤ) :
    projection left = projection right ↔ mass ℤ left = mass ℤ right ∧ clock left = clock right := by
  rw [SourceGeneratedActionObservationHistory.model_fibre_iff]
  change (∀ stage : Nat, clock ((push ℤ ^ stage) left) = clock ((push ℤ ^ stage) right)) ↔ _
  constructor
  · intro future
    have first : clock left = clock right := by
      simpa only [pow_zero, Module.End.one_apply] using future 0
    have next : clock left + mass ℤ left = clock right + mass ℤ right := by
      simpa only [pow_one, clock_push] using future 1
    rw [first] at next
    exact ⟨add_left_cancel next, first⟩
  · rintro ⟨sameMass, sameClock⟩ stage
    rw [clock_pow, clock_pow, sameMass, sameClock]

theorem model_ext_iff (left right : Model) :
    left = right ↔ massRead left = massRead right ∧ clockRead left = clockRead right := by
  refine Submodule.Quotient.induction_on _ left fun leftWord => ?_
  refine Submodule.Quotient.induction_on _ right fun rightWord => ?_
  change projection leftWord = projection rightWord ↔
    massRead (projection leftWord) = massRead (projection rightWord) ∧
      clockRead (projection leftWord) = clockRead (projection rightWord)
  rw [massRead_source, massRead_source, clockRead_source, clockRead_source]
  exact projection_fibre_iff leftWord rightWord

end
end SourceClockModel
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
