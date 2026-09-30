import H0mework.Fock.SourceHistoryClock.BinomialCore

/-! The same generic model extracts the earlier moments from the generated divided-power action. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceBinomialClock

open SourceSuccessorBoundary

noncomputable section

abbrev Model := SourceGeneratedActionObservationHistory.Model SourceClockModel.nativeAction second
abbrev projection : (Nat →₀ ℤ) →ₗ[ℤ] Model :=
  SourceGeneratedActionObservationHistory.projection SourceClockModel.nativeAction second
abbrev action : Model →ₗ[ℤ] Model :=
  SourceGeneratedActionObservationHistory.modelAction SourceClockModel.nativeAction second
abbrev secondRead : Model →ₗ[ℤ] ℤ :=
  SourceGeneratedActionObservationHistory.modelReadout SourceClockModel.nativeAction second

def clockRead : Model →ₗ[ℤ] ℤ := secondRead.comp action - secondRead
def massRead : Model →ₗ[ℤ] ℤ := clockRead.comp action - clockRead
def squareRead : Model →ₗ[ℤ] ℤ := (2 : ℤ) • secondRead - clockRead + massRead

theorem secondRead_source (word : Nat →₀ ℤ) : secondRead (projection word) = second word :=
  SourceGeneratedActionObservationHistory.modelReadout_projection SourceClockModel.nativeAction second word

theorem action_source (word : Nat →₀ ℤ) : action (projection word) = projection (push ℤ word) := by
  have source := SourceGeneratedActionObservationHistory.modelAction_source SourceClockModel.nativeAction second word
  exact source.trans (congrArg projection (show SourceClockModel.nativeAction word = push ℤ word from rfl))

theorem clockRead_source (word : Nat →₀ ℤ) : clockRead (projection word) = SourceClockModel.clock word := by
  change secondRead (action (projection word)) - secondRead (projection word) = _
  rw [action_source, secondRead_source, secondRead_source, second_push, add_sub_cancel_left]

theorem massRead_source (word : Nat →₀ ℤ) : massRead (projection word) = mass ℤ word := by
  change clockRead (action (projection word)) - clockRead (projection word) = _
  rw [action_source, clockRead_source, clockRead_source, SourceClockModel.clock_push, add_sub_cancel_left]

theorem secondRead_action (value : Model) : secondRead (action value) = secondRead value + clockRead value := by
  change secondRead (action value) = secondRead value + (secondRead (action value) - secondRead value)
  abel

theorem clockRead_action (value : Model) : clockRead (action value) = clockRead value + massRead value := by
  change clockRead (action value) = clockRead value + (clockRead (action value) - clockRead value)
  abel

theorem massRead_action (value : Model) : massRead (action value) = massRead value := by
  refine Submodule.Quotient.induction_on _ value fun word => ?_
  change massRead (action (projection word)) = massRead (projection word)
  rw [action_source, massRead_source, massRead_source, mass_push]

theorem squareRead_source (word : Nat →₀ ℤ) :
    squareRead (projection word) = SourceOperationNative.observer
      NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime.process (fun state : Nat => (state : ℤ) ^ 2) word := by
  have sourceLaw : (2 : ℤ) • second - SourceClockModel.clock + mass ℤ =
      SourceOperationNative.observer NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime.process
        (fun state : Nat => (state : ℤ) ^ 2) := by
    apply Finsupp.lhom_ext
    intro state scalar
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, second_single,
      SourceClockModel.clock_single, mass_single, smul_eq_mul]
    simp only [SourceOperationNative.observer, Finsupp.linearCombination_single, smul_eq_mul]
    rw [source_square]
    simp only [SourceClockModel.rawClock]
    ring
  change 2 * secondRead (projection word) - clockRead (projection word) + massRead (projection word) = _
  rw [secondRead_source, clockRead_source, massRead_source]
  exact LinearMap.congr_fun sourceLaw word

end
end SourceBinomialClock
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
