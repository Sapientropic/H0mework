import H0mework.Fock.PrimeField.RecoveryPoint
import H0mework.Realization.Operations.ObservationNative

/-! The actual native action turns the two prime reads into each coefficient of a complete source word. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeHistoryRecovery

open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime
open SourceGeneratedActionObservationHistory

noncomputable section

abbrev nativeAction := SourceOperationNative.sourceAction process
abbrev observation := SourceOperationNative.observer process rawField

theorem source_iterate (state steps : Nat) :
    (nativeAction ^ steps) (SourceOperationNative.statePoint process state) =
      SourceOperationNative.statePoint process (state + steps) := by
  induction steps with
  | zero => rfl
  | succ steps previous =>
      rw [pow_succ']
      change nativeAction ((nativeAction ^ steps) (SourceOperationNative.statePoint process state)) = _
      rw [previous]
      exact SourceOperationNative.sourceAction_statePoint process (state + steps)

def selector (owner : GlobalParentOwner) (index : Nat) : SourceOperationNative.Carrier process →ₗ[ℤ] ℤ :=
  (primeRead (selectedPrime owner index)).comp
    (stageEvaluator nativeAction observation (delay owner index + 1) - stageEvaluator nativeAction observation (delay owner index))

theorem selector_point (owner : GlobalParentOwner) (index state : Nat) :
    selector owner index (SourceOperationNative.statePoint process state) = if state = index then 1 else 0 := by
  change primeRead (selectedPrime owner index)
    (observation ((nativeAction ^ (delay owner index + 1)) (SourceOperationNative.statePoint process state)) -
      observation ((nativeAction ^ delay owner index) (SourceOperationNative.statePoint process state))) = _
  rw [map_sub, source_iterate, source_iterate, SourceOperationNative.observer_statePoint, SourceOperationNative.observer_statePoint]
  exact point_separation owner index state

theorem selector_is_coefficient (owner : GlobalParentOwner) (index : Nat) :
    selector owner index = Finsupp.lapply (R := ℤ) (M := ℤ) index := by
  apply Finsupp.lhom_ext'
  intro state
  apply LinearMap.ext_ring
  change selector owner index (SourceOperationNative.statePoint process state) =
    (SourceOperationNative.statePoint process state) index
  rw [selector_point]
  simp only [SourceOperationNative.statePoint, Finsupp.single_apply]

theorem recovers_source_word (owner : GlobalParentOwner) (index : Nat) (word : SourceOperationNative.Carrier process) :
    selector owner index word = word index := LinearMap.congr_fun (selector_is_coefficient owner index) word

end
end SourcePrimeHistoryRecovery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
