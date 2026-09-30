import H0mework.Fock.PrimeField.RecoveryWindow

/-! Every delayed prime read retains its original material stage and exact native next. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeHistoryRecovery

open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime
open SourceGeneratedActionObservationHistory SourceGeneratedRuntimeHistoryProbability

noncomputable section

def sourceOwner : GlobalParentOwner := liveGlobalOwner (runtimeAt 0).current.visit.current

def completionDepth (owner : GlobalParentOwner) (bound : Nat) : Nat := bound + windowBound owner bound

def cell (owner : GlobalParentOwner) (bound : Nat) (actor : Fin (bound + 1))
    (time : Fin (windowBound owner bound + 1)) : Fin (completionDepth owner bound + 1) :=
  ⟨actor.val + time.val, by unfold completionDepth; omega⟩

theorem query_is_material (owner : GlobalParentOwner) (bound : Nat) (actor : Fin (bound + 1))
    (time : Fin (windowBound owner bound + 1)) :
    observe owner bound actor time = rawField
      (((history runtimeSeed (completionDepth owner bound)).stageAt (cell owner bound actor time)).next.state) := by
  rw [query_value]
  change rawField (actor.val + 1 + time.val) = rawField (runtimeAt (actor.val + time.val + 1)).state
  rw [runtimeAt_state]
  congr 1
  omega

theorem query_material_factorizes (owner : GlobalParentOwner) (bound : Nat) (actor : Fin (bound + 1))
    (time : Fin (windowBound owner bound + 1)) :
    let stage := (history runtimeSeed (completionDepth owner bound)).stageAt (cell owner bound actor time)
    observe owner bound actor time = rawField stage.next.state ∧
      type_of% (sample_factorizes runtimeSeed (completionDepth owner bound) (cell owner bound actor time)) :=
  ⟨query_is_material owner bound actor time,
    sample_factorizes runtimeSeed (completionDepth owner bound) (cell owner bound actor time)⟩

theorem last_query_is_next (owner : GlobalParentOwner) (bound : Nat) :
    observe owner bound (Fin.last bound) (Fin.last (windowBound owner bound)) =
      rawField (SourceGeneratedRuntimeMaterialStageAt.generate (runtimeAt (completionDepth owner bound))).next.state :=
  query_is_material owner bound (Fin.last bound) (Fin.last (windowBound owner bound))

theorem posterior_material (owner : GlobalParentOwner) (bound : Nat) (index candidate : Fin (bound + 1))
    (same : observe owner bound candidate = observe owner bound index) :
    HEq ((history runtimeSeed bound).stageAt candidate) ((history runtimeSeed bound).stageAt index) := by
  have equality := observe_injective owner bound same
  subst candidate
  rfl

end
end SourcePrimeHistoryRecovery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
