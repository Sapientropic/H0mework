import H0mework.Fock.HistoryConditional.CopyHistoryNative
import H0mework.Versions.X.Fock.HistoryConditional.CopyKeysSupport
import H0mework.Versions.X.Fock.PrimeField.RecoveryInformation
import H0mework.Versions.X.Fock.PrimeField.RecoveryMaterial

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyNativeHistory

open SourcePrimeHistoryRecovery
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
noncomputable section

theorem selector_original (owner : GlobalParentOwner) (index : Nat) :
    selector index = (selectedPrime owner index).val := by
  change _ = (euclidHistory owner index).cardinalShadow.minFac
  rw [argument_value]
  rfl

theorem width_original (owner : GlobalParentOwner) (bound : Nat) :
    width bound = windowBound owner bound := by
  rw [width, selector_original owner, windowBound, delay]

theorem read_fibre (bound : Nat) (left right : Fin (bound + 1)) :
    read bound left.val = read bound right.val ↔
      observe sourceOwner bound left = observe sourceOwner bound right := by
  rw [read, read, List.ofFn_inj]
  constructor
  · intro same
    funext time
    rw [query_value, query_value]
    apply (SourceCopyNativeKeys.key_fibre _ _).mp
    let nativeTime : Fin (width bound + 1) :=
      ⟨time.val, by rw [width_original sourceOwner]; exact time.isLt⟩
    exact congrFun same nativeTime
  · intro same
    funext time
    apply (SourceCopyNativeKeys.key_fibre _ _).mpr
    let originalTime : Fin (windowBound sourceOwner bound + 1) :=
      ⟨time.val, by rw [← width_original sourceOwner]; exact time.isLt⟩
    have projected := congrFun same originalTime
    rw [query_value, query_value] at projected
    exact projected

theorem read_injective (bound : Nat) :
    Function.Injective (fun actor : Fin (bound + 1) => read bound actor.val) := by
  intro left right same
  exact observe_injective sourceOwner bound ((read_fibre bound left right).mp same)

end
end SourceCopyNativeHistory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
