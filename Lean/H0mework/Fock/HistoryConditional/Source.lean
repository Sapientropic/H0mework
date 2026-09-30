import H0mework.Probability.Runtime.Conditional
import H0mework.Checks.Probability.InvariantSource
import H0mework.Fock.SourceHistory.Installed

/-! The actual current's coarse observation conditions the complete original past-stage distribution. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalHistory.Fock

open SourceGeneratedRuntimeHistoryProbability SourceObservationInvariantControls
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

abbrev observed (depth : Nat) : PMF (ZMod 2) := Runtime.observed (process := process) runtimeSeed depth parity

def query (depth : Nat) : ZMod 2 := parity (runtimeAt depth).state

theorem query_supported (depth : Nat) : query depth ∈ (observed depth).support :=
  Runtime.query_supported (process := process) runtimeSeed depth parity (Fin.last depth)

def conditional (depth : Nat) : PMF (Fin (depth + 1)) :=
  Runtime.conditional (process := process) runtimeSeed depth parity (query depth) (query_supported depth)

theorem conditional_support_iff (depth : Nat) (index : Fin (depth + 1)) :
    index ∈ (conditional depth).support ↔ parity (runtimeAt index.val).state = query depth :=
  Runtime.conditional_support_iff (process := process) runtimeSeed depth parity
    (query depth) (query_supported depth) index

theorem current_supported (depth : Nat) : Fin.last depth ∈ (conditional depth).support :=
  (conditional_support_iff depth (Fin.last depth)).mpr rfl

theorem recombine_indices (depth : Nat) :
    (observed depth).bindOnSupport (Runtime.conditional (process := process) runtimeSeed depth parity) = historyPMF depth :=
  Runtime.recombine_indices (process := process) runtimeSeed depth parity

theorem recombine_states (depth : Nat) :
    (observed depth).bindOnSupport
      (fun value supported =>
        (Runtime.conditional (process := process) runtimeSeed depth parity value supported).map (sample runtimeSeed depth)) =
      statePMF runtimeSeed depth :=
  Runtime.recombine_states (process := process) runtimeSeed depth parity

end
end SourceConditionalHistory.Fock
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
