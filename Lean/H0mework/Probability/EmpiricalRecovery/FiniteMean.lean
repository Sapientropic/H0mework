import H0mework.Probability.EmpiricalRecovery.FiniteConditional

/-! The finite decoder reads the existing full conditional distribution at supported raw queries. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionObservationHistory.FiniteRecurrence.Native

open SourceGeneratedRuntimeHistoryProbability
open scoped Classical

noncomputable section

universe u

variable {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}
variable {B : Type u} (read : process.State → B)
variable (windowBound : Nat) (runtime : LivingRuntimeState process) (actorBound : Nat)

def mean (task : Fin (actorBound + 1) → ℂ) (values : Fin (windowBound + 1) → B) : ℂ :=
  if supported : values ∈ ((historyPMF actorBound).map (query read windowBound runtime actorBound)).support then
    ∑ index : Fin (actorBound + 1),
      (SourceConditionalHistory.conditional (historyPMF actorBound) (query read windowBound runtime actorBound)
        values supported index).toReal • task index
  else 0

theorem mean_at_query (task : Fin (actorBound + 1) → ℂ) (index : Fin (actorBound + 1)) :
    mean read windowBound runtime actorBound task (query read windowBound runtime actorBound index) =
      ∑ candidate : Fin (actorBound + 1),
        (conditional read windowBound runtime actorBound index candidate).toReal • task candidate :=
  dif_pos (query_supported read windowBound runtime actorBound index)

end
end SourceGeneratedActionObservationHistory.FiniteRecurrence.Native
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
