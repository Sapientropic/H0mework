import H0mework.Versions.X.Fock.CopyGraph.CorrectionUpdate

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalCorrection

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open SourceCopyProgram (Index)
open scoped InnerProductSpace
noncomputable section
universe u
variable {Observed : Type u} [MeasurableSpace Observed]

def updateMap (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed) :
    Space (historyPMF bound) →L[ℂ] Space (observed (historyPMF bound) query) :=
  (((strength depth bound index : ℂ) / (denominator depth bound index query : ℂ)) •
    ((innerSL ℂ (residual (historyPMF bound) query
      (taskValue (historyPMF bound) (SourceGeneratedJointClock.signal bound)))).comp
        (residual (historyPMF bound) query))).smulRight (direction bound query)

def recovery (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed) :
    Space (historyPMF bound) →L[ℂ] Space (observed (historyPMF bound) query) :=
  transfer (historyPMF bound) query + updateMap depth bound index query

theorem update_map_apply (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (value : Space (historyPMF bound)) : updateMap depth bound index query value = update depth bound index query value := by
  change (((strength depth bound index : ℂ) / (denominator depth bound index query : ℂ)) * clockPair bound query value) •
    direction bound query = (((strength depth bound index : ℂ) * clockPair bound query value) /
      (denominator depth bound index query : ℂ)) • direction bound query
  congr 1
  ring

variable [MeasurableSingletonClass Observed]

theorem recovery_source (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (value : Space (historyPMF bound)) :
    recovery depth bound index query value = SourceConditionalGraphDecoder.decode depth bound index query
      (SourceConditionalGraph.copyRead depth bound index value) := by
  change transfer (historyPMF bound) query value + updateMap depth bound index query value = _
  rw [update_map_apply]
  exact (decoder_formula depth bound index query value).symm

theorem recovery_linear (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed) :
    recovery depth bound index query = (SourceConditionalGraphDecoder.decode depth bound index query).comp
      ((SourceCopyGraph.action depth index).comp (SourceJointFiniteDecoder.read bound)) := by
  apply ContinuousLinearMap.ext
  intro value
  change recovery depth bound index query value = SourceConditionalGraphDecoder.decode depth bound index query
    (SourceCopyGraph.action depth index (SourceJointFiniteDecoder.read bound value))
  rw [SourceJointFiniteDecoder.read_source]
  exact recovery_source depth bound index query value

end
end SourceConditionalCorrection
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
