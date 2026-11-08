import H0mework.Versions.Rf9493be3.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Adapters.GeneratedTimeReplay
import H0mework.Versions.Rf9493be3.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Regression.G1RulesRegression

/-!
# G1 P98/P99 direct consumer

The concrete capture-and-terminal script is replayed by the existing P98 time
field and P99 `repeatEval`; its endpoint is the same shared-occurrence fold.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Go
namespace G1GeneratedTimeReplayRegression

open G1RulesRegression

theorem completeReplay_timeField_final :
    (reflexiveQueryIteratedTimeField (generatedReplayQuery halfKomiLaw)
      { current := some (Frame.initial 2), remaining := completeMoves }).stateAt
        completeMoves.length =
      ({ current := some completeReplay.final, remaining := [] } : ReplayCursor 2) :=
  generatedReplay_timeField_final completeReplay

theorem completeReplay_repeatEval :
    StatefulGenAlg.repeatEval
        (reflexiveQueryPrimitive (generatedReplayQuery halfKomiLaw))
        (reflexiveQueryStatefulPlan (generatedReplayQuery halfKomiLaw))
        completeMoves.length
        ({ current := some (Frame.initial 2), remaining := completeMoves } : ReplayCursor 2)
        (reflexiveQueryIteratedObservationTrace (generatedReplayQuery halfKomiLaw)
          { current := some (Frame.initial 2), remaining := completeMoves }
          completeMoves.length)
        ({ current := some completeReplay.final, remaining := [] } : ReplayCursor 2) :=
  generatedReplay_repeatEval completeReplay

theorem completeReplay_p99_endpoint_is_occurrence_fold :
    some completeReplay.final =
      some (completeReplay.toOccurrence.fold GeneratedReplay.finalAlgebra) :=
  generatedReplay_repeatEndpoint_eq_occurrenceFold completeReplay

end G1GeneratedTimeReplayRegression
end Go
end ProcessGame
end SaturationMonoid
