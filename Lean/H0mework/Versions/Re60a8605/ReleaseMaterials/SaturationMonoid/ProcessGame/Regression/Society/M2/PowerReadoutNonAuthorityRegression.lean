import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M2.GoGeneratedPowerRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Strategy.ClosureGain
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Classical.StrategyEvaluation

/-!
# Closure and payoff readouts are not relation-indexed power authority

On the same reachable bridge ply, one exact obligation update has nonzero
closure gain and a recovered caller strategy produces a terminal payoff.
Nevertheless the source-generated surviving-group relation has equal bounded
freedom and no constraint power.  Closure and payoff remain downstream
readouts; neither can replace a generated interest, phase or future delta.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Go
namespace Society
namespace M2PowerReadoutNonAuthorityRegression

open ProcessGame.Society Power
open Obligation
open _root_.SaturationMonoid.ProcessGame.Go.Classical
open GeneratedRelationRole GeneratedPower
open G2GroupLineageRegression
open M2GoGeneratedPowerRegression

/-! ## Nonzero closure on the bridge event -/

inductive BridgeIncidence where
  | playedPointVacancy
  deriving DecidableEq, Repr

def bridgeVacancyRelation : RelationProbe 3 where
  holds := fun frame => decide (frame.visible.board p01 = none)

def bridgeVacancyLineage : RelationLineage 0
    (RelationTransportLaw.retain 3) mergePrefixReplay
    bridgeVacancyRelation .impose :=
  .marked mergePrefixReplay bridgeVacancyRelation (by trivial)

def bridgeClosureFace :
    OpenRelationObligationFace mergePrefixReplay BridgeIncidence where
  incidences := {.playedPointVacancy}
  horizon := fun _ => 0
  transport := fun _ => RelationTransportLaw.retain 3
  relation := fun _ => bridgeVacancyRelation
  state := fun _ => .impose
  lineage := fun _ => bridgeVacancyLineage

def bridgeClosureUpdate :
    GeneratedObligationUpdate bridgeClosureFace bridgePly :=
  GeneratedObligationUpdate.compile bridgeClosureFace bridgePly

theorem bridge_closure_gain_eq_neg_one :
    closureGain bridgeClosureUpdate = -1 := by
  decide

/-- Nonzero closure on the actual event does not manufacture power over an
independent stable generated interest on that event. -/
theorem nonzero_closure_does_not_create_stable_relation_power :
    closureGain bridgeClosureUpdate = -1 ∧
      ¬ ConstraintPowerOverAt
        (GeneratedGroupRelationRole.compiler 0 bridgePly)
        (GeneratedGroupRelationRole.affectedGroupActor 0 bridgePly
          bridgeLeft.source)
        (GeneratedGroupRelationRole.generatedRelationOf 0 bridgePly
          bridgeLeft.source) :=
  ⟨bridge_closure_gain_eq_neg_one,
    bridge_equal_group_freedom_has_no_constraint_power⟩

/-! ## Caller strategy and payoff on the same actual current -/

def bridgeClassicalGame := recoverExtensiveGame bridgePly.extended 1

def bridgeResignProfile : bridgeClassicalGame.StrategyProfile :=
  bridgeClassicalGame.resignProfile

def bridgeEvaluatedHistory : bridgeClassicalGame.History :=
  FiniteExtensiveGame.evaluateHistory bridgeResignProfile 1
    bridgeClassicalGame.rootHistory

theorem bridge_strategy_generates_terminal_payoff :
    bridgeEvaluatedHistory.current.visible.status =
        .terminal (.resignation .positive) ∧
      bridgeClassicalGame.payoff bridgeEvaluatedHistory
        (bridgePly.extended.player .positive) = some 1 := by
  decide

/-- A valid caller `PureStrategy.choose` and its commuting payoff readout do
not acquire source authority to create relation power. -/
theorem caller_strategy_payoff_does_not_create_power :
    bridgeClassicalGame.payoff bridgeEvaluatedHistory
        (bridgePly.extended.player .positive) = some 1 ∧
      bridgePly.extended.toOccurrence.trace =
        bridgePly.extended.stateTrace ∧
      ¬ ConstraintPowerOverAt
        (GeneratedGroupRelationRole.compiler 0 bridgePly)
        (GeneratedGroupRelationRole.affectedGroupActor 0 bridgePly
          bridgeLeft.source)
        (GeneratedGroupRelationRole.generatedRelationOf 0 bridgePly
          bridgeLeft.source) := by
  refine ⟨bridge_strategy_generates_terminal_payoff.2, ?_,
    bridge_equal_group_freedom_has_no_constraint_power⟩
  exact (bridgeClassicalGame.strategyEvaluation_actual_noninterference
    bridgeResignProfile 1).1

end M2PowerReadoutNonAuthorityRegression
end Society
end Go
end ProcessGame
end SaturationMonoid
