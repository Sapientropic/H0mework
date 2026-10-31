import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.FutureFreedom
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Regression.G2GroupLineageRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Regression.G3SearchExposureRegression

/-!
# G4 finite relation-freedom regression

The first instance uses the source-generated turn constraint on two exact
actual plies: the first ply strictly compresses its bounded move-word fibre,
the second strictly enlarges it and restores the concrete word that was lost.
The second instance consumes G2's reachable whole capture and proves strict
shrink of the fixed group-survival relation.

Both tests use the same `futureConeAt` provenance theorem.  No local legal
expansion, path executor, relation owner or tactical phase is recreated here.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Go
namespace G4FutureFreedomRegression

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

/-! ## Exact shrink, growth and recovery on two actual plies -/

def p11 : Point 2 := (1, 1)

theorem responseTarget_isSome :
    (nativeStep? G3SearchExposureRegression.testLaw
      G3SearchExposureRegression.chosenPly.extended.final
      (.play p11)).isSome = true := by
  decide

def responseTarget : Frame 2 :=
  (nativeStep? G3SearchExposureRegression.testLaw
    G3SearchExposureRegression.chosenPly.extended.final
    (.play p11)).get responseTarget_isSome

def responsePly : GeneratedReplay.ActualPly
    G3SearchExposureRegression.chosenPly.extended where
  target := responseTarget
  emitted := .play p11
  step := by
    unfold LegalStep responseTarget
    exact (Option.some_get responseTarget_isSome).symm

/-- The relation is anchored once at the actual source current.  It is not
recomputed after pressure, so the response can genuinely restore it. -/
def turnRelation : RelationProbe 2 :=
  sourceTurnRelationAt G3SearchExposureRegression.emptyReplay

theorem turn_freedom_exact_fibres :
    relationFreedom G3SearchExposureRegression.emptyReplay 1 turnRelation =
        {[], [(.resign : Move 2)]} ∧
      relationFreedom G3SearchExposureRegression.chosenPly.extended 1 turnRelation = ∅ ∧
      relationFreedom responsePly.extended 1 turnRelation =
        {[], [(.resign : Move 2)]} := by
  decide

theorem pressure_strictly_shrinks_turn_freedom :
    FreedomShrinksAt G3SearchExposureRegression.chosenPly 1 turnRelation := by
  unfold FreedomShrinksAt
  decide

theorem response_strictly_grows_same_turn_freedom :
    FreedomGrowsAt responsePly 1 turnRelation := by
  unfold FreedomGrowsAt
  decide

/-- The nonempty resignation continuation is present before pressure, absent
immediately after pressure and present again after the exact response. -/
def exactTurnRecovery :
    TurnFreedomRecoveryAt G3SearchExposureRegression.chosenPly responsePly 1 where
  compressed := pressure_strictly_shrinks_turn_freedom
  expanded := response_strictly_grows_same_turn_freedom
  recoveredWord := [(.resign : Move 2)]
  presentBefore := by decide
  lostUnderPressure := by decide
  restoredByResponse := by decide

/-- The recovered common-carrier word reconstructs an exact continuation and
its whole state path is in the same response-rooted finite cone fold. -/
theorem recovered_word_has_same_cone_provenance :
    ∃ continuation : GeneratedReplay G3SearchExposureRegression.testLaw
        responsePly.extended.final exactTurnRecovery.recoveredWord,
      continuation.stateTrace ∈
          rootedPaths (futureConeAt responsePly.extended 1) ∧
        continuation.stateTrace.all turnRelation.holds = true :=
  relationFreedom_member_factors_through_futureCone
    responsePly.extended 1 turnRelation exactTurnRecovery.restoredByResponse

/-- Strict shrink and strict growth cannot both hold when their two fibres are
definitionally the same; this rejects a no-change phase fabricated by label. -/
theorem unchanged_freedom_cannot_strictly_shrink :
    ¬ StrictFreedomSubset
      (relationFreedom G3SearchExposureRegression.emptyReplay 0 turnRelation)
      (relationFreedom G3SearchExposureRegression.emptyReplay 0 turnRelation) :=
  StrictFreedomSubset.irrefl _

/-! ## Reachable whole capture shrinks a generated group relation -/

abbrev capturedGroup :
    SnapshotGroup G2GroupLineageRegression.capturePrefixReplay.final.visible.board :=
  G2GroupLineageRegression.capturedGroupTerminal.source

theorem captured_group_source_relation_holds :
    (groupRelationProbe capturedGroup).holds
      G2GroupLineageRegression.capturePrefixReplay.final = true :=
  groupRelationProbe_holds_source _ _

theorem captured_group_relation_fibres :
    (.pass :: [] : List (Move 2)) ∈
        relationFreedom G2GroupLineageRegression.capturePrefixReplay 1
          (groupRelationProbe capturedGroup) ∧
      relationFreedom G2GroupLineageRegression.capturePly.extended 1
        (groupRelationProbe capturedGroup) = ∅ := by
  decide

/-- This is the group-anchored public mouth, not a caller-written relation
predicate: G2's exact source quotient class generates the relation. -/
theorem actual_capture_strictly_shrinks_group_freedom :
    GroupFreedomShrinksAt G2GroupLineageRegression.capturePly 1 capturedGroup := by
  unfold GroupFreedomShrinksAt FreedomShrinksAt
  decide

theorem actual_capture_does_not_grow_group_freedom :
    ¬ GroupFreedomGrowsAt G2GroupLineageRegression.capturePly 1 capturedGroup := by
  unfold GroupFreedomGrowsAt FreedomGrowsAt
  decide

theorem captured_group_lost_word_has_source_cone_provenance :
    ∃ lostWord,
      lostWord ∈ relationFreedom G2GroupLineageRegression.capturePrefixReplay 1
          (groupRelationProbe capturedGroup) ∧
      lostWord ∉ relationFreedom G2GroupLineageRegression.capturePly.extended 1
          (groupRelationProbe capturedGroup) ∧
      ∃ continuation : GeneratedReplay G2GroupLineageRegression.zeroKomiLaw
          G2GroupLineageRegression.capturePrefixReplay.final lostWord,
        continuation.stateTrace ∈
          rootedPaths (futureConeAt G2GroupLineageRegression.capturePrefixReplay 1) :=
  (FreedomShrinksAt.provenance
    actual_capture_strictly_shrinks_group_freedom).2

/-- The named lost freedom is a genuinely nonempty one-ply continuation.  Its
dependent replay path is folded from the horizon-one cone, so this regression
cannot collapse to a current-only truth test. -/
theorem captured_group_pass_path_factors_through_horizon_one :
    ∃ continuation : GeneratedReplay G2GroupLineageRegression.zeroKomiLaw
        G2GroupLineageRegression.capturePrefixReplay.final
        [(.pass : Move 2)],
      continuation.stateTrace ∈
          rootedPaths
            (futureConeAt G2GroupLineageRegression.capturePrefixReplay 1) ∧
        continuation.stateTrace.all
          (groupRelationProbe capturedGroup).holds = true := by
  apply relationFreedom_member_factors_through_futureCone
  exact captured_group_relation_fibres.1

end G4FutureFreedomRegression
end Go
end ProcessGame
end SaturationMonoid
