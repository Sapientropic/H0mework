import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.ProcessGameInstance
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Regression.G2PlayerLineageRegression

/-!
# G8 Go process-game instance regression

The generic source is the exact two-pass replay.  Both generator seeds arise
at one shared occurrence root, generic actors are exactly the existing G2
players, and occurrence/trace/fold readouts commute without adding authority
to the core.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Regression
namespace GoProcessGameRegression

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Go Go.G2PlayerLineageRegression

def replay := G2PlayerLineageRegression.passPassReplay

def game : SaturationMonoid.ProcessGame (@goOccurrenceOf 2
    G2PlayerLineageRegression.law G2PlayerLineageRegression.passPassMoves) :=
  goProcessGame replay

theorem source_is_exact_generatedReplay :
    game.source = replay ∧
      game.source.actualEvents = replay.actualEvents ∧
      game.source.moverFold = [.positive, .negative] :=
  ⟨rfl, rfl, G2PlayerLineageRegression.passPass_moverFold⟩

theorem occurrence_and_actual_history_commute :
    game.occurrence = replay.toOccurrence ∧
      game.occurrence.trace = replay.stateTrace ∧
      game.occurrence.trace.map (fun frame => frame.visible.situation) =
        replay.final.positionHistory :=
  ⟨goProcessGame_occurrence replay,
    goProcessGame_occurrence_trace replay,
    goProcessGame_occurrence_positionHistory replay⟩

theorem both_polarity_seeds_are_generated_at_same_root :
    ∃ state,
      state = replay.toOccurrence.root ∧
        state ∈ replay.toOccurrence.trace ∧
        goSeedAt replay state .positive ∧
        goSeedAt replay state .negative := by
  refine ⟨replay.toOccurrence.root, rfl,
    RootedAccountedUnfolding.root_mem_trace replay.toOccurrence, ?_, ?_⟩
  · cases toMoveEq : replay.toOccurrence.root.visible.toMove <;>
      simp [goSeedAt, toMoveEq]
  · cases toMoveEq : replay.toOccurrence.root.visible.toMove <;>
      simp [goSeedAt, toMoveEq]

def positiveSeed :
    SourceSeed goOccurrenceOf Polarity goSeedAt replay :=
  goSourceSeed replay .positive

def negativeSeed :
    SourceSeed goOccurrenceOf Polarity goSeedAt replay :=
  goSourceSeed replay .negative

def positiveActor : GoGeneratedActor replay :=
  generatedActorOf game Polarity goSeedAt goLineage goLineageOf positiveSeed

def negativeActor : GoGeneratedActor replay :=
  generatedActorOf game Polarity goSeedAt goLineage goLineageOf negativeSeed

theorem generic_actor_equiv_is_existing_generated_player :
    goGeneratedActorEquiv replay positiveActor = replay.player .positive ∧
      goGeneratedActorEquiv replay negativeActor = replay.player .negative ∧
      Function.Bijective (goGeneratedActorEquiv replay) :=
  ⟨goGeneratedActorEquiv_generatedActorOf replay .positive,
    goGeneratedActorEquiv_generatedActorOf replay .negative,
    (goGeneratedActorEquiv replay).bijective⟩

theorem every_generic_actor_is_a_trace_generated_seed_image
    (actor : GoGeneratedActor replay) :
    ∃ seed : SourceSeed goOccurrenceOf Polarity goSeedAt replay,
      actor = generatedActorOf game Polarity goSeedAt goLineage goLineageOf seed :=
  generatedActor_exhaustive game Polarity goSeedAt goLineage goLineageOf actor

theorem closed_final_fold_readout_commutes :
    (goFinalFoldReadout replay).value = replay.final :=
  goFinalFoldReadout_value replay

theorem any_commuting_generic_evaluator_is_go_final
    (candidate : RootedAccountedUnfolding (Frame 2) → Frame 2)
    (commutes : ∀ (origin : Frame 2)
        (branches : AccountedBranches (Frame 2)),
      candidate (.occur origin branches) =
        GeneratedReplay.finalAlgebra origin
          (RootedAccountedUnfolding.candidateValues candidate branches)) :
    candidate game.occurrence = replay.final :=
  goCandidateEvaluator_eq_final replay candidate commutes

end GoProcessGameRegression
end Regression
end ProcessGame
end SaturationMonoid
