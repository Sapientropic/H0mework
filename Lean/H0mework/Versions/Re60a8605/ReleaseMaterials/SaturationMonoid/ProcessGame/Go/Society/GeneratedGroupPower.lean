import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Society.GeneratedGroupRelationRole
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Society.GeneratedPower

/-!
# Heterogeneous Go action power: player controller over group actor

The controller remains the G2 player-lineage image of the actual mover.  The
affected actor remains the M1 boundary-group image of an occupied stone.  The
universal power mouth accepts these two different M0 faces because both exact
seeds inhabit the same `ply.extended.toOccurrence`; no common actor registry
or coercion is introduced.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Go
namespace Society
namespace GeneratedGroupPower

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ProcessGame.Society Power
open Future

instance generatedGroupRelationPhaseZero
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replayPrefix : GeneratedReplay law (Frame.initial n) moves}
    (horizon : Nat) (ply : GeneratedReplay.ActualPly replayPrefix) :
    Zero ((GeneratedGroupRelationRole.compiler horizon ply).Phase
      (goProcessGame ply.extended).source) := by
  change Zero TacticalPhase
  infer_instance

noncomputable abbrev SourceCodes
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replayPrefix : GeneratedReplay law (Frame.initial n) moves}
    {horizon : Nat} (ply : GeneratedReplay.ActualPly replayPrefix)
    (stone : GeneratedGroupRelationRole.RelationSeed ply) :=
  (GeneratedGroupRelationRole.compiler horizon ply).futureCodesAt
    (GeneratedGroupRelationRole.generatedRelationOf horizon ply stone) .source

noncomputable abbrev TargetCodes
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replayPrefix : GeneratedReplay law (Frame.initial n) moves}
    {horizon : Nat} (ply : GeneratedReplay.ActualPly replayPrefix)
    (stone : GeneratedGroupRelationRole.RelationSeed ply) :=
  (GeneratedGroupRelationRole.compiler horizon ply).futureCodesAt
    (GeneratedGroupRelationRole.generatedRelationOf horizon ply stone) .target

/-- Exact actual mover actor on the independent player face. -/
def controllerActor
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replayPrefix : GeneratedReplay law (Frame.initial n) moves}
    (ply : GeneratedReplay.ActualPly replayPrefix) :
    (GeneratedPower.controllerCompiler ply).Actor :=
  (GeneratedPower.exactActionSeed ply).actor
    (GeneratedPower.controllerCompiler ply)

theorem controllerActor_is_existing_actual_owner
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replayPrefix : GeneratedReplay law (Frame.initial n) moves}
    (horizon : Nat) (ply : GeneratedReplay.ActualPly replayPrefix) :
    ply.extended.EventOwnedBy
      (GeneratedRelationRole.actualEventIndex ply)
      (GeneratedRelationRole.generatedActorEquiv horizon ply
        (controllerActor ply)) := by
  change ply.extended.EventOwnedBy
    (GeneratedRelationRole.actualEventIndex ply)
    (ply.extended.player replayPrefix.final.visible.toMove)
  unfold GeneratedReplay.EventOwnedBy
  exact (GeneratedRelationRole.moverAt_actualEventIndex ply).symm

theorem constraintPowerOf
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replayPrefix : GeneratedReplay law (Frame.initial n) moves}
    (horizon : Nat) (ply : GeneratedReplay.ActualPly replayPrefix)
    (stone : GeneratedGroupRelationRole.RelationSeed ply)
    (phaseNonzero :
      (GeneratedGroupRelationRole.phaseEdge horizon ply stone).phaseStep ≠ 0) :
    ConstraintPowerOverAt
      (GeneratedGroupRelationRole.compiler horizon ply)
      (GeneratedGroupRelationRole.affectedGroupActor horizon ply stone)
      (GeneratedGroupRelationRole.generatedRelationOf horizon ply stone) where
  interest :=
    GeneratedGroupRelationRole.exactSeed_generates_group_interest
      horizon ply stone
  phase_nonzero := by
    rw [GeneratedGroupRelationRole.generated_phaseStep_eq_G4_edge]
    exact phaseNonzero

/-- Full heterogeneous action power; the two actor types remain separate in
the theorem mouth. -/
noncomputable def actionPowerOf
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replayPrefix : GeneratedReplay law (Frame.initial n) moves}
    (horizon : Nat) (ply : GeneratedReplay.ActualPly replayPrefix)
    (stone : GeneratedGroupRelationRole.RelationSeed ply)
    (phaseNonzero :
      (GeneratedGroupRelationRole.phaseEdge horizon ply stone).phaseStep ≠ 0)
    (change : ActionableFreedomChange (@GeneratedPower.WordIdle n)
      (SourceCodes (horizon := horizon) ply stone)
      (TargetCodes (horizon := horizon) ply stone)) :
    ActionPowerOverAt
      (GeneratedGroupRelationRole.compiler horizon ply)
      (GeneratedPower.controllerCompiler ply)
      (controllerActor ply)
      (GeneratedGroupRelationRole.affectedGroupActor horizon ply stone)
      (GeneratedGroupRelationRole.generatedRelationOf horizon ply stone) where
  action := GeneratedPower.exactActionSeed ply
  controller_exact := rfl
  constraint := constraintPowerOf horizon ply stone phaseNonzero
  freedomChange := change

end GeneratedGroupPower
end Society
end Go
end ProcessGame
end SaturationMonoid
