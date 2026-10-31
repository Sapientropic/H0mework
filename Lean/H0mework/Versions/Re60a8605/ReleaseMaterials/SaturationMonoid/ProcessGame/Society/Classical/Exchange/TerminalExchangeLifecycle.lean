import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Classical.Source.FreeStrategicProgram

/-!
# Terminal exchange lifecycle and all-actor relation face

The original free-program occurrence supplies one adjacent M1 boundary from
its root to the generated actor-boundary atom.  Terminal exchange relations
range over every generated actor, including clearing actors, while retaining
no independent strategic future authority.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Classical
namespace GeneratedTerminalExchange

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations
open Source Source.FreeStrategicSyntax

def exchangeSourceActorSeedAt (program : FreeStrategicSyntax)
    (_source : Unit) (state : FreeClassicalAtom)
    (_actor : program.ActorIndex) : Prop :=
  state = .origin

def exchangeSourceActorFace (program : FreeStrategicSyntax) :
    M0BoundaryFace program.occurrenceOf where
  Seed := program.ActorIndex
  Lineage := fun _ => program.ActorIndex
  SeedAt := exchangeSourceActorSeedAt program
  lineageOf := fun _ seed => seed.1
  state := fun _ => .origin
  seedAt_state := by
    intro source state seed active
    exact active

/-- The source root and actor-boundary atom form the one adjacent lifecycle
edge consumed by terminal exchange. -/
def exchangeLifecycleCore (program : FreeStrategicSyntax) :
    SourceOwnedLifecycleCore program.occurrenceOf program.processGame where
  sourceFace := exchangeSourceActorFace program
  targetFace := program.actorFace
  HistorySeed := Empty
  HistoryLineage := fun _ => Empty
  historySeedAt := fun _ _ seed => nomatch seed
  historyLineageOf := fun _ seed => nomatch seed.1
  LinkSeed := Empty
  linkAdmittedAt := fun seed => nomatch seed
  linkSource := fun seed => nomatch seed
  linkTarget := fun seed => nomatch seed
  linkSource_active := by
    intro seed
    exact nomatch seed
  linkTarget_active := by
    intro seed
    exact nomatch seed
  IdentitySeed := Empty
  identityAdmittedAt := fun seed => nomatch seed
  identitySource := fun seed => nomatch seed
  identityTarget := fun seed => nomatch seed
  identitySource_active := by
    intro seed
    exact nomatch seed
  identityTarget_active := by
    intro seed
    exact nomatch seed
  ExitSeed := Empty
  exitAdmittedAt := fun seed => nomatch seed
  exitSource := fun seed => nomatch seed
  exitSource_active := by
    intro seed
    exact nomatch seed
  FreshSeed := Empty
  freshAdmittedAt := fun seed => nomatch seed
  freshTarget := fun seed => nomatch seed
  freshTarget_active := by
    intro seed
    exact nomatch seed
  ReappearanceSeed := Empty
  reappearanceAdmittedAt := fun seed => nomatch seed
  reappearanceHistory := fun seed => nomatch seed
  reappearanceHistoryState := fun seed => nomatch seed
  reappearanceHistory_active := by
    intro seed
    exact nomatch seed
  reappearanceTarget := fun seed => nomatch seed
  reappearanceTarget_active := by
    intro seed
    exact nomatch seed
  sourceIndex := 0
  source_state_mem := program.origin_mem_trace
  target_state_mem := program.actorBoundaryAtom_mem_trace
  source_at_index := program.occurrence_trace_getElem?_zero
  target_follows_source := program.occurrence_trace_getElem?_one
  history_before_event := by
    intro state seed active
    exact nomatch seed

def terminalRelationSeedAt (program : FreeStrategicSyntax)
    (_source : Unit) (state : FreeClassicalAtom)
    (_actor : program.ActorIndex) : Prop :=
  state = program.actorBoundaryAtom

/-- Exchange relations cover all generated actors.  Empty future fibres keep
them disjoint from the existing player-strategy relation compiler. -/
abbrev terminalRelationCompiler (program : FreeStrategicSyntax) :
    SourceOwnedRelationRoleCompiler program.occurrenceOf
      program.processGame (exchangeLifecycleCore program).targetFace where
  RelationSeed := program.ActorIndex
  RelationLineage := fun _ => program.ActorIndex
  relationSeedAt := terminalRelationSeedAt program
  relationLineageOf := fun _ seed => seed.1
  beneficiaryActorSeed := id
  beneficiaryActor_active := by
    intro source state seed active
    exact active
  Role := fun _ => Unit
  Phase := fun _ => Unit
  sourceRoleOf := fun _ _ => ()
  phaseStepOf := fun _ _ => ()
  advanceRole := fun _ _ _ => ()
  FutureCode := Empty
  futureCodeDecidableEq := inferInstance
  futureCodeCarrier := ∅
  futureIdle := fun code => nomatch code
  FutureContinuationAt := fun _ _ code => nomatch code
  futureBoundaryState := fun _ _ => program.actorBoundaryAtom
  futureBoundaryState_mem := by
    intro lineage side
    exact program.actorBoundaryAtom_mem_trace
  FutureContinuationWitnessAt := fun _ _ code => nomatch code
  futureContinuation_witnessed := by
    intro lineage side code
    exact nomatch code

end
end GeneratedTerminalExchange
end Classical
end Society
end ProcessGame
end SaturationMonoid
