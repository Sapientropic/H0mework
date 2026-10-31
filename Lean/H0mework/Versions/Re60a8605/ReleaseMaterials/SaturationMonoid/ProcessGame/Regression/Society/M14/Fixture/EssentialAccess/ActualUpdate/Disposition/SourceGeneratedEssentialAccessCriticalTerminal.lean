import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Power.Critical.SourceGeneratedCriticalRelationActualUpdate
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Source.SourceGeneratedEssentialAccessCriticalAction

/-!
# Source-generated terminal responsibility for essential-access loss

Every existing essential-access event uses its relation-generated actor's
existing lifecycle bearer.  The generic critical-relation process admits one
new obligation for that exact event and immediately generates a terminal
boundary; reopening is empty.  The combined carrier joins this disposition to
the same event's exact lost power and dependent relation bearer.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedEssentialAccessCriticalTerminal

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Power Exchange Settlement Price Money UBI
open M14EssentialAccessRelationFixture
open M14SourceGeneratedEssentialAccessCriticalAction

def essentialAccessCriticalBearerOf
    (event : EssentialAccessEvent) : Lifecycle.ActorBearer :=
  (sourceGeneratedEssentialAccessCriticalActionAt event
    ).criticalBearer.commonBearer

def essentialAccessCriticalTerminalAt (event : EssentialAccessEvent) :
    SourceGeneratedCriticalRelationTerminalAt
      essentialAccessCriticalBearerOf event :=
  SourceGeneratedCriticalRelationTerminalAt.generate
    essentialAccessCriticalBearerOf event

abbrev EssentialAccessCriticalActualUpdateAt
    (event : EssentialAccessEvent) :=
  SourceGeneratedCriticalRelationActualUpdateAt
    (sourceGeneratedEssentialAccessCriticalActionAt event).criticalBearer
    (essentialAccessCriticalTerminalAt event)

/-- Generic event-indexed actual update.  Power, bearer, admission, terminal
archive and no-reopen proof all come from the exact event. -/
def sourceGeneratedEssentialAccessCriticalActualUpdateAt
    (event : EssentialAccessEvent) :
    EssentialAccessCriticalActualUpdateAt event :=
  SourceGeneratedCriticalRelationActualUpdateAt.generate
    (sourceGeneratedEssentialAccessCriticalActionAt event).criticalBearer
    (essentialAccessCriticalTerminalAt event) rfl

theorem everyEssentialAccessEvent_generatesTerminalActualUpdate :
    ∀ event : EssentialAccessEvent,
      Nonempty (EssentialAccessCriticalActualUpdateAt event) :=
  fun event =>
    ⟨sourceGeneratedEssentialAccessCriticalActualUpdateAt event⟩

theorem essentialAccessCriticalActualUpdate_exact_provenance
    (event : EssentialAccessEvent) :
    (∃ seed : essentialAccessRelationCompiler.ExactRelationSeed,
      (∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
        state = Lifecycle.Universal.FixedAdapter.targetFace.state
          Lifecycle.actualEventGame.source ∧
        essentialAccessRelationCompiler.relationSeedAt
          Lifecycle.actualEventGame.source state seed.1 ∧
        Lifecycle.Universal.FixedAdapter.targetFace.SeedAt
          Lifecycle.actualEventGame.source state
          (essentialAccessRelationCompiler.beneficiaryActorSeed seed.1)) ∧
      seed.actor essentialAccessRelationCompiler =
        essentialAccessCriticalActor event ∧
      essentialAccessRelationCompiler.relationOf seed =
        essentialAccessCriticalRelation event) ∧
    (∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
      state = (essentialAccessCriticalActionController event).actionState
        Lifecycle.actualEventGame.source ∧
      (essentialAccessCriticalActionController event).actionAdmittedAt
        (essentialAccessCriticalActionPower event).action.1) :=
  SourceGeneratedCriticalRelationActualUpdateAt.exact_provenance
    (sourceGeneratedEssentialAccessCriticalActualUpdateAt event)

def sourceGeneratedHealthCriticalActualUpdate :
    EssentialAccessCriticalActualUpdateAt .health :=
  sourceGeneratedEssentialAccessCriticalActualUpdateAt .health

@[simp] theorem healthCriticalTerminal_bearer_exact :
    (criticalRelationObligation essentialAccessCriticalBearerOf .health
      ).bearer = M3FiniteExchangeFixture.exchangeLaw.bearerOfActor
        healthActor :=
  healthCriticalAction_commonBearer_exact

@[simp] theorem healthCriticalTerminal_admission_kind :
    (essentialAccessCriticalTerminalAt .health).admission.lifecycleEvent.kind =
      LifecycleKind.admitted :=
  rfl

theorem healthCriticalTerminal_disposition :
    ∃ archive,
      (essentialAccessCriticalTerminalAt .health).terminal.target.slots[
          (criticalRelationSlot essentialAccessCriticalBearerOf
            .health).val]? = some (.terminal archive) :=
  (essentialAccessCriticalTerminalAt .health).terminalDisposition

theorem healthCriticalTerminal_no_reopen
    (archive : TerminalArchive Lifecycle.LifecycleVocabulary) :
    IsEmpty ((criticalRelationTerminalProcess
      essentialAccessCriticalBearerOf).ReopenEvent archive) :=
  (essentialAccessCriticalTerminalAt .health).noReopen archive

theorem healthCriticalActualUpdate_bearer_commutes :
    sourceGeneratedHealthCriticalAction.criticalBearer.commonBearer =
      (criticalRelationObligation essentialAccessCriticalBearerOf .health
        ).bearer :=
  rfl

theorem healthCriticalActualUpdate_exact_provenance :
    (∃ seed : essentialAccessRelationCompiler.ExactRelationSeed,
      (∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
        state = Lifecycle.Universal.FixedAdapter.targetFace.state
          Lifecycle.actualEventGame.source ∧
        essentialAccessRelationCompiler.relationSeedAt
          Lifecycle.actualEventGame.source state seed.1 ∧
        Lifecycle.Universal.FixedAdapter.targetFace.SeedAt
          Lifecycle.actualEventGame.source state
          (essentialAccessRelationCompiler.beneficiaryActorSeed seed.1)) ∧
      seed.actor essentialAccessRelationCompiler = healthActor ∧
      essentialAccessRelationCompiler.relationOf seed = healthRelation) ∧
    (∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
      state = (essentialAccessCriticalActionController .health).actionState
        Lifecycle.actualEventGame.source ∧
      (essentialAccessCriticalActionController .health).actionAdmittedAt
        (essentialAccessCriticalActionPower .health).action.1) :=
  essentialAccessCriticalActualUpdate_exact_provenance .health

theorem healthCriticalTerminal_not_tenureBearer :
    (criticalRelationObligation essentialAccessCriticalBearerOf .health
      ).bearer ≠ Lifecycle.ActorBearer.target .t1 :=
  healthCriticalBearer_ne_t1

end
end M14SourceGeneratedEssentialAccessCriticalTerminal
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedEssentialAccessCriticalTerminal.sourceGeneratedEssentialAccessCriticalActualUpdateAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedEssentialAccessCriticalTerminal.healthCriticalTerminal_disposition
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedEssentialAccessCriticalTerminal.healthCriticalActualUpdate_exact_provenance
