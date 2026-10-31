import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Classical.Source.FreeStrategicProgram
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Settlement.GeneratedSettlement

/-!
# Terminal settlement vocabulary of a free strategic program

Each terminal `(profile, player)` coordinate has one exact value-bearing atom
in the sole source occurrence.  This module fixes the shared rational
vocabulary and proves exact atom provenance.  Admission, reciprocal exchange,
whole-ledger settlement, and fulfilled utility are generated once in the
downstream terminal-exchange modules; no parallel responsibility process is
installed here.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Classical
namespace Source

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Settlement
open FreeStrategicSyntax

namespace FreeStrategicSyntax

def FreeClassicalAtom.settlementKey : FreeClassicalAtom → Nat × Nat
  | .worldTerminalSettlement profile player _ => (profile, player)
  | .authorityResidual profile base _ => (profile, base)
  | _ => (0, 0)

def settlementVocabulary (program : FreeStrategicSyntax) : Vocabulary where
  SourceEvent := FreeClassicalAtom
  Content := Nat × Nat
  Residual := ℚ
  Bearer := program.Actor
  ProtectedInterest := program.Actor
  Scope := Unit
  Lineage := Nat × Nat
  Incidence := Nat × Nat
  SourceObservation := ComplementObservation.canonicalComplementPair
  sourceAnchor := fun event =>
    MinimalRegistrableSourceAnchor.canonical () event.settlementKey
  sourceIncidence := FreeClassicalAtom.settlementKey
  ObstructionAt := fun _ => Unit
  demandContent := fun {source} _ => source.settlementKey
  demandResidual := fun _ => 0
  CommitmentAt := fun _ _ => Unit
  MandateOriginAt := fun _ _ => Unit
  AcceptedTaskAt := fun _ _ => Unit
  ActiveDependencyAt := fun _ _ => Unit
  ProtectedRiskAt := fun _ _ => Unit
  AdmissionAuthorityAt := fun _ _ => Unit
  AcceptedAt := fun _ _ _ => Unit
  StandingMandateAt := fun _ _ _ => Unit
  DischargeJurisdiction := fun _ _ => Unit
  ProgressAt := fun _ _ _ _ => Unit
  MaintenanceAt := fun _ _ _ => Unit
  TypedDeferAt := fun _ _ _ => Unit
  ScopeNarrowingAt := fun _ _ _ => Unit
  TransferAcceptedAt := fun _ _ _ _ => Unit
  FulfilledAt := fun _ _ _ => Unit
  WaivedAt := fun _ _ _ => Unit
  InvalidatedAt := fun _ _ _ => Unit
  AbandonedAt := fun _ _ _ => Unit
  ImpossibleResidueAcceptedAt := fun _ _ _ => Unit
  SupersessionAt := fun _ _ _ _ _ _ _ => Unit
  ReopenAt := fun _ _ _ _ _ _ _ => Unit
  JurisdictionEndedAt := fun _ _ _ => Unit
  ConsentRevokedAt := fun _ _ _ => Unit
  CapacityReleasedAt := fun _ _ _ => Unit
  UpperRouteAt := fun _ _ _ => Unit
  NextActorSignal := Unit
  AgeSignal := Unit
  TransferOfferSignal := Unit

abbrev SettlementV (program : FreeStrategicSyntax) :=
  settlementVocabulary program

def TerminalOutcome (program : FreeStrategicSyntax) :=
  { outcome : program.OutcomeIndex //
    program.isWorldTerminal outcome.1 = true }

namespace TerminalOutcome

def profile {program : FreeStrategicSyntax}
    (outcome : TerminalOutcome program) : program.CanonicalProfile :=
  outcome.1.1

def player {program : FreeStrategicSyntax}
    (outcome : TerminalOutcome program) : program.Player :=
  outcome.1.2

def value {program : FreeStrategicSyntax}
    (outcome : TerminalOutcome program) : ℚ :=
  program.settlementValue outcome.profile outcome.player

def atom {program : FreeStrategicSyntax}
    (outcome : TerminalOutcome program) : FreeClassicalAtom :=
  .worldTerminalSettlement
    (program.profileIndex outcome.profile) outcome.player.val outcome.value

theorem atom_mem_programEvents {program : FreeStrategicSyntax}
    (outcome : TerminalOutcome program) :
    outcome.atom ∈ program.programEvents := by
  simp only [FreeStrategicSyntax.programEvents, List.mem_append]
  apply Or.inl
  apply Or.inr
  unfold FreeStrategicSyntax.outcomeEvents
  apply List.mem_flatMap.mpr
  refine ⟨outcome.profile, ?_, ?_⟩
  · simp
  · have terminal :
        program.isWorldTerminal outcome.profile = true := outcome.2
    rw [terminal]
    apply List.mem_cons_of_mem
    apply List.mem_map.mpr
    exact ⟨outcome.player, by simp, rfl⟩

theorem atom_mem_trace {program : FreeStrategicSyntax}
    (outcome : TerminalOutcome program) :
    outcome.atom ∈ program.occurrence.trace :=
  program.event_mem_trace (outcome.atom_mem_programEvents)

end TerminalOutcome

end FreeStrategicSyntax
end
end Source
end Classical
end Society
end ProcessGame
end SaturationMonoid
