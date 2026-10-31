import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Classical.Exchange.TerminalExchangeProcess
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Exchange.GeneratedExchange

/-!
# Source-generated reciprocal exchange at a terminal strategic profile

Every exact world-terminal restriction generates one finite reciprocal
exchange in the original free-program occurrence.  This module owns only the
M3 exchange compiler/law and its public provenance mouths.  Lifecycle,
reciprocal leg, process, and incidence machinery live in the two lower modules;
settlement continuation remains downstream.
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
open _root_.SaturationMonoid.ProcessGame.Society.Exchange

def firstTerminalLegBase (program : FreeStrategicSyntax) :
    TerminalLegBase program :=
  ⟨0, by omega⟩

def terminalExchangeCompiler (program : FreeStrategicSyntax) :
    SourceOwnedExchangeCompiler
      (exchangeLifecycleCore program)
      program.SettlementV
      (TerminalExchangeP program)
      (terminalExchangeIncidence program)
      (terminalRelationCompiler program) where
  ExchangeSeed := program.ExactWorldTerminalRestriction
  exchangeAdmittedAt := fun _ => True
  Leg := fun _ => TerminalLeg program
  legDecidableEq := fun _ => inferInstance
  legs := fun _ => (Finset.univ : Finset (TerminalLeg program)).toList
  legs_nodup := by
    intro seed
    exact Finset.nodup_toList _
  leg_mem := by
    intro seed leg
    simp
  principalLeg := fun _ => (firstTerminalLegBase program, false)
  counterparty := fun _ leg => terminalCounterparty program leg
  counterparty_involutive := by
    intro seed leg
    exact terminalCounterparty_counterparty program leg
  counterparty_ne := by
    intro seed leg
    exact terminalCounterparty_ne program leg
  relationSeed := fun _ leg => terminalLegActorIndex program leg
  relationSeed_active := by
    intro seed leg admitted
    rfl
  responsibilitySeed := fun terminal leg => ⟨terminal, leg⟩
  responsibilitySeed_active := by
    intro seed leg admitted
    trivial
  admissionEvent := fun terminal leg => ⟨terminal, leg⟩
  sourceState := fun _ =>
    NativeResponsibilityProcess.GeneratedState.initial
      (TerminalExchangeP program)
  parentStateOf := fun _ => program.actorBoundaryAtom

/-- Exact exchange seed generated from an exact terminal restriction. -/
def exactTerminalExchangeSeed (program : FreeStrategicSyntax)
    (terminal : program.ExactWorldTerminalRestriction) :
    (terminalExchangeCompiler program).ExactExchangeSeed :=
  ⟨terminal, program.actorBoundaryAtom,
    program.actorBoundaryAtom_mem_trace, rfl, trivial⟩

def terminalExchangeLaw (program : FreeStrategicSyntax) :
    SourceOwnedExchangeLaw
      (exchangeLifecycleCore program)
      program.SettlementV
      (TerminalExchangeP program)
      (terminalExchangeIncidence program)
      (terminalRelationCompiler program) where
  compiler := terminalExchangeCompiler program
  bearerOfActor := id
  protectedInterestOfActor := id
  actorSeed_eq := by
    intro seed leg
    rfl
  obligation_eq := by
    intro seed leg
    rfl
  sourceEvent_eq := by
    intro seed leg
    rfl
  bearer_eq := by
    intro seed leg
    rfl
  beneficiary_eq := by
    intro seed leg
    rfl
  restriction_parent_state_eq := by
    intro seed leg
    rfl
  sourceEvents_ne := by
    intro seed leg
    exact TerminalExchangeAdmission.sourceEvent_counterparty_ne
      (⟨seed.1, leg⟩ : TerminalExchangeAdmission program)
  counterpartyActors_ne := by
    intro seed leg equal
    apply terminalLegActorIndex_counterparty_ne program leg
    exact congrArg Subtype.val equal

/-- Public generated exchange at one exact terminal restriction. -/
def terminalExchange (program : FreeStrategicSyntax)
    (terminal : program.ExactWorldTerminalRestriction) :
    (terminalExchangeLaw program).GeneratedExchange :=
  (terminalExchangeLaw program).exchangeOf
    (exactTerminalExchangeSeed program terminal)

@[simp] theorem terminalExchange_exactSeed
    (program : FreeStrategicSyntax)
    (terminal : program.ExactWorldTerminalRestriction) :
    (terminalExchange program terminal).exactSeed
        (terminalExchangeLaw program) =
      exactTerminalExchangeSeed program terminal :=
  rfl

/-- The payoff leg, typed in this terminal exchange's dependent carrier. -/
def terminalPlayerLeg (program : FreeStrategicSyntax)
    (terminal : program.ExactWorldTerminalRestriction)
    (player : program.Player) :
    (exactTerminalExchangeSeed program terminal).Leg :=
  playerLeg program player

@[simp] theorem terminalPlayerLeg_eq
    (program : FreeStrategicSyntax)
    (terminal : program.ExactWorldTerminalRestriction)
    (player : program.Player) :
    terminalPlayerLeg program terminal player = playerLeg program player :=
  rfl

/-- Player utility is the residual of its exact admitted exchange obligation. -/
theorem terminalPlayerLeg_obligation_residual
    (program : FreeStrategicSyntax)
    (terminal : program.ExactWorldTerminalRestriction)
    (player : program.Player) :
    ((exactTerminalExchangeSeed program terminal).obligation
      (terminalExchangeCompiler program)
      (terminalPlayerLeg program terminal player)).residual =
        program.settlementValue (terminalProfile program terminal) player := by
  change
    (TerminalExchangeAdmission.residual
      (⟨terminal, playerLeg program player⟩ :
        TerminalExchangeAdmission program)) = _
  simp [TerminalExchangeAdmission.residual,
    TerminalExchangeAdmission.profile, playerLeg,
    terminalLegPlayer?_playerLegBase]

/-- The payoff obligation is borne by the exact M0 participation actor. -/
theorem terminalPlayerLeg_obligation_bearer
    (program : FreeStrategicSyntax)
    (terminal : program.ExactWorldTerminalRestriction)
    (player : program.Player) :
    ((exactTerminalExchangeSeed program terminal).obligation
      (terminalExchangeCompiler program)
      (terminalPlayerLeg program terminal player)).bearer =
        program.actorOf (program.playerActorIndex player) := by
  change
    program.actorOf
        (terminalLegBaseActorIndex program (playerLegBase program player)) =
      program.actorOf (program.playerActorIndex player)
  apply Subtype.ext
  apply Fin.ext
  rfl

theorem terminalPlayerLeg_sourceEvent_mem_trace
    (program : FreeStrategicSyntax)
    (terminal : program.ExactWorldTerminalRestriction)
    (player : program.Player) :
    (exactTerminalExchangeSeed program terminal).sourceEvent
        (terminalExchangeCompiler program)
        (terminalPlayerLeg program terminal player) ∈
      program.occurrence.trace := by
  exact TerminalExchangeAdmission.sourceEvent_mem_trace
    (⟨terminal, playerLeg program player⟩ :
      TerminalExchangeAdmission program)

/-- Clearing legs at zero players retain the same exact event provenance. -/
theorem terminalExchangeLeg_sourceEvent_mem_trace
    (program : FreeStrategicSyntax)
    (terminal : program.ExactWorldTerminalRestriction)
    (leg : (exactTerminalExchangeSeed program terminal).Leg) :
    (exactTerminalExchangeSeed program terminal).sourceEvent
        (terminalExchangeCompiler program) leg ∈
      program.occurrence.trace :=
  TerminalExchangeAdmission.sourceEvent_mem_trace
    (⟨terminal, leg⟩ : TerminalExchangeAdmission program)

theorem terminalExchange_counterparty_sourceEvents_ne
    (program : FreeStrategicSyntax)
    (terminal : program.ExactWorldTerminalRestriction)
    (leg : (exactTerminalExchangeSeed program terminal).Leg) :
    (exactTerminalExchangeSeed program terminal).sourceEvent
        (terminalExchangeCompiler program) leg ≠
      (exactTerminalExchangeSeed program terminal).sourceEvent
        (terminalExchangeCompiler program)
        ((exactTerminalExchangeSeed program terminal).counterparty
          (terminalExchangeCompiler program) leg) :=
  (terminalExchangeLaw program).counterparty_restrictions_distinct
    (exactTerminalExchangeSeed program terminal) leg

/-- Direct M3 reciprocity consumer for every exact terminal-exchange leg. -/
theorem terminalExchange_native_reciprocity
    (program : FreeStrategicSyntax)
    (terminal : program.ExactWorldTerminalRestriction)
    (leg : (exactTerminalExchangeSeed program terminal).Leg) :
    (terminalRelationCompiler program).GeneratedInterestAt
        ((exactTerminalExchangeSeed program terminal).actor
          (terminalExchangeCompiler program) leg)
        ((exactTerminalExchangeSeed program terminal).relation
          (terminalExchangeCompiler program) leg) ∧
      Nonempty ((terminalExchangeIncidence program).TargetResponsibilityAt
        ((exactTerminalExchangeSeed program terminal).actor
          (terminalExchangeCompiler program) leg)
        ((exactTerminalExchangeSeed program terminal).obligation
          (terminalExchangeCompiler program) leg)
        ((exactTerminalExchangeSeed program terminal).sourceEvent
          (terminalExchangeCompiler program) leg)) ∧
      Nonempty (SourceOwnsResponsibilityIncidence program.SettlementV
        ((exactTerminalExchangeSeed program terminal).sourceEvent
          (terminalExchangeCompiler program) leg)
        ((exactTerminalExchangeSeed program terminal).obligation
          (terminalExchangeCompiler program) leg)) ∧
      ((exactTerminalExchangeSeed program terminal).obligation
          (terminalExchangeCompiler program) leg).bearer =
        (terminalExchangeLaw program).bearerOfActor
          ((exactTerminalExchangeSeed program terminal).actor
            (terminalExchangeCompiler program) leg) ∧
      ((exactTerminalExchangeSeed program terminal).obligation
          (terminalExchangeCompiler program) leg).beneficiary =
        (terminalExchangeLaw program).protectedInterestOfActor
          ((exactTerminalExchangeSeed program terminal).actor
            (terminalExchangeCompiler program)
            ((exactTerminalExchangeSeed program terminal).counterparty
              (terminalExchangeCompiler program) leg)) :=
  (terminalExchangeLaw program).native_reciprocity
    (exactTerminalExchangeSeed program terminal) leg

end
end GeneratedTerminalExchange
end Classical
end Society
end ProcessGame
end SaturationMonoid
