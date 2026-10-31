import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Classical.Exchange.TerminalExchangeLifecycle
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Classical.Source.SettlementOutcome
import H0mework.Foundation.Agency.ResponsibilityIncidence

/-!
# Terminal exchange legs, process, and exact incidence

This module owns the reciprocal leg carrier and the one program-local rational
responsibility process.  A false player leg uses its exact value-bearing
settlement atom; a true counterparty leg uses its exact authority-residual
atom; zero-player dummy legs remain exact source restrictions.  No exchange
compiler or completed settlement run is constructed here.
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

abbrev TerminalLegBase (program : FreeStrategicSyntax) :=
  program.AuthorityBase

abbrev TerminalLeg (program : FreeStrategicSyntax) :=
  TerminalLegBase program × Bool

def terminalLegBaseActorIndex (program : FreeStrategicSyntax)
    (base : TerminalLegBase program) : program.ActorIndex :=
  ⟨base.val, by
    unfold FreeStrategicSyntax.actorCount
    omega⟩

def secondActorIndex (program : FreeStrategicSyntax) : program.ActorIndex :=
  ⟨1, (by decide : 1 < 2).trans_le (Nat.le_max_right _ _)⟩

/-- Base zero uses actor one as counterparty; every other base uses actor
zero.  Thus every pair has distinct generated actors without one clearing
actor per player. -/
def terminalCounterActorIndex (program : FreeStrategicSyntax)
    (base : TerminalLegBase program) : program.ActorIndex :=
  if base.val = 0 then secondActorIndex program else program.firstActorIndex

def terminalLegActorIndex (program : FreeStrategicSyntax)
    (leg : TerminalLeg program) : program.ActorIndex :=
  if leg.2 then terminalCounterActorIndex program leg.1
  else terminalLegBaseActorIndex program leg.1

def terminalCounterparty (program : FreeStrategicSyntax)
    (leg : TerminalLeg program) : TerminalLeg program :=
  (leg.1, !leg.2)

@[simp] theorem terminalCounterparty_counterparty
    (program : FreeStrategicSyntax) (leg : TerminalLeg program) :
    terminalCounterparty program (terminalCounterparty program leg) = leg := by
  rcases leg with ⟨base, side⟩
  cases side <;> rfl

theorem terminalCounterparty_ne
    (program : FreeStrategicSyntax) (leg : TerminalLeg program) :
    terminalCounterparty program leg ≠ leg := by
  intro equal
  have sides := congrArg Prod.snd equal
  exact Bool.not_ne_self leg.2 sides

theorem terminalLegActorIndex_counterparty_ne
    (program : FreeStrategicSyntax) (leg : TerminalLeg program) :
    terminalLegActorIndex program leg ≠
      terminalLegActorIndex program (terminalCounterparty program leg) := by
  rcases leg with ⟨base, side⟩
  cases side <;>
    simp only [terminalLegActorIndex, terminalCounterparty,
      Bool.not_false, Bool.not_true, if_true,
      terminalCounterActorIndex]
  all_goals
    by_cases zero : base.val = 0
    · rw [if_pos zero]
      intro equal
      have values := congrArg Fin.val equal
      simp [terminalLegBaseActorIndex, secondActorIndex, zero] at values
    · rw [if_neg zero]
      intro equal
      have values := congrArg Fin.val equal
      simp [terminalLegBaseActorIndex, firstActorIndex] at values
      exact zero (by omega)

theorem actorEmission_mem_trace (program : FreeStrategicSyntax)
    (actor : program.ActorIndex) :
    FreeClassicalAtom.actorEmission actor.val ∈ program.occurrence.trace := by
  apply program.event_mem_trace
  simp only [FreeStrategicSyntax.programEvents, List.mem_append]
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inl
  unfold FreeStrategicSyntax.actorEvents
  apply List.mem_map.mpr
  exact ⟨actor, by simp, rfl⟩

def terminalProfile (program : FreeStrategicSyntax)
    (terminal : program.ExactWorldTerminalRestriction) :
    program.CanonicalProfile :=
  terminal.1.1

def terminalLegPlayer? (program : FreeStrategicSyntax)
    (base : TerminalLegBase program) : Option program.Player :=
  if inRange : base.val < program.playerCount then
    some ⟨base.val, inRange⟩
  else
    none

def playerLegBase (program : FreeStrategicSyntax)
    (player : program.Player) : TerminalLegBase program :=
  ⟨player.val, player.isLt.trans_le (Nat.le_max_left _ _)⟩

def playerLeg (program : FreeStrategicSyntax)
    (player : program.Player) : TerminalLeg program :=
  (playerLegBase program player, false)

@[simp] theorem terminalLegPlayer?_playerLegBase
    (program : FreeStrategicSyntax) (player : program.Player) :
    terminalLegPlayer? program (playerLegBase program player) = some player := by
  unfold terminalLegPlayer? playerLegBase
  simp only [dif_pos player.isLt]

structure TerminalExchangeAdmission (program : FreeStrategicSyntax) where
  terminal : program.ExactWorldTerminalRestriction
  leg : TerminalLeg program

namespace TerminalExchangeAdmission

def profile {program : FreeStrategicSyntax}
    (admission : TerminalExchangeAdmission program) :
    program.CanonicalProfile :=
  terminalProfile program admission.terminal

def actorIndex {program : FreeStrategicSyntax}
    (admission : TerminalExchangeAdmission program) : program.ActorIndex :=
  terminalLegActorIndex program admission.leg

def counterpartyActorIndex {program : FreeStrategicSyntax}
    (admission : TerminalExchangeAdmission program) : program.ActorIndex :=
  terminalLegActorIndex program
    (terminalCounterparty program admission.leg)

def playerOutcome {program : FreeStrategicSyntax}
    (admission : TerminalExchangeAdmission program)
    (player : program.Player) : TerminalOutcome program :=
  ⟨(admission.profile, player), admission.terminal.1.2⟩

def sourceEvent {program : FreeStrategicSyntax}
    (admission : TerminalExchangeAdmission program) : FreeClassicalAtom :=
  if admission.leg.2 then
    program.authorityAtom admission.profile admission.leg.1
  else
    match terminalLegPlayer? program admission.leg.1 with
    | none => .actorEmission admission.actorIndex.val
    | some player => (admission.playerOutcome player).atom

theorem sourceEvent_mem_trace {program : FreeStrategicSyntax}
    (admission : TerminalExchangeAdmission program) :
    admission.sourceEvent ∈ program.occurrence.trace := by
  unfold sourceEvent
  by_cases counterparty : admission.leg.2
  · rw [if_pos counterparty]
    exact program.authorityAtom_mem_trace admission.profile admission.leg.1
      admission.terminal.1.2
  · rw [if_neg counterparty]
    split
    · exact actorEmission_mem_trace program admission.actorIndex
    · rename_i player playerEq
      exact (admission.playerOutcome player).atom_mem_trace

def residual {program : FreeStrategicSyntax}
    (admission : TerminalExchangeAdmission program) : ℚ :=
  if admission.leg.2 then
    program.authorityResidual admission.profile admission.leg.1
  else
    match terminalLegPlayer? program admission.leg.1 with
    | none => 0
    | some player => program.settlementValue admission.profile player

def content {program : FreeStrategicSyntax}
    (admission : TerminalExchangeAdmission program) : Nat × Nat :=
  admission.sourceEvent.settlementKey

theorem sourceEvent_counterparty_ne {program : FreeStrategicSyntax}
    (admission : TerminalExchangeAdmission program) :
    admission.sourceEvent ≠
      (TerminalExchangeAdmission.mk admission.terminal
        (terminalCounterparty program admission.leg)).sourceEvent := by
  rcases admission with ⟨terminal, ⟨base, side⟩⟩
  cases side with
  | false =>
      unfold sourceEvent
      simp only [terminalCounterparty, Bool.not_false,
        Bool.false_eq_true, if_false, if_true]
      split <;> intro equal <;> cases equal
  | true =>
      unfold sourceEvent
      simp only [terminalCounterparty, if_true,
        Bool.not_true, Bool.false_eq_true, if_false]
      split <;> intro equal <;> cases equal

end TerminalExchangeAdmission

def terminalExchangeAdmissionPayload (program : FreeStrategicSyntax)
    (admission : TerminalExchangeAdmission program) :
    NativeAdmissionPayload program.SettlementV where
  sourceEvent := admission.sourceEvent
  content := admission.content
  residual := admission.residual
  bearer := program.actorOf admission.actorIndex
  beneficiary := program.actorOf admission.counterpartyActorIndex
  scope := ()
  lineage := admission.sourceEvent.settlementKey
  anchor_scope_eq := rfl
  anchor_lineage_eq := rfl
  origin := .explicitCommitment ()
  authority := ()
  assumption := .accepted ()
  dischargeJurisdiction := ()

def terminalExchangeProcess (program : FreeStrategicSyntax) :
    NativeResponsibilityProcess program.SettlementV where
  AdmissionEvent := TerminalExchangeAdmission program
  admissionPayload := terminalExchangeAdmissionPayload program
  BoundaryEvent := fun _ => Unit
  boundarySource := fun {obligation} _ => obligation.admission.sourceEvent
  boundary_anchor_eq := by
    intro obligation event
    rfl
  boundary_incidence_eq := by
    intro obligation event
    rfl
  boundaryDisposition := fun _ => .terminal (.final (.fulfilled ()))
  ReopenEvent := fun _ => Empty
  reopenPayload := fun event => nomatch event

abbrev TerminalExchangeP (program : FreeStrategicSyntax) :=
  terminalExchangeProcess program

def terminalExchangeIncidenceCompiler (program : FreeStrategicSyntax) :
    ActorResponsibilityIncidenceCompiler
      (exchangeLifecycleCore program) program.SettlementV where
  SourceSeed := Empty
  sourceAdmittedAt := fun seed => nomatch seed
  sourceActorSeed := fun seed => nomatch seed
  sourceActor_active := by
    intro seed
    exact nomatch seed
  sourceObligation := fun seed => nomatch seed
  sourceEvent := fun seed => nomatch seed
  TargetSeed := TerminalExchangeAdmission program
  targetAdmittedAt := fun _ => True
  targetActorSeed := fun admission => admission.actorIndex
  targetActor_active := by
    intro seed admitted
    rfl
  targetObligation := fun admission =>
    (terminalExchangeAdmissionPayload program admission).toObligation
  targetEvent := fun admission => admission.sourceEvent
  HistoricalSeed := Empty
  historicalAdmittedAt := fun seed => nomatch seed
  historicalActorSeed := fun seed => nomatch seed
  historicalActorState := fun seed => nomatch seed
  historicalActor_active := by
    intro seed
    exact nomatch seed
  historicalObligation := fun seed => nomatch seed
  historicalEvent := fun seed => nomatch seed

def terminalExchangeIncidence (program : FreeStrategicSyntax) :
    ActorResponsibilityIncidence
      (exchangeLifecycleCore program) program.SettlementV where
  compiler := terminalExchangeIncidenceCompiler program
  source_actor_unique := by
    intro obligation sourceEvent first last firstAt
    exact nomatch firstAt.seed.1
  target_actor_unique := by
    intro obligation sourceEvent first last firstAt lastAt
    have obligationsEq := firstAt.obligation_eq.trans lastAt.obligation_eq.symm
    have bearersEq := congrArg AdmittedObligation.bearer obligationsEq
    calc
      first = firstAt.seed.actor (terminalExchangeIncidenceCompiler program) :=
        firstAt.actor_eq.symm
      _ = lastAt.seed.actor (terminalExchangeIncidenceCompiler program) := by
        exact bearersEq
      _ = last := lastAt.actor_eq
  historical_actor_unique := by
    intro obligation sourceEvent first last firstAt
    exact nomatch firstAt.seed.1

end
end GeneratedTerminalExchange
end Classical
end Society
end ProcessGame
end SaturationMonoid
