import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.History
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Finance
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle
abbrev Input := ProgrammeSource.Input Actor Good Port Technology Instrument
def sources (input : Input) := input
abbrev Account := (Financial.Family.process sources).GeneratedState

/-- All later occurrences consume one persistent family account; old source accounts remain separate. -/
structure State (plan : Plan) where
  private mk ::
  session : Session plan
  account : Account

def start {plan : Plan} (initial : Session plan) : State plan :=
  ⟨initial,.initial (Financial.Family.process sources)⟩

def State.preAccount {plan : Plan} (state : State plan) (query : Query) (mode : Mode) : Account :=
  Financial.Family.consumeVisit sources (state.session.input query mode) 0 state.account

def State.postAccount {plan : Plan} (state : State plan) (query : Query) (mode : Mode) : Account :=
  Financial.Family.consumeVisit sources (state.session.input query mode) 1 (state.preAccount query mode)

def State.input {plan : Plan} (state : State plan) (query : Query) (mode : Mode) := state.session.input query mode

namespace Runtime
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
variable {plan : Plan} (state : State plan) (query : Query) (mode : Mode)
structure Result (ordinal : Nat) where
  supply : Supply.Runtime.Result state.session query mode ordinal
  account : Account
  actualAccount : account=Financial.Family.continueVisits sources (state.input query mode) 0 (ordinal+1) state.account

def result (ordinal : Nat) : Result state query mode ordinal :=
  ⟨Supply.Runtime.result state.session query mode ordinal,
    Financial.Family.continueVisits sources (state.input query mode) 0 (ordinal+1) state.account,rfl⟩

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (state.input query mode)).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ =>
    (ordinal : Nat) → current=(ProgrammeHistory.visitAt (state.input query mode) ordinal).current →
      Result state query mode ordinal
  project := fun _ {_} _ _ ordinal _ => result state query mode ordinal

def root := (ProgrammeLiving.livingRoot (state.input query mode)).withProjectionCoface (projectionLaw state query mode)
def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (state.input query mode)) :=
  ⟨ProgrammeSource.V (state.input query mode),root state query mode,
   ProgrammeHistory.temporalVisit (state.input query mode) ordinal⟩
def process : SourceNativeLivingRootProcess (ProgrammeSource.N (state.input query mode)) where
  State := Nat
  stateAt := stateAt state query mode
  stateAt_injective := by
    intro first second same
    have labels := congrArg (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (state.input query mode)) =>
      (⟨state.V.Current,state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    exact ProgrammeHistory.visit_current_injective (state.input query mode) (eq_of_heq (Sigma.mk.inj labels).2)
  initial := 0
  successorAt := fun n => ⟨n+1,rfl,HEq.rfl⟩

inductive Face where | execution | supply
def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (state.input query mode)) where
  process := process state query mode
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .execution => ProgrammeLiving.projectionLaw (state.input query mode)
    | .supply => projectionLaw state query mode
  installationAt := by
    intro tick face
    cases face
    · exact SourceNativeProjectionLaw.InstallationAt.inheritedCoface
        (ProgrammeLiving.authoritySource (state.input query mode)) (projectionLaw state query mode)
    · exact SourceNativeProjectionLaw.InstallationAt.componentCoface
        (ProgrammeLiving.authoritySource (state.input query mode)) (projectionLaw state query mode)
  projectionAt := fun _ face => match face with | .execution => .execution | .supply => ()
def activated (ordinal : Nat) := (facade state query mode).seed.advance ordinal
theorem activated_state (ordinal : Nat) : (activated state query mode ordinal).state=ordinal := by
  induction ordinal with | zero => rfl | succ n ih => exact congrArg Nat.succ ih
def consume (ordinal : Nat) : Result state query mode ordinal :=
  match (facade state query mode).readoutAt (activated state query mode ordinal) .supply with
  | .inl ⟨_,payload⟩ => payload ordinal (by
      change (ProgrammeHistory.visitAt (state.input query mode) (activated state query mode ordinal).state).current=_
      rw [activated_state])
  | .inr impossible => nomatch impossible

theorem same_occurrence_whole_ledger_and_own_next (ordinal : Nat) :
    (activated state query mode ordinal).tick.generated.occurrence=
      (activated state query mode ordinal).current.root.toAuthoritativeRoot.toLedgerRoot.emitted
        (activated state query mode ordinal).current.visit.current ∧
    HEq (activated state query mode ordinal).tick.generated.wholeLedgerWriteBack
      ((activated state query mode ordinal).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (activated state query mode ordinal).current.visit.current) ∧
    HEq ((facade state query mode).readoutAt (activated state query mode ordinal) .supply)
      ((activated state query mode ordinal).tick.generated.projectionOutcome
        (((facade state query mode).installationAt (activated state query mode ordinal) .supply).embed
          ((facade state query mode).projectionAt (activated state query mode ordinal) .supply))) ∧
    (activated state query mode ordinal).tick.nextCurrent=
      (process state query mode).stateAt ((process state query mode).successor (activated state query mode ordinal).state) :=
  ((facade state query mode).readoutAt_factorizes (activated state query mode ordinal) .supply).2

theorem consume_account : (consume state query mode 1).account=state.postAccount query mode := by
  rw [(consume state query mode 1).actualAccount]
  rfl
end Runtime

def State.next {plan : Plan} (state : State plan) (query : Query) (mode : Mode) : State plan :=
  ⟨state.session.next query mode,(Runtime.consume state query mode 1).account⟩

def State.transition {plan : Plan} (state : State plan) (query : Query) (mode : Mode) :
    (Financial.Family.process sources).Run state.account.current (state.next query mode).account.current := by
  change (Financial.Family.process sources).Run state.account.current (Runtime.consume state query mode 1).account.current
  rw [Runtime.consume_account]
  exact (Financial.Family.visitRun sources (state.session.input query mode) 0 state.account).concatRuns
    (Financial.Family.process sources)
    (Financial.Family.visitRun sources (state.session.input query mode) 1 (state.preAccount query mode))

theorem State.every_original_issued_claim_keeps_its_identity {plan : Plan}
    (state : State plan) (query : Query) (mode : Mode) :
    state.account.current.slots.map (Financial.Family.slotClaim sources) <+:
      (state.next query mode).account.current.slots.map (Financial.Family.slotClaim sources) := by
  change _ <+: (Runtime.consume state query mode 1).account.current.slots.map _
  rw [Runtime.consume_account]
  exact (Financial.Family.consumeOrigins_preserves_original_claims sources _ _).trans
    (Financial.Family.consumeOrigins_preserves_original_claims sources _ _)

def State.migrate {plan : Plan} (state : State plan) (query : Query) (mode : Mode)
    (index : Nat) (slot : ObligationSlot (Financial.Family.vocabulary sources))
    (present : state.account.current.slots[index]?=some slot) :
    Financial.Family.Migration.Follow sources (state.transition query mode) index slot :=
  Financial.Family.Migration.follow sources (state.transition query mode) index slot present

def run {plan : Plan} (initial : State plan) (requests : Nat → Query×Mode) : Nat → State plan
  | 0 => initial
  | n+1 => (run initial requests n).next (requests n).1 (requests n).2

theorem run_material_is_the_same_source_generated_recursion {plan : Plan}
    (initial : State plan) (requests : Nat → Query×Mode) (n : Nat) :
    (run initial requests n).session=Supply.run initial.session requests n := by
  induction n with
  | zero => rfl
  | succ n ih => change (run initial requests n).session.next _ _=_;rw [ih];rfl

def run_financial_path {plan : Plan} (initial : State plan) (requests : Nat → Query×Mode) (n : Nat) :
    (Financial.Family.process sources).Run initial.account.current (run initial requests n).account.current := by
  induction n with
  | zero => exact .nil
  | succ n ih => exact ih.concatRuns _ ((run initial requests n).transition _ _)

theorem run_keeps_every_original_financial_admission {plan : Plan}
    (initial : State plan) (requests : Nat → Query×Mode) (n : Nat) :
    initial.account.current.slots.map (Financial.Family.slotClaim sources) <+:
      (run initial requests n).account.current.slots.map (Financial.Family.slotClaim sources) := by
  induction n with
  | zero => exact List.prefix_rfl
  | succ n ih => exact ih.trans ((run initial requests n).every_original_issued_claim_keeps_its_identity _ _)
end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Finance
