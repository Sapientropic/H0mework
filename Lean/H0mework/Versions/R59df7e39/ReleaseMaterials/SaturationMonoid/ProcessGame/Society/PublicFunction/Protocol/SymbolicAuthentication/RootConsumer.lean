import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Runtime

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RootConsumer

open Distributed Institutions.Capitalism.Universal.Source.Program
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

inductive ReceptionData (Wire : Type) where
  | blocked
  | available (state : ReceiverStateData Wire)
  deriving DecidableEq

variable (source : Source Party Good Port Technology Instrument)
  (interface : Interface source.code) (receiver : Fin source.code.sites)
  (incoming : Nat → Option (Envelope source.code))

abbrev Reception := ReceptionData (Envelope source.code)

def fromOutcome : source.code.Outcome source.reference → Reception source
  | .blocked _ => .blocked
  | .selected choice => .available
      (run source.code interface choice.policy.policy (source.code.historyCurrent source.history)
        source.events receiver incoming source.events.length)

def generate : Reception source := fromOutcome source interface receiver incoming source.answer

/-- The independent consumer reads the existing installed synthesis face. It
adds no sibling process, new root, or authority interpretation of a receipt. -/
def rooted : Reception source :=
  match (Distributed.Runtime.facade source).readoutAt
      (Distributed.Runtime.activated source (source.history.length + 1)) .synthesis with
  | .inl outcome => fromOutcome source interface receiver incoming outcome.2
  | .inr impossible => nomatch impossible

theorem rooted_eq_generated : rooted source interface receiver incoming = generate source interface receiver incoming := by
  rfl

/-- Availability is derived from the original compiler's successful branch;
blocked output cannot be consumed as an available authenticated history. -/
theorem available_has_paid_source (state : ReceiverState source.code)
    (available : generate source interface receiver incoming = .available state) :
    ∃ choice : source.code.Selection source.reference,
      source.answer = .selected choice ∧
      state = run source.code interface choice.policy.policy (source.code.historyCurrent source.history)
        source.events receiver incoming source.events.length ∧
      (source.actualExecution source.history.length).submitted =
        (source.code.executed choice.policy.policy (source.history, source.events)).word ∧
      ServiceAdequate source.code.law (source.actualExecution source.history.length).before source.code.task
        (source.actualExecution source.history.length).submitted ∧
      source.currentAt (source.history.length + 2) = source.code.law.next
        (source.code.historyCurrent source.history)
        (source.code.executed choice.policy.policy (source.history, source.events)).word ∧
      source.code.verify source.reference choice.policy.policy = true := by
  unfold generate fromOutcome at available
  split at available
  · contradiction
  · rename_i choice generated
    have same := ReceptionData.available.inj available
    have paid := source.selected_plan_is_paid_on_its_own_root choice generated
    exact ⟨choice, generated, same.symm, paid⟩

theorem existing_root_ledger_and_next_are_preserved :
    let actual := Distributed.Runtime.activated source (source.history.length + 1)
    rooted source interface receiver incoming = generate source interface receiver incoming ∧
      HEq ((Distributed.Runtime.facade source).readoutAt actual .synthesis)
        (actual.tick.generated.projectionOutcome (.component ())) ∧
      HEq actual.tick.generated.wholeLedgerWriteBack
        (actual.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt actual.current.visit.current) ∧
      actual.tick.nextCurrent = (Distributed.Runtime.facade source).process.stateAt
        ((Distributed.Runtime.facade source).process.successor actual.state) := by
  have facts := (Distributed.Runtime.facade source).readoutAt_factorizes
    (Distributed.Runtime.activated source (source.history.length + 1)) .synthesis
  exact ⟨rooted_eq_generated source interface receiver incoming,
    facts.2.2.2.1, facts.2.2.1, facts.2.2.2.2⟩

theorem every_rooted_receipt_has_an_admitted_actual_send
    (state : ReceiverState source.code)
    (available : rooted source interface receiver incoming = .available state)
    (receipt : Receipt source.code) (present : receipt ∈ state.receipts) :
    ∃ choice : source.code.Selection source.reference,
      source.answer = .selected choice ∧
      (source.history, source.events) ∈ source.code.scenarios ∧
      verify source.code interface choice.policy.policy (source.code.historyCurrent source.history)
        source.events receipt.wire = true ∧
      receipt.wire.recipient = receiver ∧ receipt.wire.occurrence < receipt.delivery ∧
      receipt.delivery < source.events.length ∧
      deliveredAt source.code source.events receipt.delivery receipt.wire.serial = true := by
  rw [rooted_eq_generated] at available
  obtain ⟨choice, generated, same, _⟩ :=
    available_has_paid_source source interface receiver incoming state available
  subst state
  exact ⟨choice, generated, source.admitted,
    receipts_authenticated source.code interface choice.policy.policy
      (source.code.historyCurrent source.history) source.events receiver incoming
      source.events.length receipt present⟩

theorem blocked_has_no_available_reception
    (blocked : ∀ choice : source.code.Selection source.reference, source.answer ≠ .selected choice)
    (state : ReceiverState source.code) : rooted source interface receiver incoming ≠ .available state := by
  intro available
  rw [rooted_eq_generated] at available
  obtain ⟨choice, generated, _⟩ := available_has_paid_source source interface receiver incoming state available
  exact blocked choice generated

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RootConsumer
