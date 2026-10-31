import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Word

/-! Source checks for a reproduced productive control relation.  Material
routes use actual debit/credit legs, including productive conversions.
Operator, private controller and recipient remain distinct source roles. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl

open Program
universe u
variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)
  (current : RawCurrent Party Good Technology Instrument)
  (word : RawEvent Party Good Port Technology Instrument)

abbrev Cell := Party × Good

structure RouteLeg where
  item : OriginalItem law current word
  destination : Cell (Party := Party) (Good := Good)

/-- Edges require actual debit and actual credit.  Co-mention does not
produce an economic connection.  Indices strictly advance along a route. -/
def Follows : Cell (Party := Party) (Good := Good) → Nat →
    List (RouteLeg law current word) → Cell (Party := Party) (Good := Good) → Nat → Prop
  | origin, lower, [], target, upper => origin = target ∧ lower ≤ upper
  | origin, lower, leg :: tail, target, upper =>
      lower ≤ leg.item.val.index ∧
      law.Valid leg.item.val.before leg.item.val.request ∧
      0 < flowAt (law.actualDebit leg.item.val.before leg.item.val.request) origin.1 origin.2 ∧
      0 < flowAt (law.actualCredit leg.item.val.before leg.item.val.request)
        leg.destination.1 leg.destination.2 ∧
      Follows leg.destination (leg.item.val.index + 1) tail target upper

instance (origin : Cell (Party := Party) (Good := Good)) (lower : Nat)
    (route : List (RouteLeg law current word)) (target : Cell (Party := Party) (Good := Good))
    (upper : Nat) : Decidable (Follows law current word origin lower route target upper) := by
  induction route generalizing origin lower with
  | nil => unfold Follows; infer_instance
  | cons head tail ih =>
      unfold Follows
      letI := ih head.destination (head.item.val.index + 1)
      infer_instance

/-- Private authority is a phase of actual source permissions, not a
permanent interpretation of a port name. -/
def PrivatePhase (state : RawCurrent Party Good Technology Instrument)
    (port : Port) (recipient : Party) : Prop :=
  law.allowed state.technology port (law.controller state.technology port) = true ∧
  law.allowed state.technology port recipient = false

instance (state : RawCurrent Party Good Technology Instrument) (port : Port) (recipient : Party) :
    Decidable (PrivatePhase law state port recipient) := by unfold PrivatePhase; infer_instance

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] in
theorem private_phase_separates_controller (state : RawCurrent Party Good Technology Instrument)
    (port : Port) (recipient : Party) (phase : PrivatePhase law state port recipient) :
    law.controller state.technology port ≠ recipient := by
  intro same
  unfold PrivatePhase at phase
  rw [same] at phase
  exact Bool.noConfusion (phase.1.symm.trans phase.2)

/-- The finite proposal consists of addresses in the original execution.
The checker derives production, necessary use and the current/next phases. -/
structure CircuitProposal where
  production : OriginalItem law current word
  necessity : OriginalItem law current word
  operator : Party
  recipient : Party
  port : Port
  outputGood : Good
  necessityGood : Good
  delivery : List (RouteLeg law current word)

namespace CircuitProposal
variable (proposal : CircuitProposal law current word)

def controller : Party := law.controller proposal.production.val.before.technology proposal.port

def Produced : Prop :=
  match proposal.production.val.request.operation with
  | .produce operator => operator = proposal.operator ∧
      law.Valid proposal.production.val.before proposal.production.val.request ∧
      proposal.port ∈ law.requiredPorts proposal.production.val.before proposal.production.val.request ∧
      0 < flowAt (law.actualCredit proposal.production.val.before proposal.production.val.request)
        proposal.operator proposal.outputGood
  | _ => False

def NecessityPaid : Prop :=
  match proposal.necessity.val.request.operation with
  | .use recipient goods .necessity => recipient = proposal.recipient ∧
      law.Valid proposal.necessity.val.before proposal.necessity.val.request ∧
      0 < amount Good goods proposal.necessityGood
  | _ => False

def Checks : Prop :=
  proposal.Produced law current word ∧
  proposal.NecessityPaid law current word ∧
  PrivatePhase law proposal.production.val.before proposal.port proposal.recipient ∧
  Follows law current word (proposal.operator, proposal.outputGood)
    (proposal.production.val.index + 1) proposal.delivery
    (proposal.recipient, proposal.necessityGood) proposal.necessity.val.index ∧
  PrivatePhase law (law.next current word) proposal.port proposal.recipient ∧
  proposal.port ∈ law.requiredPorts (law.next current word) proposal.production.val.request

instance : Decidable (proposal.Produced law current word) := by
  unfold Produced
  cases proposal.production.val.request.operation <;> infer_instance

instance : Decidable (proposal.NecessityPaid law current word) := by
  unfold NecessityPaid
  cases proposal.necessity.val.request.operation with
  | use _ _ purpose => cases purpose <;> infer_instance
  | _ => infer_instance

instance : Decidable (proposal.Checks law current word) := by unfold Checks; infer_instance
end CircuitProposal

structure ReproducedControl where
  private mk ::
  proposal : CircuitProposal law current word
  checked : proposal.Checks law current word

def compileCircuit (proposal : CircuitProposal law current word) :
    Option (ReproducedControl law current word) :=
  if checked : proposal.Checks law current word then some ⟨proposal, checked⟩ else none

theorem compileCircuit_success (proposal : CircuitProposal law current word)
    (checked : proposal.Checks law current word) :
    ∃ circuit, compileCircuit law current word proposal = some circuit :=
  ⟨⟨proposal, checked⟩, dif_pos checked⟩

namespace ReproducedControl
variable (circuit : ReproducedControl law current word)

def port := circuit.proposal.port

def recipient := circuit.proposal.recipient

def owner := circuit.proposal.controller law current word

def nextOwner := law.controller (law.next current word).technology circuit.proposal.port

omit [DecidableEq Port] in
theorem production_is_original_control_use :
    law.Valid circuit.proposal.production.val.before circuit.proposal.production.val.request ∧
    circuit.proposal.port ∈ law.requiredPorts circuit.proposal.production.val.before
      circuit.proposal.production.val.request := by
  have paid := circuit.checked.1
  unfold CircuitProposal.Produced at paid
  split at paid
  · exact ⟨paid.2.1, paid.2.2.1⟩
  all_goals contradiction

omit [DecidableEq Port] in
theorem actual_necessary_life :
    law.Valid circuit.proposal.necessity.val.before circuit.proposal.necessity.val.request ∧
    ∃ goods, circuit.proposal.necessity.val.request.operation =
      .use circuit.proposal.recipient goods .necessity ∧
      goods = law.necessities circuit.proposal.necessity.val.before circuit.proposal.recipient ∧
      0 < amount Good goods circuit.proposal.necessityGood := by
  have paid := circuit.checked.2.1
  unfold CircuitProposal.NecessityPaid at paid
  cases operation : circuit.proposal.necessity.val.request.operation with
  | use bearer goods purpose =>
      cases purpose <;> simp only [operation] at paid
      case necessity =>
        rcases paid with ⟨rfl, accepted, positive⟩
        have guarded := accepted.2.2.1
        simp only [RawLaw.ClaimGuard, operation] at guarded
        exact ⟨accepted, goods, rfl, guarded, positive⟩
  | _ => simp only [operation] at paid

omit [DecidableEq Port] in
theorem source_and_next_have_distinct_roles :
    circuit.owner law current word ≠ circuit.recipient law current word ∧
    circuit.nextOwner law current word ≠ circuit.recipient law current word :=
  ⟨private_phase_separates_controller law _ _ _ circuit.checked.2.2.1,
    private_phase_separates_controller law _ _ _ circuit.checked.2.2.2.2.1⟩

def activeAt (item : OriginalItem law current word) : Bool :=
  decide (PrivatePhase law item.val.before circuit.proposal.port circuit.proposal.recipient)
end ReproducedControl

/-- Each instruction reads its own actual permission phase. -/
def generatedFamily (circuits : List (ReproducedControl law current word))
    (item : OriginalItem law current word) : List Port :=
  circuits.filterMap (fun circuit =>
    if circuit.activeAt law current word item then some circuit.proposal.port else none)

#print axioms compileCircuit
#print axioms ReproducedControl.actual_necessary_life

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl
