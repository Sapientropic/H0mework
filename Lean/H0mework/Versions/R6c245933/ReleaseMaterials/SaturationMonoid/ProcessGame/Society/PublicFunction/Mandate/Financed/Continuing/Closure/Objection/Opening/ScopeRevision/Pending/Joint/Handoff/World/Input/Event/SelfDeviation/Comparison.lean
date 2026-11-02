import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.SelfDeviation.Consequences

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 600000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.SelfDeviation.Comparison

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
open Future.Expiry.Progress
noncomputable section

/-- The declared reader receives the complete actual path and source response,
without a baseline/deviation label or a caller-supplied successful endpoint. -/
structure Observation (first : Packet) where
  private mk ::
  front : Packet
  incoming : Evolution first front
  trace : Trace front.2
  original : trace = Future.Expiry.Progress.Runtime.trace front.2

namespace Observation
variable {first : Packet} (observed : Observation first)
abbrev packet := observed.trace.packet

def native : Evolution first observed.packet := InheritedResponse.combined observed.incoming observed.trace

def inherited := InheritedResponse.classify observed.incoming observed.trace

def originalRow (row : Responsibility.Row first) := InheritedResponse.original observed.incoming observed.trace row

def financeRun := first.2.finance.generated.concatRuns _ (Response.financeAlong observed.native)
def births := Financial.Family.Migration.Exposure.admissions sources observed.financeRun

def operating (party : Bool) (good : Good) := Costs.cost observed.native party (.operating good)
def settlement (party : Bool) (good : Good) := Costs.cost observed.native party (.debtPayment good)
def elapsed (party : Bool) := Costs.cost observed.native party .elapsed

def stock (party : Bool) (good : Good) := (current observed.packet.1 observed.packet.2.inputs).stock party good
def position (side : Financial.Family.Migration.Posting.Side) (party : Bool) (good : Good) := FinancialBalance.positions observed.packet side party good

def quotedNet (party : Bool) (good : Good) := FinancialBalance.quotedNet observed.packet party good

/-- This is an accounting identity in each original good, not a conversion
promise. Settlement cash and its retired claim are not added a second time. -/
def netExpense (party : Bool) (good : Good) :=
  observed.operating party good - FinancialBalance.otherCredits observed.native party good -
    FinancialBalance.issues observed.native .credit party good + FinancialBalance.issues observed.native .debit party good -
    FinancialBalance.assignments observed.native .credit party good

theorem expense_is_the_actual_net_position_change (party : Bool) (good : Good) :
    observed.netExpense party good = FinancialBalance.quotedNet first party good - observed.quotedNet party good := by
  have balance := FinancialBalance.actual_net_balance (first := first) (last := observed.packet) observed.native party good
  unfold netExpense operating quotedNet
  linarith

theorem all_original_rows_and_histories_are_retained (row : Responsibility.Row first) :
    (observed.originalRow row).row.origin = row.origin ∧ row.state.history <+: (observed.originalRow row).state.history ∧
      Nonempty ((observed.originalRow row).native.Run row.origin.initial (observed.originalRow row).state) :=
  InheritedResponse.all_original_rows_have_their_actual_complete_runs (first := first) (last := observed.front) observed.incoming observed.trace row

theorem all_financial_births_cover_the_final_account_once :
    observed.births.map Financial.Family.Migration.Exposure.Birth.index = List.range observed.packet.2.finance.current.slots.length := by
  simpa only [births,ResponsibilityState.empty,List.length_nil,List.range_zero,List.nil_append] using
    Financial.Family.Migration.Exposure.admission_indices sources observed.financeRun

theorem original_financial_identity_and_payments (birth : Financial.Family.Migration.Exposure.Birth sources observed.financeRun) (_member : birth ∈ observed.births) :
    observed.packet.2.finance.current.slots[birth.index]? = some birth.follow.slot ∧
      Financial.Family.slotClaim sources birth.follow.slot = birth.claim ∧ birth.remaining + birth.paid = birth.claim.2.quantity :=
  ⟨birth.actual_slot,birth.original_claim,birth.conservation⟩

theorem material_balance (party : Bool) (good : Good) :
    observed.stock party good + observed.operating party good + observed.settlement party good =
      (current first.1 first.2.inputs).stock party good + Costs.credits observed.native party good :=
  Costs.material_balance observed.native party good

theorem time_is_actual (party : Bool) : observed.elapsed party =
    (current observed.packet.1 observed.packet.2.inputs).clock - (current first.1 first.2.inputs).clock :=
  Costs.elapsed_exact observed.native party

theorem response_is_its_original_root_answer_and_next :
    observed.trace = Future.Expiry.Progress.Runtime.trace observed.front.2 ∧
    HEq (Future.Expiry.Progress.Runtime.activated observed.front.2 (Future.Expiry.Progress.Runtime.ordinal observed.front.2)).tick.generated.wholeLedgerWriteBack
      ((Future.Expiry.Progress.Runtime.activated observed.front.2 (Future.Expiry.Progress.Runtime.ordinal observed.front.2)).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (Future.Expiry.Progress.Runtime.activated observed.front.2 (Future.Expiry.Progress.Runtime.ordinal observed.front.2)).current.visit.current) ∧
    (Future.Expiry.Progress.Runtime.activated observed.front.2 (Future.Expiry.Progress.Runtime.ordinal observed.front.2)).tick.nextCurrent =
      (Future.Expiry.Progress.Runtime.facade observed.front.2).process.stateAt
        ((Future.Expiry.Progress.Runtime.facade observed.front.2).process.successor
          (Future.Expiry.Progress.Runtime.activated observed.front.2 (Future.Expiry.Progress.Runtime.ordinal observed.front.2)).state) := by
  have factor := (Future.Expiry.Progress.Runtime.facade observed.front.2).readoutAt_factorizes
    (Future.Expiry.Progress.Runtime.activated observed.front.2 (Future.Expiry.Progress.Runtime.ordinal observed.front.2)) (.inr ())
  exact ⟨observed.original,factor.2.2.1,factor.2.2.2.2⟩

end Observation

variable {first : Packet} {epoch : Epoch} (inventory : Inventory epoch) (intent : Input.Intent) (actor : Bool)

def intents : List Input.Intent := [.admission,.challenge,.exit,.revision,.renewal]

theorem every_intent_is_generated (action : Input.Intent) : action ∈ intents := by
  cases action <;> simp [intents]

abbrev Candidate (inventory : Inventory epoch) (actor : Bool) := (action : Input.Intent) × Permit inventory action actor

def candidates (inventory : Inventory epoch) (actor : Bool) : List (Candidate inventory actor) :=
  intents.flatMap fun action => (permits inventory action actor).map (fun permit => ⟨action,permit⟩)

theorem every_generated_permit_is_a_candidate (action : Input.Intent) (permit : Permit inventory action actor)
    (listed : permit ∈ permits inventory action actor) : (⟨action,permit⟩ : Candidate inventory actor) ∈ candidates inventory actor :=
  List.mem_flatMap.mpr ⟨action,every_intent_is_generated action,List.mem_map.mpr ⟨permit,listed,rfl⟩⟩

inductive Branch (inventory : Inventory epoch) (intent : Input.Intent) (actor : Bool) where
  | baseline
  | alternative (candidate : Candidate inventory actor)

def Branch.word : Branch inventory intent actor → List Action
  | .baseline => Input.emit inventory intent
  | .alternative candidate => SelfDeviation.word inventory candidate.1 candidate.2.choice

def observe (earlier : Evolution first ⟨epoch,inventory⟩) (branch : Branch inventory intent actor) : Observation first :=
  let after := World.submit inventory (branch.word inventory intent actor)
  ⟨⟨epoch,after⟩,.append earlier (.submit inventory (branch.word inventory intent actor)),
    Future.Expiry.Progress.Runtime.trace after,rfl⟩

def observeSubmission (earlier : Evolution first ⟨epoch,inventory⟩) (word : List Action) : Observation first :=
  let after := World.submit inventory word
  ⟨⟨epoch,after⟩,.append earlier (.submit inventory word),
    Future.Expiry.Progress.Runtime.trace after,rfl⟩

abbrev baseline (earlier : Evolution first ⟨epoch,inventory⟩) := observe inventory intent actor earlier .baseline
abbrev alternative (earlier : Evolution first ⟨epoch,inventory⟩) (candidate : Candidate inventory actor) :=
  observe inventory intent actor earlier (.alternative candidate)

theorem baseline_is_the_original_emitted_input (earlier : Evolution first ⟨epoch,inventory⟩) :
    (baseline inventory intent actor earlier).front = ⟨epoch,Input.staged inventory intent⟩ := rfl

theorem alternative_is_the_original_permit_response (earlier : Evolution first ⟨epoch,inventory⟩) (candidate : Candidate inventory actor) :
    (alternative inventory intent actor earlier candidate).trace = SelfDeviation.trace candidate.2 ∧
      (alternative inventory intent actor earlier candidate).native = SelfDeviation.path candidate.2 earlier := ⟨rfl,rfl⟩

theorem same_cut_net_difference (earlier : Evolution first ⟨epoch,inventory⟩) (candidate : Candidate inventory actor)
    (party : Bool) (good : Good) :
    (alternative inventory intent actor earlier candidate).netExpense party good - (baseline inventory intent actor earlier).netExpense party good =
      (baseline inventory intent actor earlier).quotedNet party good - (alternative inventory intent actor earlier candidate).quotedNet party good := by
  rw [Observation.expense_is_the_actual_net_position_change,Observation.expense_is_the_actual_net_position_change]
  ring

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.SelfDeviation.Comparison
