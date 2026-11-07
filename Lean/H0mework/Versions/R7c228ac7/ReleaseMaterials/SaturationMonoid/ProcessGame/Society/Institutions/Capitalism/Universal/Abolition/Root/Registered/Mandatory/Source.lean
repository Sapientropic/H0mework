import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.ReviewPhase.Dispatch
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Control.Dispatch
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Mandatory.CurrentScope.Control

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Mandatory

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (current : Physical.Cursor Party Good Port Technology Instrument)

abbrev state := Physical.stateAt input depth count prefixLimit renewalLimit current.past

inductive Reason : Type
  | migration (plan : Material.Migration.Plan input (Actual.origin input depth count) (state input depth count prefixLimit renewalLimit current).raw
      (Actual.members input depth count) prefixLimit renewalLimit)
      (selected : Actual.select input depth count prefixLimit renewalLimit (state input depth count prefixLimit renewalLimit current) = .accepted plan)
      (source : Actual.decide input depth count prefixLimit renewalLimit (state input depth count prefixLimit renewalLimit current) =
        .action (.migration plan selected))
  | repair (cause : Actual.Cause input depth count prefixLimit renewalLimit (state input depth count prefixLimit renewalLimit current))
      (attempt : Repair.AttemptAt input depth count (state input depth count prefixLimit renewalLimit current).raw
        (cause.focus input depth count prefixLimit renewalLimit) (state input depth count prefixLimit renewalLimit current).remaining)
      (source : Actual.decide input depth count prefixLimit renewalLimit (state input depth count prefixLimit renewalLimit current) =
        .action (.repair cause attempt))
  | firstRenewal (word : RawEvent Party Good Port Technology Instrument)
      (phase : (state input depth count prefixLimit renewalLimit current).phase = .renewal word)
      (checked : Review.Guarded.Checks input (Actual.origin input depth count) (state input depth count prefixLimit renewalLimit current).raw
        (Actual.members input depth count) word)
      (source : Actual.decide input depth count prefixLimit renewalLimit (state input depth count prefixLimit renewalLimit current) =
        .action (.renewal word phase checked))
      (unpaidBoundary : ¬ PaidBoundary input depth count prefixLimit renewalLimit current)

inductive Permission : Type
  | blocked (obstruction : Actual.ExactObstruction input depth count prefixLimit renewalLimit (state input depth count prefixLimit renewalLimit current))
      (source : Actual.decide input depth count prefixLimit renewalLimit (state input depth count prefixLimit renewalLimit current) = .blocked obstruction)
  | completedRenewal (word : RawEvent Party Good Port Technology Instrument)
      (phase : (state input depth count prefixLimit renewalLimit current).phase = .renewal word)
      (checked : Review.Guarded.Checks input (Actual.origin input depth count) (state input depth count prefixLimit renewalLimit current).raw
        (Actual.members input depth count) word)
      (source : Actual.decide input depth count prefixLimit renewalLimit (state input depth count prefixLimit renewalLimit current) =
        .action (.renewal word phase checked))
      (paidBoundary : PaidBoundary input depth count prefixLimit renewalLimit current)

inductive Selection : Type
  | mandatory (reason : Reason input depth count prefixLimit renewalLimit current)
  | admitted (permission : Permission input depth count prefixLimit renewalLimit current)

def select : Selection input depth count prefixLimit renewalLimit current :=
  match source : Actual.decide input depth count prefixLimit renewalLimit (state input depth count prefixLimit renewalLimit current) with
  | .blocked obstruction => .admitted (.blocked obstruction source)
  | .action (.migration plan selected) => .mandatory (.migration plan selected source)
  | .action (.repair cause attempt) => .mandatory (.repair cause attempt source)
  | .action (.renewal word phase checked) =>
      if paid : PaidBoundary input depth count prefixLimit renewalLimit current then
        .admitted (.completedRenewal word phase checked source paid)
      else .mandatory (.firstRenewal word phase checked source paid)

variable (proposal : Compile.RawInput Party Good Port Technology Instrument)

structure MigrationAt where
  private mk ::
  pair : RawEvent Party Good Port Technology Instrument × RawEvent Party Good Port Technology Instrument
  raw_exact : proposal = .migrate pair
  checked : Actual.Migration.Checks input (Actual.origin input depth count)
    (state input depth count prefixLimit renewalLimit current).raw (Actual.members input depth count) pair

def migration? : Option (MigrationAt input depth count prefixLimit renewalLimit current proposal) :=
  match proposal with
  | .migrate pair =>
      match Actual.Migration.inspect input (Actual.origin input depth count)
          (state input depth count prefixLimit renewalLimit current).raw (Actual.members input depth count) pair with
      | .accepted checked => some ⟨pair, rfl, checked⟩
      | .refused _ => none
  | _ => none

/-- Only the current phase and the proposed finite pair are inspected.
The native search is not rerun before accepting a checked replacement. -/
def priorityMigration? : Option (MigrationAt input depth count prefixLimit renewalLimit current proposal) :=
  match proposal with
  | .migrate pair => if FirstRenewalDue input depth count prefixLimit renewalLimit current then none
      else migration? input depth count prefixLimit renewalLimit current (.migrate pair)
  | _ => none

abbrev ReviewResult := Σ context : ReviewPhase.ContextAt input,
  ReviewPhase.Decision context.source depth count prefixLimit renewalLimit
    (context.reviewEpoch depth count prefixLimit renewalLimit) context.fee

def reviewDispatch (review : Option (ReviewPhase.ContextAt input) := none) :
    Option (ReviewResult input depth count prefixLimit renewalLimit) :=
  match review with
  | none => none
  | some context => some ⟨context, context.dispatch depth count prefixLimit renewalLimit current⟩

def ordinaryRaw : Compile.RawInput Party Good Port Technology Instrument :=
  match priorityMigration? input depth count prefixLimit renewalLimit current proposal with
  | some _ => proposal
  | none => match select input depth count prefixLimit renewalLimit current with
    | .mandatory _ => .advance
    | .admitted _ => proposal

def ordinaryDeferred : Option (Compile.RawInput Party Good Port Technology Instrument) :=
  match priorityMigration? input depth count prefixLimit renewalLimit current proposal with
  | some _ => none
  | none => match select input depth count prefixLimit renewalLimit current, proposal with
    | .mandatory _, .advance => none
    | .mandatory _, _ => some proposal
    | .admitted _, _ => none

/-- An explicitly configured legacy epoch retains its original priority.
Otherwise the first consumed review registration owns its pending source
choices. No new proposal supplies or resets its fee, code, or epoch. -/
def executionRaw (review : Option (ReviewPhase.ContextAt input) := none) :
    Compile.RawInput Party Good Port Technology Instrument :=
  match review with
  | none =>
    match ReviewSource.Control.action input depth count prefixLimit renewalLimit current with
    | .execute raw => raw
    | .obstructed => match proposal with
      | .primitive request => .primitive request
      | _ => .stopReview
    | .inactive | .materialPaid => CurrentScope.filterRaw input depth count prefixLimit renewalLimit current
        proposal (ordinaryRaw input depth count prefixLimit renewalLimit current proposal)

  | some context =>
      match context.dispatch depth count prefixLimit renewalLimit current with
      | .execute raw => raw
      | .obstructed _ => match proposal with
        | .primitive request => .primitive request
        | _ => .stopReview
      | .released =>
        if FirstRenewalDue input depth count prefixLimit renewalLimit current then .advance
        else match priorityMigration? input depth count prefixLimit renewalLimit current proposal with
        | some _ => proposal
        | none => match select input depth count prefixLimit renewalLimit current with
          | .mandatory _ => .advance
          | .admitted _ => proposal

def deferred (review : Option (ReviewPhase.ContextAt input) := none) :
    Option (Compile.RawInput Party Good Port Technology Instrument) :=
  match review with
  | none =>
    match ReviewSource.Control.action input depth count prefixLimit renewalLimit current with
    | .execute _ => some proposal
    | .obstructed => match proposal with
      | .primitive _ => none
      | _ => some proposal
    | .inactive | .materialPaid => CurrentScope.filterDeferred input depth count prefixLimit renewalLimit current
        proposal (ordinaryDeferred input depth count prefixLimit renewalLimit current proposal)

  | some context =>
      match context.dispatch depth count prefixLimit renewalLimit current with
      | .execute _ => some proposal
      | .obstructed _ => match proposal with
        | .primitive _ => none
        | _ => some proposal
      | .released =>
        match priorityMigration? input depth count prefixLimit renewalLimit current proposal with
        | some _ => none
        | none => match select input depth count prefixLimit renewalLimit current, proposal with
          | .mandatory _, .advance => none
          | .mandatory _, _ => some proposal
          | .admitted _, _ => none

structure Report (review : Option (ReviewPhase.ContextAt input) := none) where
  private mk ::
  originalProposal : Compile.RawInput Party Good Port Technology Instrument
  original_exact : originalProposal = proposal
  selection : Selection input depth count prefixLimit renewalLimit current
  source_exact : selection = select input depth count prefixLimit renewalLimit current
  migrationOverride : Option (MigrationAt input depth count prefixLimit renewalLimit current proposal)
  override_exact : migrationOverride = priorityMigration? input depth count prefixLimit renewalLimit current proposal
  reviewResult : Option (ReviewResult input depth count prefixLimit renewalLimit)
  review_exact : reviewResult = reviewDispatch input depth count prefixLimit renewalLimit current (review := review)
  implicitReport : ReviewSource.Control.ReportAt input depth count prefixLimit renewalLimit current
  implicit_exact : implicitReport = ReviewSource.Control.report input depth count prefixLimit renewalLimit current
  currentScope : CurrentScope.View input depth count prefixLimit renewalLimit current
  scope_exact : currentScope = CurrentScope.inspect input depth count prefixLimit renewalLimit current
  selectedRaw : Compile.RawInput Party Good Port Technology Instrument
  selected_exact : selectedRaw = executionRaw input depth count prefixLimit renewalLimit current proposal (review := review)
  deferredProposal : Option (Compile.RawInput Party Good Port Technology Instrument)
  deferred_exact : deferredProposal = deferred input depth count prefixLimit renewalLimit current proposal (review := review)

def produce (review : Option (ReviewPhase.ContextAt input) := none) :
    Report input depth count prefixLimit renewalLimit current proposal (review := review) :=
  ⟨proposal, rfl, select input depth count prefixLimit renewalLimit current, rfl,
    priorityMigration? input depth count prefixLimit renewalLimit current proposal, rfl,
    reviewDispatch input depth count prefixLimit renewalLimit current (review := review), rfl,
    ReviewSource.Control.report input depth count prefixLimit renewalLimit current, rfl,
    CurrentScope.inspect input depth count prefixLimit renewalLimit current, rfl,
    executionRaw input depth count prefixLimit renewalLimit current proposal (review := review), rfl,
    deferred input depth count prefixLimit renewalLimit current proposal (review := review), rfl⟩

def executionCursor (review : Option (ReviewPhase.ContextAt input) := none) :=
  Physical.receive current (executionRaw input depth count prefixLimit renewalLimit current proposal (review := review))

theorem original_past_and_proposal_are_not_rewritten :
    (executionCursor input depth count prefixLimit renewalLimit current proposal).past = current.past ∧
      (∀ raw, deferred input depth count prefixLimit renewalLimit current proposal = some raw → raw = proposal) := by
  constructor
  · rfl
  · intro raw stored
    dsimp only [deferred] at stored
    split at stored
    · cases stored; rfl
    · split at stored <;> simp_all
    · unfold CurrentScope.filterDeferred at stored
      split at stored
      · unfold ordinaryDeferred at stored
        split at stored
        · cases stored
        · split at stored <;> simp_all
      · cases proposal <;> simp_all
    · unfold CurrentScope.filterDeferred at stored
      split at stored
      · unfold ordinaryDeferred at stored
        split at stored
        · cases stored
        · split at stored <;> simp_all
      · cases proposal <;> simp_all

theorem an_unregistered_past_keeps_the_ordinary_source_route
    (absent : ReviewSource.Control.recovered input depth count prefixLimit renewalLimit current = none) :
    executionRaw input depth count prefixLimit renewalLimit current proposal =
      CurrentScope.filterRaw input depth count prefixLimit renewalLimit current
        proposal (ordinaryRaw input depth count prefixLimit renewalLimit current proposal) ∧
      deferred input depth count prefixLimit renewalLimit current proposal =
        CurrentScope.filterDeferred input depth count prefixLimit renewalLimit current
          proposal (ordinaryDeferred input depth count prefixLimit renewalLimit current proposal) := by
  have idle := ReviewSource.Control.without_an_actual_registration_the_ordinary_route_is_unchanged
    input depth count prefixLimit renewalLimit current absent
  simp only [executionRaw, deferred, idle, and_self]

theorem every_proposal_consumes_the_same_registered_opcode
    (raw : Compile.RawInput Party Good Port Technology Instrument)
    (source : ReviewSource.Control.action input depth count prefixLimit renewalLimit current = .execute raw) :
    executionRaw input depth count prefixLimit renewalLimit current proposal = raw ∧
      deferred input depth count prefixLimit renewalLimit current proposal = some proposal := by
  simp only [executionRaw, deferred, source, and_self]

theorem the_original_stop_cannot_fall_back_to_automatic_power
    (source : ReviewSource.Control.action input depth count prefixLimit renewalLimit current = .obstructed) :
    executionRaw input depth count prefixLimit renewalLimit current .advance = .stopReview := by
  simp only [executionRaw, source]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Mandatory
