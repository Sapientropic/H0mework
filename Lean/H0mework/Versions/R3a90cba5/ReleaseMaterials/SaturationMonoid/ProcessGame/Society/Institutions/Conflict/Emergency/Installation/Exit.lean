import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency.Installation.Lifecycle

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency.Installation.Opening

open Capitalism.Universal.Source.Program Capitalism.Universal.Root
open Capitalism.Universal.Exit
open PublicFunction PublicFunction.Mandate

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

local notation "Raw" => RawCurrent Party Good (State Party Technology) Instrument
local notation "Req" => Request Party Good Port (State Party Technology) Instrument

def IndependentNecessity (active : RawLaw Party Good Port (State Party Technology) Instrument)
    (current : Raw) (bearer : Party) (instruction : Req) : Prop :=
  instruction.signer = bearer ∧ instruction.consents = [] ∧
    Necessity.UseMatches instruction.operation bearer (active.necessities current bearer) .necessity ∧
    active.Valid current instruction

instance (active : RawLaw Party Good Port (State Party Technology) Instrument)
    (current : Raw) (bearer : Party) (instruction : Req) :
    Decidable (IndependentNecessity active current bearer instruction) := by
  unfold IndependentNecessity
  infer_instance

def independentOffersAt (active : RawLaw Party Good Port (State Party Technology) Instrument)
    (current : Raw) (actions : Raw → List Req) (bearer : Party) : List Req :=
  (actions current).filter fun instruction => decide (IndependentNecessity active current bearer instruction)

variable {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}
  {first second : Party} {unit : Good}
  {initial : RawCurrent Party Good (State Party Technology) Instrument}
  {original : RawEvent Party Good Port (State Party Technology) Instrument}
  {service : List (RawEvent Party Good Port (State Party Technology) Instrument)}
  (opening : Opening base scope first second unit initial original service)

def afterReview : Raw :=
  (law base opening.installedScope).next opening.term.cell.target opening.reviewWord

abbrev SelfFunded (bearer : Party) (instruction : Req) : Prop :=
  IndependentNecessity (law base opening.installedScope) opening.afterReview bearer instruction

/-- The exact independent necessary-use options in the original action
menu after both review payments. The issuer and first reviewer cannot
act in place of the person taking the exit. -/
def independentOffers (actions : Raw → List Req) (bearer : Party) : List Req :=
  independentOffersAt (law base opening.installedScope) opening.afterReview actions bearer

theorem independent_offers_exact (actions : Raw → List Req) (bearer : Party) (instruction : Req) :
    instruction ∈ opening.independentOffers actions bearer ↔
      instruction ∈ actions opening.afterReview ∧ opening.SelfFunded bearer instruction := by
  simp only [independentOffers, independentOffersAt, List.mem_filter, decide_eq_true_eq]

variable (actions : RawCurrent Party Good (State Party Technology) Instrument →
    List (Request Party Good Port (State Party Technology) Instrument))
  (budget : Nat)
  (positive : ∀ slot ∈ scope.task.slots, ∃ item ∈ slot.goods, 0 < item.2)

theorem after_review_is_the_original_physical_successor :
    (opening.actual actions budget positive).after = opening.afterReview := by
  have exact := opening.actual_reviews_are_the_registered_paid_word actions budget positive
  rw [(opening.actual actions budget positive).after_exact, exact.1, exact.2]
  rfl

/-- Consume a computed independent exit at its literal next native
position. The preceding review remains the same original execution. -/
theorem selected_independent_offer_pays_on_the_original_following_visit
    (bearer : Party) (instruction : Req) (selected : instruction ∈ opening.independentOffers actions bearer) :
    let native := (opening.source actions budget positive).source
    let later := opening.inputs ++ [[instruction]]
    let paid := OutstandingSource.History.actualExecution native later (service.length + 2)
    paid.before = opening.afterReview ∧ paid.submitted = [instruction] ∧
      (law base opening.installedScope).actualDebit paid.before instruction =
        locate bearer ((law base opening.installedScope).necessities paid.before bearer) ∧
      paid.after = ProgrammeSource.rawCurrent (OutstandingSource.History.input native later)
        (ProgrammeHistory.visitAt (OutstandingSource.History.input native later) (service.length + 4)).current := by
  dsimp only
  let native := (opening.source actions budget positive).source
  let later := opening.inputs ++ [[instruction]]
  let visit := service.length + 3
  have old : OutstandingSource.History.currentAt native opening.inputs visit = opening.afterReview :=
    (opening.actual actions budget positive).root_next_exact.symm.trans
      (opening.after_review_is_the_original_physical_successor actions budget positive)
  have unchanged := OutstandingSource.History.extending_inputs_preserves_its_executed_prefix
    native opening.inputs [[instruction]] visit (by simp [visit, inputs])
  have ready : OutstandingSource.History.currentAt native later visit = opening.afterReview := by
    rw [(OutstandingSource.History.actual_frame native later visit).1, unchanged,
      ← (OutstandingSource.History.actual_frame native opening.inputs visit).1]
    exact old
  have sameIndex : opening.inputs.length = service.length + 1 := by simp [inputs]
  have inside : service.length + 1 < later.length := by simp [later, sameIndex]
  have posted := OutstandingSource.History.scheduled_input_is_actual native later (service.length + 1) inside
  have exact : later[service.length + 1] = [instruction] := by
    simp [later, ← sameIndex]
  have conditions := (opening.independent_offers_exact actions bearer instruction).mp selected
  have operation := (Necessity.useMatches_iff _ _ _ _).mp conditions.2.2.2.1
  refine ⟨ready, posted.trans exact, ?_, (OutstandingSource.History.actualExecution native later _).root_next_exact⟩
  change (law base opening.installedScope).actualDebit
    (OutstandingSource.History.currentAt native later visit) instruction =
      locate bearer ((law base opening.installedScope).necessities
        (OutstandingSource.History.currentAt native later visit) bearer)
  rw [ready, RawLaw.actualDebit, if_pos conditions.2.2.2.2, RawLaw.debit, operation]

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency.Installation.Opening
