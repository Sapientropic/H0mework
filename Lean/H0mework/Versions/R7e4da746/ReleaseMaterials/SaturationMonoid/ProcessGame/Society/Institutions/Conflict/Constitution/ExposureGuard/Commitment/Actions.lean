import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment.Chosen
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment.Publication
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Contract.Defence

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open PublicFunction.Mandate
open Quantities.Execution (endAt endAt_append primitiveScript)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]

local notation "M" => State Party Technology
local notation "C" => Root.Cut Party Good Port M Instrument
local notation "Word" => Reparation.Actual.Script Party Good Port M Instrument
local notation "RawWord" => RawEvent Party Good Port M Instrument

variable {seed : Root.Cut Party Good Port (State Party Technology) Instrument}
  {community : Party → Community}
  {anchor : Reparation.Actual.Script Party Good Port (State Party Technology) Instrument}

/-- The rejected proposal has only its typed disposition. The certified
proposal occupies its original visits and returns their one paid successor. -/
def execute (prior : PaidVisit seed community anchor) (answers : OwnerAnswers seed)
    (rival : Scheduler Party Good Port M Instrument) (person : Party) (word : Word) :
    PlanFailure prior answers word ⊕ PaidVisit seed community anchor :=
  match inspectPlan prior answers word with
  | .inl issue => .inl issue
  | .inr checked => .inr (visitAt prior answers word rival person checked.down word.length)

theorem execute_writes_the_certified_literal_word (prior : PaidVisit seed community anchor)
    (answers : OwnerAnswers seed) (rival : Scheduler Party Good Port M Instrument) (person : Party)
    (word : Word) (approved : Certified prior answers word) :
    execute prior answers rival person word = .inr (advancePaid prior answers word approved.due) := by
  unfold execute
  cases inspectPlan prior answers word with
  | inl issue => exact (issue.refutes _ _ _ approved).elim
  | inr checked =>
    change Sum.inr (visitAt prior answers word rival person checked.down word.length) =
      Sum.inr (advancePaid prior answers word approved.due)
    rw [the_priority_endpoint_is_the_same_original_write prior answers word rival person checked.down]

variable [DecidableEq Technology]
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}
  {control : RawCurrent Party Good (State Party Technology) Instrument → List Party}

theorem certifyExit (prior : GuardedVisit base scope seed community anchor control) {answers : OwnerAnswers seed}
    (chosen : MandateExit.Chosen prior answers) : Certified (paidView prior) answers chosen.word :=
  ⟨of_chosen chosen, chosen.checked.2, chosen.checked.1.1.standing⟩

theorem the_signed_exit_is_written_by_the_reserved_dispatcher
    (prior : GuardedVisit base scope seed community anchor control) {answers : OwnerAnswers seed}
    (chosen : MandateExit.Chosen prior answers) (rival : Scheduler Party Good Port M Instrument) (person : Party) :
    let reached := visitAt (paidView prior) answers chosen.word rival person (certifyExit prior chosen) chosen.word.length
    reached.history = prior.history ++ chosen.word ∧
      HEq reached.state (MandateExit.exercise prior chosen) ∧
      (endAt seed prior.history).raw.clock < (endAt seed reached.history).raw.clock := by
  rw [the_priority_endpoint_is_the_same_original_write (paidView prior) answers chosen.word rival person]
  exact ⟨rfl, HEq.rfl, (MandateExit.an_owner_selected_exit_pays_on_the_same_original_ledger prior chosen).2.1⟩

/-- Reopen ordinary scheduling from the actual paid endpoint by checking
the next offered exit there. This does not rerun any prior receipt. -/
def resume (base : RawLaw Party Good Port Technology Instrument)
    (scope : Scope (Party := Party) (Good := Good) (Port := Port))
    (control : RawCurrent Party Good (State Party Technology) Instrument → List Party)
    (current : PaidVisit seed community anchor) (offer : Word) :
    MandateExit.PlanFailure seed anchor current.history community base scope control offer ⊕
      GuardedVisit base scope seed community anchor control :=
  match MandateExit.inspectPlan seed anchor current.history community base scope control offer with
  | .inl issue => .inl issue
  | .inr ready => .inr ⟨current.history, current.original, current.state, current.origins, ready.down⟩

variable {source : Root.Cut Party Good Port (State Party Technology) Instrument}
  {attackWord : RawEvent Party Good Port (State Party Technology) Instrument}
  (attack : Boundary.AggressionAt source attackWord community)

def DefenceEffect (response floor : RawWord) (reached : PaidVisit seed community anchor) : Prop :=
  ¬ Boundary.Permission attack.after.native.input.law (endAt seed reached.history).raw attack.item.request ∧
    ¬ Nonempty (Boundary.AggressionAt attack.after response community) ∧
    Boundary.ExitFloorAt source (endAt seed reached.history) attack.residents floor

omit [DecidableEq Technology] in
theorem a_reserved_defence_closes_the_original_permission
    (prior : PaidVisit seed community anchor) (answers : OwnerAnswers seed)
    (rival : Scheduler Party Good Port M Instrument) (person : Party) (response floor : RawWord)
    (atAttack : endAt seed prior.history = attack.after) (defended : Boundary.DefenceAt attack response floor)
    (approved : Certified prior answers (primitiveScript response)) :
    let reached := visitAt prior answers (primitiveScript response) rival person approved (primitiveScript response).length
    DefenceEffect attack response floor reached := by
  let reached := visitAt prior answers (primitiveScript response) rival person approved (primitiveScript response).length
  have literal : endAt seed reached.history = Root.terminal attack.after response := by
    rw [show reached.history = prior.history ++ primitiveScript response from
      (a_commitment_completes_at_exactly_its_literal_dispatch_count prior answers _ rival person approved _).mpr le_rfl,
      endAt_append, atAttack]
  change DefenceEffect attack response floor reached
  unfold DefenceEffect
  rw [literal]
  exact ⟨defended.closed, defended.noOverreach, defended.independentExit⟩

omit [DecidableEq Technology] in
def executeDefence (prior : PaidVisit seed community anchor) (answers : OwnerAnswers seed)
    (rival : Scheduler Party Good Port M Instrument) (person : Party) (response floor : RawWord)
    (atAttack : endAt seed prior.history = attack.after) :
    (Boundary.DefenceFailure attack response floor ⊕ PlanFailure prior answers (primitiveScript response)) ⊕
      { reached : PaidVisit seed community anchor // DefenceEffect attack response floor reached } :=
  match Boundary.inspectDefence attack response floor with
  | .refused issue => .inl (.inl issue)
  | .permitted defended =>
    match inspectPlan prior answers (primitiveScript response) with
    | .inl issue => .inl (.inr issue)
    | .inr approved =>
      .inr ⟨_, a_reserved_defence_closes_the_original_permission
        attack prior answers rival person response floor atAttack defended approved.down⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment
