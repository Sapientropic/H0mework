import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment.Admission
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment.Window

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Civil.Persistence (Window)
open PublicFunction.Mandate
open Quantities.Execution (endAt)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]

local notation "M" => State Party Technology
local notation "Word" => Reparation.Actual.Script Party Good Port M Instrument

variable {seed : Root.Cut Party Good Port (State Party Technology) Instrument}
  {community : Party → Community}
  {anchor : Reparation.Actual.Script Party Good Port (State Party Technology) Instrument}
  (prior : PaidVisit seed community anchor) (answers : OwnerAnswers seed)
  (word : Reparation.Actual.Script Party Good Port (State Party Technology) Instrument)

/-- The whole literal plan is checked before it receives priority.
Its evidence comes from the same registered material inventory. -/
structure Certified : Prop where
  admitted : Checked seed community anchor answers prior.history word
  due : MandateExit.PaidAt seed anchor (prior.history ++ word)
  standing : Exit.StandingAlong (Exit.roster seed community anchor prior.history)
    (endAt seed prior.history) word

abbrev PlanFailure :=
  Failure seed community anchor answers prior.history word ⊕
    (Exit.StandingFailure (Exit.roster seed community anchor prior.history) (endAt seed prior.history) word ⊕
      MandateExit.DueFailure seed anchor (prior.history ++ word))

theorem PlanFailure.refutes (failure : PlanFailure prior answers word) :
    ¬ Certified prior answers word := by
  intro approved
  cases failure with
  | inl failed => exact failed.refutes approved.admitted
  | inr failed =>
    cases failed with
    | inl standing => exact standing.refutes approved.standing
    | inr due => exact due.refutes _ approved.due

private def dueOrdinal {opening : Root.Cut Party Good Port (State Party Technology) Instrument}
    {window : Window Party Good Port M Instrument} {suffix : Word} :
    Due.FirstFailure opening window suffix → Nat
  | .here _ => 0
  | .later _ failure => dueOrdinal failure + 1

def PlanFailure.ordinal : PlanFailure prior answers word → Nat
  | .inl failed => failed.front.length
  | .inr (.inl failed) => failed.before.length
  | .inr (.inr failed) => dueOrdinal failed - (prior.history.length - anchor.length)

private def earlier (left right : PlanFailure prior answers word) : PlanFailure prior answers word :=
  if left.ordinal prior answers word ≤ right.ordinal prior answers word then left else right

def inspectPlan : PlanFailure prior answers word ⊕ PLift (Certified prior answers word) :=
  let authorised := inspect seed community anchor answers prior.history word
  let standing := Exit.inspectStanding (Exit.roster seed community anchor prior.history) (endAt seed prior.history) word
  let due := Due.inspect (endAt seed anchor) ((Window.at seed).run anchor) ((prior.history ++ word).drop anchor.length)
  match standing, authorised, due with
  | .inr kept, .inr admitted, .inr paid => .inr ⟨admitted.down, paid.down, kept.down⟩
  | .inl lost, .inr _, .inr _ => .inl (.inr (.inl lost))
  | .inr _, .inl refused, .inr _ => .inl (.inl refused)
  | .inr _, .inr _, .inl late => .inl (.inr (.inr late))
  | .inl lost, .inl refused, .inr _ => .inl (earlier prior answers word (.inr (.inl lost)) (.inl refused))
  | .inl lost, .inr _, .inl late => .inl (earlier prior answers word (.inr (.inl lost)) (.inr (.inr late)))
  | .inr _, .inl refused, .inl late => .inl (earlier prior answers word (.inl refused) (.inr (.inr late)))
  | .inl lost, .inl refused, .inl late =>
    .inl (earlier prior answers word (.inr (.inl lost)) (earlier prior answers word (.inl refused) (.inr (.inr late))))

theorem an_admissible_commitment_is_returned_as_certified (approved : Certified prior answers word) :
    ∃ verified, inspectPlan prior answers word = .inr verified := by
  cases inspectPlan prior answers word with
  | inl failure => exact (failure.refutes _ _ _ approved).elim
  | inr checked => exact ⟨checked, rfl⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment
