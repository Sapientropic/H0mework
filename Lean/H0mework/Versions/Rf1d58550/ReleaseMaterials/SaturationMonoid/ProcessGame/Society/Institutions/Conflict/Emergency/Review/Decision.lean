import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency.Review.Raw
import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency.Review.Native

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency

open Capitalism.Universal.Source.Program
open PublicFunction.Mandate

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

local notation "C" => Root.Cut Party Good Port (State Party Technology) Instrument
local notation "Word" => RawEvent Party Good Port (State Party Technology) Instrument
local notation "Base" => RawLaw Party Good Port Technology Instrument
local notation "J" => Scope (Party := Party) (Good := Good) (Port := Port)

structure ReviewPaid (base : Base) (scope : J) (cut : C) (first second : Party)
    (good : Good) (tail : Word) : Prop where
  expired : scope.task.deadline < cut.raw.clock
  standing : cut.raw.technology.holder ≠ none
  distinct : first ≠ second
  independent : cut.raw.technology.holder ≠ some first ∧ cut.raw.technology.holder ≠ some second
  charged : 0 < amount Good scope.revisionCost good
  localTail : LocalTail tail
  whole : Root.Paid cut (reviewWord base scope cut first second tail)
  raw : RawReview base scope cut.raw first second tail
  native : NativeReview base scope cut first second tail

theorem ReviewPaid.release_on_the_original_successor
    {base : Base} {scope : J} {cut : C} {first second : Party} {good : Good} {tail : Word}
    (review : ReviewPaid base scope cut first second good tail) (original : Installed cut base scope) :
    let next := Root.terminal cut (reviewWord base scope cut first second tail)
    next.raw.technology.holder = none ∧ next.raw.technology.offered = none ∧ next.raw.claims = cut.raw.claims := by
  dsimp only
  rw [review.whole.original_raw_exact, original]
  exact review.raw.released

inductive ReviewIssue (base : Base) (scope : J) (cut : C) (first second : Party) (good : Good) (tail : Word)
  | beforeCutoff (live : cut.raw.clock ≤ scope.task.deadline)
  | vacant (missing : cut.raw.technology.holder = none)
  | duplicated (same : first = second)
  | firstHolder (same : cut.raw.technology.holder = some first)
  | secondHolder (same : cut.raw.technology.holder = some second)
  | unpaidFee (fee : amount Good scope.revisionCost good ≤ 0)
  | foreignTail (missing : ¬ LocalTail tail)
  | originalFailure (failure : Root.Failure cut (reviewWord base scope cut first second tail))

inductive ReviewOutcome (base : Base) (scope : J) (cut : C) (first second : Party) (good : Good) (tail : Word)
  | reviewed (proof : ReviewPaid base scope cut first second good tail)
  | blocked (issue : ReviewIssue base scope cut first second good tail)

/-- Construct two paid checks from the same original submission. Expiry does
not depend on either reviewer completing the release. -/
def inspectReview (base : Base) (scope : J) (cut : C) (first second : Party) (good : Good) (tail : Word)
    (original : Installed cut base scope) : ReviewOutcome base scope cut first second good tail :=
  if expired : scope.task.deadline < cut.raw.clock then
    if vacant : cut.raw.technology.holder = none then .blocked (.vacant vacant)
    else if same : first = second then .blocked (.duplicated same)
    else if firstOwns : cut.raw.technology.holder = some first then .blocked (.firstHolder firstOwns)
    else if secondOwns : cut.raw.technology.holder = some second then .blocked (.secondHolder secondOwns)
    else if fee : 0 < amount Good scope.revisionCost good then
      if safe : LocalTail tail then
        match Root.inspect cut (reviewWord base scope cut first second tail) with
        | .paid actual =>
          let accepted := original_review_items original actual
          .reviewed ⟨expired, vacant, same, ⟨firstOwns, secondOwns⟩, fee, safe, actual,
            raw_review base scope cut.raw first second expired safe accepted.1 accepted.2,
            native_review original safe actual⟩
        | .rejected failure => .blocked (.originalFailure failure)
      else .blocked (.foreignTail safe)
    else .blocked (.unpaidFee (le_of_not_gt fee))
  else .blocked (.beforeCutoff (le_of_not_gt expired))

def ReviewOutcome.isReviewed {base : Base} {scope : J} {cut : C} {first second : Party} {good : Good}
    {tail : Word} : ReviewOutcome base scope cut first second good tail → Bool
  | .reviewed _ => true
  | .blocked _ => false

theorem inspectReview_accepts_iff (base : Base) (scope : J) (cut : C) (first second : Party)
    (good : Good) (tail : Word) (original : Installed cut base scope) :
    (inspectReview base scope cut first second good tail original).isReviewed = true ↔
      ReviewPaid base scope cut first second good tail := by
  constructor
  · intro reviewed
    cases decision : inspectReview base scope cut first second good tail original with
    | reviewed proof => exact proof
    | blocked issue => rw [decision] at reviewed; cases reviewed
  · intro paid
    simp only [inspectReview, dif_pos paid.expired, dif_neg paid.standing, dif_neg paid.distinct,
      dif_neg paid.independent.1, dif_neg paid.independent.2, dif_pos paid.charged, dif_pos paid.localTail]
    have actual := (Root.inspect_accepts_iff cut (reviewWord base scope cut first second tail)).mpr paid.whole
    cases decision : Root.inspect cut (reviewWord base scope cut first second tail) with
    | paid receipt => rfl
    | rejected issue => rw [decision] at actual; cases actual

end
end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency
