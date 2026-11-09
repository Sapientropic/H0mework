import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment.Window

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open PublicFunction.Mandate

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]

local notation "M" => State Party Technology
local notation "Word" => Reparation.Actual.Script Party Good Port M Instrument
local notation "Input" => Reparation.Actual.Input Party Good Port M Instrument

variable {seed : Root.Cut Party Good Port (State Party Technology) Instrument}
  {community : Party → Community}
  {anchor : Reparation.Actual.Script Party Good Port (State Party Technology) Instrument}

theorem same_paid_visit (left right : PaidVisit seed community anchor)
    (original : left.history = right.history) (whole : HEq left.state right.state) :
    left = right := by
  rcases left with ⟨before, h₁, first, a₁, p₁⟩
  rcases right with ⟨after, h₂, last, a₂, p₂⟩
  change before = after at original
  subst after
  have equal : first = last := eq_of_heq whole
  subst last
  rfl

variable (answers : OwnerAnswers seed)

private theorem empty_write {past : Word} (state : Reparation.Actual.State seed community past) :
    HEq (Receipts.writeAfter answers state []) state := by
  unfold Receipts.writeAfter
  rw [List.reverseRecOn_nil]
  exact eqRec_heq (List.append_nil past).symm state

private theorem congr_write {first last : Word}
    (left : Reparation.Actual.State seed community first) (right : Reparation.Actual.State seed community last)
    (same : first = last) (whole : HEq left right) (input : Input) :
    HEq (Receipts.writeTick answers left input) (Receipts.writeTick answers right input) := by
  subst last
  have equal := eq_of_heq whole
  subst right
  rfl

private theorem singleton_write {past : Word} (state : Reparation.Actual.State seed community past) (input : Input) :
    HEq (Receipts.writeAfter answers state [input]) (Receipts.writeTick answers state input) := by
  have actual := Receipts.writeAfter_snoc answers state [] input
  exact (heq_of_eq actual).trans ((eqRec_heq (List.append_assoc past [] [input]) _).trans
    (congr_write answers (Receipts.writeAfter answers state []) state (List.append_nil past)
      (empty_write answers state) input))

variable (prior : PaidVisit seed community anchor)

theorem advance_paid_empty (paid : MandateExit.PaidAt seed anchor (prior.history ++ [])) :
    advancePaid prior answers [] paid = prior :=
  same_paid_visit _ _ (List.append_nil _) (empty_write answers prior.state)

/-- Writing the next original visit consumes the same full account as
writing the whole prefix, with no additional receipt allocation. -/
theorem advance_paid_snoc (front : Word) (input : Input)
    (first : MandateExit.PaidAt seed anchor (prior.history ++ front))
    (next : MandateExit.PaidAt seed anchor ((prior.history ++ front) ++ [input]))
    (whole : MandateExit.PaidAt seed anchor (prior.history ++ (front ++ [input]))) :
    advancePaid (advancePaid prior answers front first) answers [input] next =
      advancePaid prior answers (front ++ [input]) whole := by
  apply same_paid_visit _ _ (List.append_assoc _ _ _)
  let initial := Receipts.writeAfter answers prior.state front
  have actual := Receipts.writeAfter_snoc answers prior.state front input
  exact (singleton_write answers initial input).trans
    ((eqRec_heq (List.append_assoc prior.history front [input])
      (Receipts.writeTick answers initial input)).symm.trans (heq_of_eq actual.symm))

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment
