import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Material.Payments

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Material

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Registered Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (task : OriginalTask input depth count)
  (current : Physical.Cursor Party Good Port Technology Instrument)
  (pair : Abolition.Material.Migration.CodePair Party Good Port Technology Instrument)

/-- Candidate branches are obligations of the proposed code. They are not
recorded payments; only the first branch consumes an occurred source witness. -/
def SlotsKept : Prop := ∀ index : Slot input depth count task,
  (payment? input depth count prefixLimit renewalLimit task current index).isSome = true ∨
    SlotPaid input depth count task (rawAt input depth count prefixLimit renewalLimit current) pair.1 index ∨
    SlotPaid input depth count task (input.law.next (rawAt input depth count prefixLimit renewalLimit current) pair.1) pair.2 index

def Checks : Prop := MigrationChecks input depth count prefixLimit renewalLimit current task pair ∧
  SlotsKept input depth count prefixLimit renewalLimit task current pair

inductive SlotIssue (before : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) (index : Slot input depth count task) : Type
  | tooEarly (failed : before.clock < task.val.earliest)
  | tooLate (failed : task.val.deadline < (input.law.next before word).clock)
  | unpaid (failed : ¬ Exit.Necessity.BundlePaid input.law before word
      (slot input depth count task index).bearer (slot input depth count task index).goods
      (slot input depth count task index).purpose)

theorem SlotIssue.refutes {before : RawCurrent Party Good Technology Instrument}
    {word : RawEvent Party Good Port Technology Instrument} {index : Slot input depth count task}
    (issue : SlotIssue input depth count task before word index) : ¬ SlotPaid input depth count task before word index := by
  intro paid
  cases issue with
  | tooEarly failed => exact (not_le_of_gt failed) paid.1
  | tooLate failed => exact (not_le_of_gt failed) paid.2.1
  | unpaid failed => exact failed paid.2.2

private def diagnoseSlot (before : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) (index : Slot input depth count task)
    (failed : ¬ SlotPaid input depth count task before word index) : SlotIssue input depth count task before word index :=
  if earliest : task.val.earliest ≤ before.clock then
    if deadline : (input.law.next before word).clock ≤ task.val.deadline then
      .unpaid (fun paid => failed ⟨earliest, deadline, paid⟩)
    else .tooLate (lt_of_not_ge deadline)
  else .tooEarly (lt_of_not_ge earliest)

inductive Issue : Type
  | material (issue : Actual.Migration.Issue input (Actual.origin input depth count)
      (rawAt input depth count prefixLimit renewalLimit current)
      (scope input depth count prefixLimit renewalLimit current task pair) pair)
  | service (index : Slot input depth count task)
      (notObserved : payment? input depth count prefixLimit renewalLimit task current index = none)
      (front : SlotIssue input depth count task (rawAt input depth count prefixLimit renewalLimit current) pair.1 index)
      (tail : SlotIssue input depth count task
        (input.law.next (rawAt input depth count prefixLimit renewalLimit current) pair.1) pair.2 index)

theorem Issue.refutes (issue : Issue input depth count prefixLimit renewalLimit task current pair) :
    ¬ Checks input depth count prefixLimit renewalLimit task current pair := by
  intro checked
  cases issue with
  | material issue => exact issue.refutes input _ _ _ _ checked.1
  | service index absent front tail =>
      rcases checked.2 index with prior | futureFront | futureTail
      · rw [absent] at prior; cases prior
      · exact front.refutes input depth count task futureFront
      · exact tail.refutes input depth count task futureTail

inductive Check : Type
  | accepted (checked : Checks input depth count prefixLimit renewalLimit task current pair)
  | refused (issue : Issue input depth count prefixLimit renewalLimit task current pair)

/-- This inspects the whole material scope and actual service windows, but
does not claim a native service lifecycle attachment; that gate is separate. -/
def inspect : Check input depth count prefixLimit renewalLimit task current pair :=
  match Actual.Migration.inspect input (Actual.origin input depth count)
      (rawAt input depth count prefixLimit renewalLimit current)
      (scope input depth count prefixLimit renewalLimit current task pair) pair with
  | .refused issue => .refused (.material issue)
  | .accepted material =>
      match Abolition.Material.inspectList (fun index : Slot input depth count task =>
          (payment? input depth count prefixLimit renewalLimit task current index).isSome = true ∨
            SlotPaid input depth count task (rawAt input depth count prefixLimit renewalLimit current) pair.1 index ∨
            SlotPaid input depth count task (input.law.next (rawAt input depth count prefixLimit renewalLimit current) pair.1) pair.2 index)
          (List.finRange task.val.slots.length) with
      | .clear kept => .accepted ⟨material, fun index => kept index (by simp)⟩
      | .failure index _ failed => .refused (.service index (by
          cases found : payment? input depth count prefixLimit renewalLimit task current index with
          | none => rfl
          | some witness => exact (failed (Or.inl (by rw [found]; rfl))).elim)
          (diagnoseSlot input depth count task _ _ index (fun paid => failed (Or.inr (Or.inl paid))))
          (diagnoseSlot input depth count task _ _ index (fun paid => failed (Or.inr (Or.inr paid)))))

instance : Decidable (Checks input depth count prefixLimit renewalLimit task current pair) :=
  match inspect input depth count prefixLimit renewalLimit task current pair with
  | .accepted checked => isTrue checked
  | .refused issue => isFalse (issue.refutes input depth count prefixLimit renewalLimit task current pair)

theorem an_observed_payment_does_not_require_candidate_repayment (index : Slot input depth count task)
    (paid : (payment? input depth count prefixLimit renewalLimit task current index).isSome = true) :
    (payment? input depth count prefixLimit renewalLimit task current index).isSome = true ∨
      SlotPaid input depth count task (rawAt input depth count prefixLimit renewalLimit current) pair.1 index ∨
      SlotPaid input depth count task (input.law.next (rawAt input depth count prefixLimit renewalLimit current) pair.1) pair.2 index :=
  Or.inl paid

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Material

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Material.inspect
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Material.Issue.refutes
