import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Check
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Actual.Migration.Check
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Migration.Candidates

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Migration

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (source : PublicFunction.OutstandingSource Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (current : Physical.Cursor Party Good Port Technology Instrument)
  (pair : Material.Migration.CodePair Party Good Port Technology Instrument)

/-- These are checks of proposed code at its interpreted currents. Only the
inherited branch reads an already generated payment; neither future branch
creates a receipt before its word actually occurs. -/
def SlotsKept : Prop :=
  ∀ index : source.Slot,
    (payments source depth count prefixLimit renewalLimit current.past index).isSome = true ∨
      source.SlotPaid (state source depth count prefixLimit renewalLimit current).raw pair.1 index ∨
      source.SlotPaid (source.seed.law.next (state source depth count prefixLimit renewalLimit current).raw pair.1) pair.2 index

def Checks : Prop :=
  Actual.Migration.Checks source.input (Actual.origin source.input depth count)
    (state source depth count prefixLimit renewalLimit current).raw
    (Actual.members source.input depth count) pair ∧
      SlotsKept source depth count prefixLimit renewalLimit current pair

inductive SlotIssue (before : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) (index : source.Slot) : Type
  | tooEarly (failed : before.clock < source.seed.task.earliest)
  | tooLate (failed : source.seed.task.deadline < (source.seed.law.next before word).clock)
  | unpaid (failed : ¬ Exit.Necessity.BundlePaid source.seed.law before word
      (source.seed.slot index).bearer (source.seed.slot index).goods (source.seed.slot index).purpose)

omit [DecidableEq Port] in
theorem SlotIssue.refutes {before : RawCurrent Party Good Technology Instrument}
    {word : RawEvent Party Good Port Technology Instrument} {index : source.Slot}
    (issue : SlotIssue source before word index) : ¬ source.SlotPaid before word index := by
  intro paid
  cases issue with
  | tooEarly failed => exact (not_le_of_gt failed) paid.1
  | tooLate failed => exact (not_le_of_gt failed) paid.2.1
  | unpaid failed => exact failed paid.2.2

private def diagnoseSlot (before : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) (index : source.Slot)
    (failed : ¬ source.SlotPaid before word index) : SlotIssue source before word index :=
  if earliest : source.seed.task.earliest ≤ before.clock then
    if deadline : (source.seed.law.next before word).clock ≤ source.seed.task.deadline then
      .unpaid (fun paid => failed ⟨earliest, deadline, paid⟩)
    else .tooLate (lt_of_not_ge deadline)
  else .tooEarly (lt_of_not_ge earliest)

inductive Problem : Type
  | material (issue : Actual.Migration.Issue source.input (Actual.origin source.input depth count)
      (state source depth count prefixLimit renewalLimit current).raw
      (Actual.members source.input depth count) pair)
  | service (index : source.Slot)
      (unrecorded : payments source depth count prefixLimit renewalLimit current.past index = none)
      (front : SlotIssue source (state source depth count prefixLimit renewalLimit current).raw pair.1 index)
      (tail : SlotIssue source
        (source.seed.law.next (state source depth count prefixLimit renewalLimit current).raw pair.1) pair.2 index)

theorem Problem.refutes (problem : Problem source depth count prefixLimit renewalLimit current pair) :
    ¬ Checks source depth count prefixLimit renewalLimit current pair := by
  intro checked
  cases problem with
  | material issue =>
      exact issue.refutes source.input (Actual.origin source.input depth count) _
        (Actual.members source.input depth count) pair checked.1
  | service index unrecorded frontUnpaid tailUnpaid =>
      rcases checked.2 index with old | front | tail
      · rw [unrecorded] at old
        cases old
      · exact frontUnpaid.refutes source front
      · exact tailUnpaid.refutes source tail

inductive Check : Type
  | accepted (checked : Checks source depth count prefixLimit renewalLimit current pair)
  | refused (problem : Problem source depth count prefixLimit renewalLimit current pair)

def inspect : Check source depth count prefixLimit renewalLimit current pair :=
  match Actual.Migration.inspect source.input (Actual.origin source.input depth count)
      (state source depth count prefixLimit renewalLimit current).raw (Actual.members source.input depth count) pair with
  | .refused issue => .refused (.material issue)
  | .accepted material =>
      match Material.inspectList (fun index : source.Slot =>
          (payments source depth count prefixLimit renewalLimit current.past index).isSome = true ∨
            source.SlotPaid (state source depth count prefixLimit renewalLimit current).raw pair.1 index ∨
            source.SlotPaid (source.seed.law.next (state source depth count prefixLimit renewalLimit current).raw pair.1) pair.2 index)
          (List.finRange source.seed.task.slots.length) with
      | .clear kept => .accepted ⟨material, fun index => kept index (by simp)⟩
      | .failure index _ failed => .refused (.service index (by
          cases recorded : payments source depth count prefixLimit renewalLimit current.past index with
          | none => rfl
          | some paid => exact (failed (Or.inl (by rw [recorded]; rfl))).elim)
          (diagnoseSlot source _ _ index (fun paid => failed (Or.inr (Or.inl paid))))
          (diagnoseSlot source _ _ index (fun paid => failed (Or.inr (Or.inr paid)))))

instance : Decidable (Checks source depth count prefixLimit renewalLimit current pair) :=
  match inspect source depth count prefixLimit renewalLimit current pair with
  | .accepted checked => isTrue checked
  | .refused problem => isFalse (problem.refutes source depth count prefixLimit renewalLimit current pair)

theorem every_unpaid_original_slot_is_checked_in_its_original_window
    (checked : Checks source depth count prefixLimit renewalLimit current pair)
    (index : source.Slot)
    (unpaid : payments source depth count prefixLimit renewalLimit current.past index = none) :
    source.SlotPaid (state source depth count prefixLimit renewalLimit current).raw pair.1 index ∨
      source.SlotPaid (source.seed.law.next (state source depth count prefixLimit renewalLimit current).raw pair.1) pair.2 index := by
  rcases checked.2 index with old | paid
  · rw [unpaid] at old
    cases old
  · exact paid

#print axioms inspect
#print axioms Problem.refutes
#print axioms every_unpaid_original_slot_is_checked_in_its_original_window

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Migration
