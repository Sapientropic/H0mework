import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Migration.Census.Planner
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Admission.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Review.Trace.Fees

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Migration.Budget

open Source.Program PublicFunction

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (source : OutstandingSource Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (current : Physical.Cursor Party Good Port Technology Instrument)
  (code : Admission.FeeCode (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))

/-- Fee participants are prospective responsibilities of the same finite
review code. This does not insert them into the already occurred census. -/
def scope (afterFees : RawCurrent Party Good Technology Instrument)
    (pair : Material.Migration.CodePair Party Good Port Technology Instrument) :=
  (Census.standing source depth count prefixLimit renewalLimit current ++
    Source.ProgrammeFace.parties source.seed.law ((state source depth count prefixLimit renewalLimit current).raw, [code.request]) ++
    Source.ProgrammeFace.parties source.seed.law (afterFees, pair.1) ++
    Source.ProgrammeFace.parties source.seed.law (source.seed.law.next afterFees pair.1, pair.2)).dedup

theorem every_current_member_remains_in_scope (afterFees : RawCurrent Party Good Technology Instrument)
    (pair : Material.Migration.CodePair Party Good Port Technology Instrument) (person : Party)
    (present : person ∈ Census.standing source depth count prefixLimit renewalLimit current) :
    person ∈ scope source depth count prefixLimit renewalLimit current code afterFees pair :=
  List.mem_dedup.mpr (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ present)))

def feeBefore (position : Nat) :=
  (source.seed.law.execute (state source depth count prefixLimit renewalLimit current).raw 0
    (List.replicate position code.request)).final

/-- A fee can discharge a service only at its own original micro-occurrence;
separate partial payments are not merged into an invented service event. -/
def FeePaidOn (position : Nat) (index : source.Slot) : Prop :=
  let before := feeBefore source depth count prefixLimit renewalLimit current code position
  source.seed.task.earliest ≤ before.clock ∧
    (source.seed.law.step before code.request).clock ≤ source.seed.task.deadline ∧
    Exit.Necessity.BundlePaid source.seed.law before [code.request]
      (source.seed.slot index).bearer (source.seed.slot index).goods (source.seed.slot index).purpose

instance (position : Nat) (index : source.Slot) :
    Decidable (FeePaidOn source depth count prefixLimit renewalLimit current code position index) := by
  unfold FeePaidOn
  infer_instance

def SlotsKept (paidCount : Nat) (afterFees : RawCurrent Party Good Technology Instrument)
    (pair : Material.Migration.CodePair Party Good Port Technology Instrument) : Prop :=
  ∀ index,
    (payments source depth count prefixLimit renewalLimit current.past index).isSome = true ∨
      (∃ position : Fin paidCount, FeePaidOn source depth count prefixLimit renewalLimit current code position.val index) ∨
      source.SlotPaid afterFees pair.1 index ∨
      source.SlotPaid (source.seed.law.next afterFees pair.1) pair.2 index

def Checks (paidCount : Nat) (afterFees : RawCurrent Party Good Technology Instrument)
    (pair : Material.Migration.CodePair Party Good Port Technology Instrument) : Prop :=
  Actual.Migration.Checks source.input (Actual.origin source.input depth count) afterFees
    (scope source depth count prefixLimit renewalLimit current code afterFees pair) pair ∧
      SlotsKept source depth count prefixLimit renewalLimit current code paidCount afterFees pair

inductive Issue (paidCount : Nat) (afterFees : RawCurrent Party Good Technology Instrument)
    (pair : Material.Migration.CodePair Party Good Port Technology Instrument) : Type
  | material (issue : Actual.Migration.Issue source.input (Actual.origin source.input depth count) afterFees
      (scope source depth count prefixLimit renewalLimit current code afterFees pair) pair)
  | service (index : source.Slot)
      (unrecorded : payments source depth count prefixLimit renewalLimit current.past index = none)
      (feesUnpaid : ∀ position : Fin paidCount, ¬ FeePaidOn source depth count prefixLimit renewalLimit current code position.val index)
      (front : Migration.SlotIssue source afterFees pair.1 index)
      (tail : Migration.SlotIssue source (source.seed.law.next afterFees pair.1) pair.2 index)

theorem Issue.refutes {paidCount : Nat} {afterFees : RawCurrent Party Good Technology Instrument}
    {pair : Material.Migration.CodePair Party Good Port Technology Instrument}
    (issue : Issue source depth count prefixLimit renewalLimit current code paidCount afterFees pair) :
    ¬ Checks source depth count prefixLimit renewalLimit current code paidCount afterFees pair := by
  intro checked
  cases issue with
  | material issue => exact issue.refutes source.input _ _ _ pair checked.1
  | service index unrecorded feesUnpaid front tail =>
      rcases checked.2 index with old | feePaid | frontPaid | tailPaid
      · rw [unrecorded] at old
        cases old
      · obtain ⟨position, paid⟩ := feePaid
        exact feesUnpaid position paid
      · exact front.refutes source frontPaid
      · exact tail.refutes source tailPaid

private def diagnoseSlot (before : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) (index : source.Slot)
    (failed : ¬ source.SlotPaid before word index) : Migration.SlotIssue source before word index :=
  if earliest : source.seed.task.earliest ≤ before.clock then
    if deadline : (source.seed.law.next before word).clock ≤ source.seed.task.deadline then
      .unpaid (fun paid => failed ⟨earliest, deadline, paid⟩)
    else .tooLate (lt_of_not_ge deadline)
  else .tooEarly (lt_of_not_ge earliest)

inductive Check (paidCount : Nat) (afterFees : RawCurrent Party Good Technology Instrument)
    (pair : Material.Migration.CodePair Party Good Port Technology Instrument) : Type
  | accepted (checked : Checks source depth count prefixLimit renewalLimit current code paidCount afterFees pair)
  | rejected (issue : Issue source depth count prefixLimit renewalLimit current code paidCount afterFees pair)

/-- The first actual fee changes the current at which the candidate is
checked. Original service windows and old payment provenance stay fixed. -/
def inspect (paidCount : Nat) (afterFees : RawCurrent Party Good Technology Instrument)
    (pair : Material.Migration.CodePair Party Good Port Technology Instrument) :
    Check source depth count prefixLimit renewalLimit current code paidCount afterFees pair :=
  match Actual.Migration.inspect source.input (Actual.origin source.input depth count) afterFees
      (scope source depth count prefixLimit renewalLimit current code afterFees pair) pair with
  | .refused issue => .rejected (.material issue)
  | .accepted material =>
      match Material.inspectList (fun index : source.Slot =>
          (payments source depth count prefixLimit renewalLimit current.past index).isSome = true ∨
            (∃ position : Fin paidCount, FeePaidOn source depth count prefixLimit renewalLimit current code position.val index) ∨
            source.SlotPaid afterFees pair.1 index ∨ source.SlotPaid (source.seed.law.next afterFees pair.1) pair.2 index)
          (List.finRange source.seed.task.slots.length) with
      | .clear kept => .accepted ⟨material, fun index => kept index (by simp)⟩
      | .failure index _ failed => .rejected (.service index (by
          cases recorded : payments source depth count prefixLimit renewalLimit current.past index with
          | none => rfl
          | some paid => exact (failed (Or.inl (by rw [recorded]; rfl))).elim)
          (fun position paid => failed (Or.inr (Or.inl ⟨position, paid⟩)))
          (diagnoseSlot source afterFees pair.1 index (fun paid => failed (Or.inr (Or.inr (Or.inl paid)))))
          (diagnoseSlot source _ pair.2 index (fun paid => failed (Or.inr (Or.inr (Or.inr paid))))))

theorem checked_migration_keeps_every_original_livelihood (paidCount : Nat)
    (afterFees : RawCurrent Party Good Technology Instrument)
    (pair : Material.Migration.CodePair Party Good Port Technology Instrument)
    (checked : Checks source depth count prefixLimit renewalLimit current code paidCount afterFees pair) :
    Actual.Migration.Checks source.input (Actual.origin source.input depth count) afterFees
      (Actual.members source.input depth count) pair :=
  Census.actual_migration_restrict source.input _ _ _ _
    (fun person original => every_current_member_remains_in_scope source depth count prefixLimit renewalLimit current code afterFees pair person
      (Census.every_original_member_is_still_standing source depth count prefixLimit renewalLimit current person original)) pair checked.1

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Migration.Budget

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Migration.Budget.inspect
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Migration.Budget.checked_migration_keeps_every_original_livelihood
