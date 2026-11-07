import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.History

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (source : PublicFunction.OutstandingSource Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (current : Physical.Cursor Party Good Port Technology Instrument)
  (word : RawEvent Party Good Port Technology Instrument)

abbrev state := Physical.stateAt source.input depth count prefixLimit renewalLimit current.past

def SlotsKept : Prop :=
  ∀ index : source.Slot,
    (payments source depth count prefixLimit renewalLimit current.past index).isSome = true ∨
      source.SlotPaid (state source depth count prefixLimit renewalLimit current).raw word index

def Checks : Prop :=
  Actual.Batch.Checks source.input (Actual.origin source.input depth count)
    (state source depth count prefixLimit renewalLimit current).raw (Actual.members source.input depth count) word ∧
    SlotsKept source depth count prefixLimit renewalLimit current word

inductive Problem : Type
  | material (issue : Actual.Batch.Issue source.input (Actual.origin source.input depth count)
      (state source depth count prefixLimit renewalLimit current).raw (Actual.members source.input depth count) word)
  | service (index : source.Slot)
      (unrecorded : payments source depth count prefixLimit renewalLimit current.past index = none)
      (unpaid : ¬ source.SlotPaid (state source depth count prefixLimit renewalLimit current).raw word index)

theorem Problem.refutes (problem : Problem source depth count prefixLimit renewalLimit current word) :
    ¬ Checks source depth count prefixLimit renewalLimit current word := by
  intro checked
  cases problem with
  | material issue =>
      exact issue.refutes source.input (Actual.origin source.input depth count)
        _ (Actual.members source.input depth count) word checked.1
  | service index unrecorded unpaid =>
      rcases checked.2 index with old | paid
      · rw [unrecorded] at old
        cases old
      · exact unpaid paid

inductive Check : Type
  | accepted (checked : Checks source depth count prefixLimit renewalLimit current word)
  | refused (problem : Problem source depth count prefixLimit renewalLimit current word)

/-- Service and livelihood are checked together at this actual current.
An individually feasible service word cannot hide an unpaid life floor. -/
def inspect : Check source depth count prefixLimit renewalLimit current word :=
  match Actual.Batch.inspect source.input (Actual.origin source.input depth count)
      (state source depth count prefixLimit renewalLimit current).raw (Actual.members source.input depth count) word with
  | .refused issue => .refused (.material issue)
  | .accepted material =>
      match Material.inspectList (fun index : source.Slot =>
          (payments source depth count prefixLimit renewalLimit current.past index).isSome = true ∨
            source.SlotPaid (state source depth count prefixLimit renewalLimit current).raw word index)
          (List.finRange source.seed.task.slots.length) with
      | .clear kept => .accepted ⟨material, fun index => kept index (by simp)⟩
      | .failure index original failed => .refused (.service index (by
          cases recorded : payments source depth count prefixLimit renewalLimit current.past index with
          | none => rfl
          | some paid => exact (failed (Or.inl (by rw [recorded]; rfl))).elim)
          (fun paid => failed (Or.inr paid)))

instance : Decidable (Checks source depth count prefixLimit renewalLimit current word) :=
  match inspect source depth count prefixLimit renewalLimit current word with
  | .accepted checked => isTrue checked
  | .refused problem => isFalse (problem.refutes source depth count prefixLimit renewalLimit current word)

#print axioms inspect
#print axioms Problem.refutes

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services
