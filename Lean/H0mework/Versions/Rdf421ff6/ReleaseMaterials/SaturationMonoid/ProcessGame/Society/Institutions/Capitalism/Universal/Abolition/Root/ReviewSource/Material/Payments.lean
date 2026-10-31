import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Material.Scope

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

abbrev Slot := Fin task.val.slots.length
def slot (index : Slot input depth count task) := task.val.slots[index]

def SlotPaid (before : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) (index : Slot input depth count task) : Prop :=
  task.val.earliest ≤ before.clock ∧ (input.law.next before word).clock ≤ task.val.deadline ∧
    Exit.Necessity.BundlePaid input.law before word (slot input depth count task index).bearer
      (slot input depth count task index).goods (slot input depth count task index).purpose

instance (before : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) (index : Slot input depth count task) :
    Decidable (SlotPaid input depth count task before word index) := by unfold SlotPaid; infer_instance

/-- This checks the declared task against the actual word at its original
declaration occurrence, not against a same-looking earlier task. -/
def DeclarationPaid (index : Slot input depth count task) : Prop :=
  SlotPaid input depth count task
    (ProgrammeSource.rawCurrent input (Settlement.committedVisit input depth count).current)
    (ProgrammeSource.rawEvent input (Settlement.committedVisit input depth count).current) index

def EventPaid (event : Physical.Cursor Party Good Port Technology Instrument)
    (index : Slot input depth count task) : Prop :=
  let before := Physical.stateAt input depth count prefixLimit renewalLimit event.past
  let result := Physical.resultAt input depth count prefixLimit renewalLimit event
  task.val.earliest ≤ before.raw.clock ∧
    (result.next input depth count prefixLimit renewalLimit before).raw.clock ≤ task.val.deadline ∧
    Exit.Necessity.BundlePaid input.law before.raw
      (result.requests input depth count prefixLimit renewalLimit before)
      (slot input depth count task index).bearer (slot input depth count task index).goods
      (slot input depth count task index).purpose

def PhysicalPaid (past : List (Compile.RawInput Party Good Port Technology Instrument))
    (position : Fin past.length) (index : Slot input depth count task) : Prop :=
  EventPaid input depth count prefixLimit renewalLimit task (Physical.Prefix.eventCursor past position) index

instance (index : Slot input depth count task) : Decidable (DeclarationPaid input depth count task index) := by
  unfold DeclarationPaid
  infer_instance

instance (past : List (Compile.RawInput Party Good Port Technology Instrument))
    (position : Fin past.length) (index : Slot input depth count task) :
    Decidable (PhysicalPaid input depth count prefixLimit renewalLimit task past position index) := by
  unfold PhysicalPaid EventPaid
  infer_instance

variable (current : Physical.Cursor Party Good Port Technology Instrument)

abbrev PaymentPosition := Unit ⊕ Fin current.past.length

def PaidAt (position : PaymentPosition current) (index : Slot input depth count task) : Prop :=
  match position with
  | .inl _ => DeclarationPaid input depth count task index
  | .inr actual => PhysicalPaid input depth count prefixLimit renewalLimit task current.past actual index

instance (position : PaymentPosition current) (index : Slot input depth count task) :
    Decidable (PaidAt input depth count prefixLimit renewalLimit task current position index) := by
  unfold PaidAt
  cases position <;> infer_instance

def positions : List (PaymentPosition current) := .inl () :: (List.finRange current.past.length).map Sum.inr

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] in
private theorem positions_complete (position : PaymentPosition current) : position ∈ positions current := by
  cases position with
  | inl original => cases original; exact List.mem_cons_self
  | inr actual => exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨actual, by simp, rfl⟩)

/-- A finite search over already occurred source positions. This is an
effect witness; it creates neither a native archive nor a payment registry. -/
def payment? (index : Slot input depth count task) :
    Option {position : PaymentPosition current // PaidAt input depth count prefixLimit renewalLimit task current position index} :=
  match Abolition.Material.inspectList (fun position =>
      ¬ PaidAt input depth count prefixLimit renewalLimit task current position index) (positions current) with
  | .clear _ => none
  | .failure position _ unpaid => some ⟨position, not_not.mp unpaid⟩

theorem no_payment_iff_no_observed_payment (index : Slot input depth count task) :
    payment? input depth count prefixLimit renewalLimit task current index = none ↔
      ∀ position, ¬ PaidAt input depth count prefixLimit renewalLimit task current position index := by
  cases scan : Abolition.Material.inspectList (fun position =>
      ¬ PaidAt input depth count prefixLimit renewalLimit task current position index) (positions current) with
  | clear checked =>
      exact ⟨fun _ position => checked position (positions_complete current position),
        fun _ => by simp only [payment?, scan]⟩
  | failure position member unpaid =>
      constructor
      · intro impossible
        simp only [payment?, scan] at impossible
        cases impossible
      · intro absent
        exact (unpaid (absent position)).elim

theorem recorded_payment_has_its_exact_original_source (index : Slot input depth count task)
    (paid : (payment? input depth count prefixLimit renewalLimit task current index).isSome = true) :
    DeclarationPaid input depth count task index ∨
      ∃ position, PhysicalPaid input depth count prefixLimit renewalLimit task current.past position index := by
  cases found : payment? input depth count prefixLimit renewalLimit task current index with
  | none => rw [found] at paid; cases paid
  | some evidence =>
      rcases evidence with ⟨position, original⟩
      cases position with
      | inl _ => exact Or.inl original
      | inr position => exact Or.inr ⟨position, original⟩

theorem earlier_physical_payment_is_the_same_occurrence
    (later : List (Compile.RawInput Party Good Port Technology Instrument))
    (position : Fin current.past.length) (index : Slot input depth count task) :
    PhysicalPaid input depth count prefixLimit renewalLimit task (current.past ++ later)
        ⟨position.val, by simp; omega⟩ index ↔
      PhysicalPaid input depth count prefixLimit renewalLimit task current.past position index := by
  have same : Physical.Prefix.eventCursor (current.past ++ later) ⟨position.val, by simp; omega⟩ =
      Physical.Prefix.eventCursor current.past position := by
    simp only [Physical.Prefix.eventCursor, List.get_eq_getElem,
      List.take_append_of_le_length (Nat.le_of_lt position.isLt), List.getElem_append_left position.isLt]
  exact congrArg (fun event => EventPaid input depth count prefixLimit renewalLimit task event index) same |>.to_iff

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Material

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Material.recorded_payment_has_its_exact_original_source
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Material.earlier_physical_payment_is_the_same_occurrence
