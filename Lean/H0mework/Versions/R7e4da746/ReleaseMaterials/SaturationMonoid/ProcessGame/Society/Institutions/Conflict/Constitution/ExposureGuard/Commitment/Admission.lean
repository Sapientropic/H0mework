import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Contract.Grant

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open PublicFunction.Mandate
open Quantities.Execution (endAt endAt_append endAt_input inventory inventory_append)
open Reparation.Actual.Allocation (Position)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]

local notation "M" => State Party Technology
local notation "C" => Root.Cut Party Good Port M Instrument
local notation "Input" => Reparation.Actual.Input Party Good Port M Instrument
local notation "Word" => Reparation.Actual.Script Party Good Port M Instrument

variable (seed : Root.Cut Party Good Port (State Party Technology) Instrument)
  (community : Party → Community)
  (anchor : Reparation.Actual.Script Party Good Port (State Party Technology) Instrument)
  (answers : OwnerAnswers seed)

local notation "roster" past => (bearers seed community anchor ++ bearers seed community past)

/-- Check the original admission and absence of new grants at each visit
of the submitted word. Each check reads the preceding literal history. -/
def Checked : Word → Word → Prop
  | _, [] => True
  | past, input :: tail =>
    Admitted (roster past) answers past input ∧
      (∀ position : Position seed past input, ¬ Grants (originalItems (seed := seed) past input)[position].request) ∧
      Checked (past ++ [input]) tail

abbrev IssueAt (past : Word) (input : Input) :=
  ExposureGuard.Failure (roster past) answers past input ⊕
    {position : Position seed past input // Grants (originalItems (seed := seed) past input)[position].request}

/-- The first refused visit and all the earlier checks on its own original prefix. -/
abbrev Failure (past word : Word) :=
  Σ front : Word, Σ input : Input, Σ tail : Word,
    PLift (word = front ++ input :: tail ∧ Checked seed community anchor answers past front) ×
      IssueAt seed community anchor answers (past ++ front) input

namespace Failure

variable {seed community anchor answers}
  {past word : Reparation.Actual.Script Party Good Port (State Party Technology) Instrument}
  (failed : Failure seed community anchor answers past word)

abbrev front : Word := failed.1
abbrev input : Input := failed.2.1
abbrev tail : Word := failed.2.2.1
abbrev split : word = front failed ++ input failed :: tail failed := failed.2.2.2.1.down.1
abbrev previous : Checked seed community anchor answers past (front failed) := failed.2.2.2.1.down.2
abbrev issue : IssueAt seed community anchor answers (past ++ front failed) (input failed) := failed.2.2.2.2

end Failure

def inspect : (past word : Word) →
    Failure seed community anchor answers past word ⊕ PLift (Checked seed community anchor answers past word)
  | _, [] => .inr ⟨trivial⟩
  | past, input :: tail =>
    match inspectAdmission (roster past) answers past input with
    | .inl denied =>
      .inl ⟨[], input, tail, ⟨⟨rfl, trivial⟩⟩, by rw [List.append_nil]; exact .inl denied⟩
    | .inr admitted =>
      match Capitalism.Universal.Abolition.Material.inspectList
          (fun position : Position seed past input => ¬ Grants (originalItems (seed := seed) past input)[position].request)
          (List.finRange (originalItems (seed := seed) past input).length) with
      | .failure position _ denied =>
        .inl ⟨[], input, tail, ⟨⟨rfl, trivial⟩⟩, by
          rw [List.append_nil]
          exact .inr ⟨position, not_not.mp denied⟩⟩
      | .clear checked =>
        have noGrants := fun position => checked position (List.mem_finRange _)
        match inspect (past ++ [input]) tail with
        | .inr rest => .inr ⟨admitted.down, noGrants, rest.down⟩
        | .inl ⟨front, failed, back, ⟨⟨literal, previous⟩⟩, issue⟩ =>
          have same : past ++ input :: front = (past ++ [input]) ++ front := by
            simp only [List.append_assoc, List.singleton_append]
          .inl ⟨input :: front, failed, back,
            ⟨⟨congrArg (input :: ·) literal, admitted.down, noGrants, previous⟩⟩, same.symm ▸ issue⟩

variable {seed community anchor answers}

theorem Checked.original_authority {past word : Word}
    (checked : Checked seed community anchor answers past word) :
    Reparation.Actual.SourceAuthority (endAt seed past) word := by
  induction word generalizing past with
  | nil => exact fun _ listed => (List.not_mem_nil listed).elim
  | cons input tail inherited =>
    intro item listed
    change item ∈ inventory (endAt seed past) ([input] ++ tail) at listed
    rw [inventory_append] at listed
    rcases List.mem_append.mp listed with here | later
    · exact checked.1.1 item here
    · have atNext : item ∈ inventory (endAt seed (past ++ [input])) tail := by rwa [endAt_append]
      have valid := inherited checked.2.2 item atNext
      rw [endAt_input] at valid ⊢
      exact valid

theorem Checked.no_grants {past word : Word}
    (checked : Checked seed community anchor answers past word) :
    ∀ item ∈ inventory (endAt seed past) word, ¬ Grants item.request := by
  induction word generalizing past with
  | nil => exact fun _ listed => (List.not_mem_nil listed).elim
  | cons input tail inherited =>
    intro item listed
    change item ∈ inventory (endAt seed past) ([input] ++ tail) at listed
    rw [inventory_append] at listed
    rcases List.mem_append.mp listed with here | later
    · change item ∈ originalItems (seed := seed) past input at here
      obtain ⟨index, found⟩ := List.getElem?_of_mem here
      obtain ⟨inside, exactItem⟩ := List.getElem?_eq_some_iff.mp found
      exact exactItem ▸ checked.2.1 ⟨index, inside⟩
    · have atNext : item ∈ inventory (endAt seed (past ++ [input])) tail := by rwa [endAt_append]
      exact inherited checked.2.2 item atNext

theorem Checked.at_visit {past word : Word}
    (checked : Checked seed community anchor answers past word) (front : Word) (input : Input) (tail : Word)
    (split : word = front ++ input :: tail) :
    Admitted (roster (past ++ front)) answers (past ++ front) input ∧
      ∀ position : Position seed (past ++ front) input,
        ¬ Grants (originalItems (seed := seed) (past ++ front) input)[position].request := by
  induction front generalizing past word with
  | nil =>
    subst word
    rw [List.append_nil]
    exact ⟨checked.1, checked.2.1⟩
  | cons first earlier inherited =>
    subst word
    rw [show past ++ first :: earlier = (past ++ [first]) ++ earlier from by
      simp only [List.append_assoc, List.singleton_append]]
    exact inherited checked.2.2 rfl

theorem Failure.refutes {past word : Word} (failed : Failure seed community anchor answers past word) :
    ¬ Checked seed community anchor answers past word := by
  intro accepted
  have here := accepted.at_visit failed.front failed.input failed.tail failed.split
  cases failed.issue with
  | inl denied => exact denied.refutes _ _ _ _ here.1
  | inr grant => exact here.2 grant.val grant.property

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment
