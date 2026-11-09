import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Effects
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Refusal

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt inventory)

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "Input" => Reparation.Actual.Input Party Good Port Technology Instrument
local notation "Word" => Reparation.Actual.Script Party Good Port Technology Instrument
local notation "Item" => ExecutionItem Party Good Port Technology Instrument
abbrev Rule (seed : Root.Cut Party Good Port Technology Instrument) :=
  (roster : List Party) → OwnerAnswers seed → (past : Word) → (input : Input) →
    Fin (originalItems (seed := seed) past input).length → Prop

abbrev DecidableRule {seed : Root.Cut Party Good Port Technology Instrument} (rule : Rule seed) :=
  ∀ roster answers past input, DecidablePred (rule roster answers past input)

/-- Check the submitted continuation at this history and return its proof
when the finite check succeeds. -/
abbrev Probe (viable : Word → Prop) := (history : Word) → Option (PLift (viable history))

variable {seed : Root.Cut Party Good Port Technology Instrument}
  (roster : List Party) (answers : OwnerAnswers seed) (extension : Rule seed)
  (viable : Reparation.Actual.Script Party Good Port Technology Instrument → Prop)
  (check : Probe viable)
  (past : Reparation.Actual.Script Party Good Port Technology Instrument)
  (input : Reparation.Actual.Input Party Good Port Technology Instrument)

inductive Issue
  | original (failed : Failure roster answers past input)
  | additional (position : Fin (originalItems (seed := seed) past input).length)
      (denied : ¬ extension roster answers past input position)
  | future (missing : check (past ++ [input]) = none)

inductive Selection
  | accepted (original : Admitted roster answers past input)
      (additional : ∀ position, extension roster answers past input position)
      (continues : viable (past ++ [input]))
  | stopped (issue : Issue roster answers extension viable check past input)
      (empty : originalItems (seed := seed) past stop = [])
      (continues : viable (past ++ [stop]))
  | retained (issue : Issue roster answers extension viable check past input)
      (unavailable : originalItems (seed := seed) past stop ≠ [] ∨ check (past ++ [stop]) = none)

private def refuse (issue : Issue roster answers extension viable check past input) :
    Selection roster answers extension viable check past input :=
  if empty : (originalItems (seed := seed) past stop).length = 0 then
    match verified : check (past ++ [stop]) with
    | some proof => .stopped issue (List.eq_nil_of_length_eq_zero empty) proof.down
    | none => .retained issue (.inr verified)
  else .retained issue (.inl (fun noItems => empty (congrArg List.length noItems)))

variable [checkRule : DecidableRule extension]

def select : Selection roster answers extension viable check past input :=
  match inspectAdmission roster answers past input with
  | .inl failed => refuse roster answers extension viable check past input (.original failed)
  | .inr checked =>
    letI := checkRule roster answers past input
    match Capitalism.Universal.Abolition.Material.inspectList (extension roster answers past input)
        (List.finRange (originalItems (seed := seed) past input).length) with
    | .failure position _ denied => refuse roster answers extension viable check past input (.additional position denied)
    | .clear additional =>
      match verified : check (past ++ [input]) with
      | some proof => .accepted checked.down (fun position => additional position (List.mem_finRange _)) proof.down
      | none => refuse roster answers extension viable check past input (.future verified)

namespace Selection

variable {roster answers extension viable check past input}
  (selection : Selection roster answers extension viable check past input)

def emitted : Word :=
  match selection with
  | .accepted .. => [input]
  | .stopped .. => [stop]
  | .retained .. => []

omit checkRule in
theorem next_keeps_the_required_continuation (initial : viable past) :
    viable (past ++ selection.emitted) := by
  cases selection with
  | accepted _ _ continues | stopped _ _ continues => exact continues
  | retained => simpa only [emitted, List.append_nil] using initial

omit checkRule in
theorem every_emitted_input_is_lawful (emitted : Input) (chosen : emitted ∈ selection.emitted) :
    Admitted roster answers past emitted ∧ ∀ position, extension roster answers past emitted position := by
  cases selection with
  | accepted original additional =>
    have same : emitted = input := List.mem_singleton.mp chosen
    subst emitted
    exact ⟨original, additional⟩
  | stopped _ empty _ =>
    have same : emitted = stop := List.mem_singleton.mp chosen
    subst emitted
    refine ⟨no_material_is_admitted roster answers past stop empty, ?_⟩
    intro position
    have impossible : position.val < 0 := Nat.lt_of_lt_of_eq position.isLt (congrArg List.length empty)
    exact (Nat.not_lt_zero _ impossible).elim
  | retained => exact (List.not_mem_nil chosen).elim

omit checkRule in
theorem original_position_of_selected_item (item : Item)
    (listed : item ∈ inventory (endAt seed past) selection.emitted) :
    ∃ emitted ∈ selection.emitted, ∃ position : Fin (originalItems (seed := seed) past emitted).length,
      (originalItems (seed := seed) past emitted)[position] = item := by
  cases selection with
  | retained => exact (List.not_mem_nil listed).elim
  | stopped _ empty _ =>
    change item ∈ originalItems (seed := seed) past stop at listed
    rw [empty] at listed
    exact (List.not_mem_nil listed).elim
  | accepted =>
    change item ∈ originalItems (seed := seed) past input at listed
    obtain ⟨index, found⟩ := List.getElem?_of_mem listed
    obtain ⟨inside, same⟩ := List.getElem?_eq_some_iff.mp found
    exact ⟨input, List.mem_singleton_self _, ⟨index, inside⟩, same⟩

omit checkRule in
theorem the_original_selected_word_has_source_authority :
    Reparation.Actual.SourceAuthority (endAt seed past) selection.emitted := by
  intro item listed
  obtain ⟨actual, chosen, position, same⟩ := selection.original_position_of_selected_item item listed
  exact (selection.every_emitted_input_is_lawful actual chosen).1.1 item
    (same ▸ List.getElem_mem position.isLt)

end Selection

theorem the_composed_gate_forwards_an_admitted_continuation
    (lawful : Admitted roster answers past input)
    (additional : ∀ position, extension roster answers past input position)
    {verified : PLift (viable (past ++ [input]))}
    (continues : check (past ++ [input]) = some verified) :
    (select roster answers extension viable check past input).emitted = [input] := by
  unfold select
  cases inspectAdmission roster answers past input with
  | inl issue => exact (issue.refutes _ _ _ _ lawful).elim
  | inr checked =>
    let test := checkRule roster answers past input
    cases @Capitalism.Universal.Abolition.Material.inspectList _ (extension roster answers past input) test
      (List.finRange (originalItems (seed := seed) past input).length) with
    | failure position _ denied => exact (denied (additional position)).elim
    | clear _ =>
      dsimp only
      split
      · rfl
      · rename_i missing
        rw [continues] at missing
        cases missing

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard
