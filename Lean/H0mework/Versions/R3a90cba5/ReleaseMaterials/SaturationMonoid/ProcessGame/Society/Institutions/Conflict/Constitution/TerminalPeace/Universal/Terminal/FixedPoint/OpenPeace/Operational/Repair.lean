import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Operational.RecipeMenu

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Operational.Repair

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Material
open Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  [DecidableEq (Request Party Good Port Technology Instrument)]

local notation "Action" => Request Party Good Port Technology Instrument
local notation "Word" => RawEvent Party Good Port Technology Instrument

private def substitute (alphabet : List Action) (word : Word) (position : Nat) : List Word :=
  if position < word.length then
    let front := word.take position
    let rest := word.drop (position + 1)
    (front ++ rest) :: alphabet.map (fun action => front ++ action :: rest)
  else []

private def insertAt (alphabet : List Action) (word : Word) (position : Nat) : List Word :=
  alphabet.map fun action => word.take position ++ action :: word.drop position

private def atAllGaps (alphabet : List Action) (word : Word) : List Word :=
  (List.range (word.length + 1)).flatMap (insertAt alphabet word)

private def replaceRequest (alphabet : List Action) (word : Word) (request : Action) : List Word :=
  (List.range word.length).flatMap fun position =>
    if word[position]? = some request then substitute alphabet word position else []

private def forNeed (alphabet : List Action) (word : Word) (person : Party) (purpose : Use) (good : Good) : List Word :=
  atAllGaps (alphabet.filter fun request =>
    match request.operation with
    | .use bearer goods kind => decide (bearer = person ∧ kind = purpose ∧ 0 < amount Good goods good)
    | _ => false) word

variable (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (origin raw : RawCurrent Party Good Technology Instrument)

local notation "Alphabet" => Migration.sourceAlphabet input raw

/-- The issue names which original instruction or obligation is edited.
Each new instruction is taken from the alphabet at the same physical cut. -/
def wordEdits {people : List Party} {word : Word}
    (issue : WordIssue input origin raw people word) : List Word :=
  match issue with
  | .unregistered request _ _ => replaceRequest Alphabet word request
  | .unpaid (.instruction failure) =>
    let providers := match failure.issue with
      | .materialShortage lot _ _ =>
        let before := (input.law.rawItems raw word)[failure.position].before
        let (person, good) := lot.1
        (Alphabet).filter fun action => decide (before.stock person good < (input.law.step before action).stock person good)
      | _ => Alphabet
    insertAt providers word failure.position.val ++ substitute Alphabet word failure.position.val
  | .unpaid (.originalNeed need) => forNeed Alphabet word need.cell.1 need.cell.2.1 need.cell.2.2.1
  | .unpaid (.currentNeed need) => forNeed Alphabet word need.cell.1 need.cell.2.1 need.cell.2.2.1
  | .unpaid (.clock _) => []

variable (people : List Party)

/-- Only material words change. Stability of the underlying programme is
inherited from the registered code, then the entire recipe is rechecked. -/
def codeEdits {code : RepeatCode input raw}
    (issue : RecipeIssue input origin raw people code) : RecipeMenu input raw :=
  let withProduction := fun word => { code with production := word }
  match issue with
  | .production failed => (wordEdits input origin raw failed).map withProduction
  | .personal failed =>
    (wordEdits input origin raw failed.issue).flatMap fun personal =>
      (atAllGaps Alphabet code.production).map fun production =>
        { code with production, personal := fun p => if p = failed.person then personal else code.personal p }
  | .imbalance (.unsupported request _ _) =>
    (replaceRequest Alphabet code.production request).map withProduction
  | .imbalance (.imbalance _ _ _) =>
    ((List.range (code.production.length + 1)).flatMap fun position =>
      insertAt Alphabet code.production position ++ substitute Alphabet code.production position).map withProduction
  | .stalled _ => (atAllGaps Alphabet code.production).map withProduction

variable (menu : RecipeMenu input raw) (incumbent : RawEvent Party Good Port Technology Instrument)

def Fresh (word : Word) : Prop :=
  word ≠ incumbent ∧ ∀ code ∈ menu, word ≠ code.production

instance (word : Word) : Decidable (Fresh input raw menu incumbent word) := by
  unfold Fresh
  infer_instance

variable (each : RejectedRecipes input origin raw people menu)

/-- Every rejected position contributes its own typed edit family. The
incumbent and all previously submitted production words are excluded. -/
def candidates : RecipeMenu input raw :=
  ((List.finRange menu.length).flatMap fun pos => codeEdits input origin raw people (each pos)).filter
    fun code => decide (Fresh input raw menu incumbent code.production)

theorem candidate_comes_from_an_original_failure (code : RepeatCode input raw) :
    code ∈ candidates input origin raw people menu incumbent each ↔
      (∃ pos : Fin menu.length, code ∈ codeEdits input origin raw people (each pos)) ∧
      Fresh input raw menu incumbent code.production := by
  simp [candidates, List.mem_flatMap]

inductive Decision
  | registered (chosen : SelectedRecipe input origin raw people menu)
  | generated (each : RejectedRecipes input origin raw people menu)
      (chosen : SelectedRecipe input origin raw people (candidates input origin raw people menu incumbent each))
  | exhausted (each : RejectedRecipes input origin raw people menu)
      (rejected : RejectedRecipes input origin raw people (candidates input origin raw people menu incumbent each))

/-- The registered menu keeps precedence. Only its complete typed rejection
opens the repair search, which uses the same checker and ordered selection. -/
def select : Decision input origin raw people menu incumbent :=
  match chooseRecipe input origin raw people menu with
  | .inr chosen => .registered chosen
  | .inl rejected =>
    match chooseRecipe input origin raw people (candidates input origin raw people menu incumbent rejected) with
    | .inr chosen => .generated rejected chosen
    | .inl refused => .exhausted rejected refused

variable {input origin raw people menu incumbent} in
def Decision.generatedWord : Decision input origin raw people menu incumbent → Option Word
  | .generated _ chosen => some chosen.recipe.move.word
  | _ => none

theorem a_generated_word_is_fresh_and_located
    (chosen : SelectedRecipe input origin raw people (candidates input origin raw people menu incumbent each)) :
    Fresh input raw menu incumbent chosen.recipe.move.word ∧
      ∃ pos : Fin menu.length, ∃ code : RepeatCode input raw, code ∈ codeEdits input origin raw people (each pos) ∧
        code.production = chosen.recipe.move.word := by
  let code := (candidates input origin raw people menu incumbent each)[chosen.position]
  have source := (candidate_comes_from_an_original_failure input origin raw people menu incumbent each code).mp
    (List.getElem_mem chosen.position.isLt)
  obtain ⟨pos, edit⟩ := source.1
  exact ⟨chosen.word.symm ▸ source.2, pos, code, edit, chosen.word.symm⟩

theorem an_available_edit_is_selected
    (rejected : chooseRecipe input origin raw people menu = .inl each)
    {code : RepeatCode input raw} {pos : Fin menu.length}
    (edit : code ∈ codeEdits input origin raw people (each pos))
    (fresh : Fresh input raw menu incumbent code.production)
    (available : RecipeConditions input origin raw people code) :
    ∃ chosen, select input origin raw people menu incumbent = .generated each chosen := by
  have listed := (candidate_comes_from_an_original_failure input origin raw people menu incumbent each code).mpr
    ⟨⟨pos, edit⟩, fresh⟩
  obtain ⟨i, eq⟩ := List.mem_iff_getElem.mp listed
  obtain ⟨chosen, accepted⟩ := chooseRecipe_finds_an_available_word input origin raw people
    (candidates input origin raw people menu incumbent each) ⟨i, eq.1⟩ (eq.2.symm ▸ available)
  exact ⟨chosen, by simp only [select, rejected, accepted]⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Operational.Repair
