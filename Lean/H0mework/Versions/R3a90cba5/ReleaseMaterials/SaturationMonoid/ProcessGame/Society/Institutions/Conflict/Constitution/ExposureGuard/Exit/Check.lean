import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Exit.Standing

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Exit

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Civil.Persistence (ExitAtCut RoundFailure Window inspectRound timelyUses)
open Quantities.Execution (endAt inventory)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]

local notation "C" => Conflict.Root.Cut Party Good Port Technology Instrument
local notation "Word" => Reparation.Actual.Script Party Good Port Technology Instrument
local notation "Item" => ExecutionItem Party Good Port Technology Instrument
local notation "Cell" => Party × Use × Good × ℚ

/-- The raw item's own signer bears its material and financial exposures.
The item's current control seat is read at that very item. -/
def OwnExposure (cut : C) (control : RawCurrent Party Good Technology Instrument → List Party) (item : Item) : Prop :=
  item.request.signer ∉ control item.before ∧
    ∀ question ∈ questions cut item, question.1 = item.request.signer

instance (cut : C) (control : RawCurrent Party Good Technology Instrument → List Party) (item : Item) :
    Decidable (OwnExposure cut control item) := by
  unfold OwnExposure
  infer_instance

abbrev timelyAt (cut : C) (control : RawCurrent Party Good Technology Instrument → List Party)
    (word : Word) (cell : Cell) : ℚ :=
  timelyUses (Window.at cut).deadline (control cut.raw) cell cut word

structure Shortage (cut : C) (cells : List Cell) (control : RawCurrent Party Good Technology Instrument → List Party)
    (word : Word) where
  cell : Cell
  original : cell ∈ cells
  deficit : timelyAt cut control word cell < cell.2.2.2

def Shortage.amount {cut : C} {cells : List Cell} {control : RawCurrent Party Good Technology Instrument → List Party}
    {word : Word} (short : Shortage cut cells control word) : ℚ :=
  short.cell.2.2.2 - timelyAt cut control word short.cell

omit [DecidableEq Community] in
theorem Shortage.positive {cut : C} {cells : List Cell}
    {control : RawCurrent Party Good Technology Instrument → List Party} {word : Word}
    (short : Shortage cut cells control word) : 0 < short.amount :=
  sub_pos.mpr short.deficit

inductive FailureAt (baseline cut : C) (community : Party → Community) (people : List Party)
    (cells : List Cell) (control : RawCurrent Party Good Technology Instrument → List Party) (word : Word)
  | standing (issue : StandingFailure people cut word)
  | exposure (item : Item) (original : item ∈ inventory cut word) (refused : ¬ OwnExposure cut control item)
  | shortage (issue : Shortage cut cells control word)
  | round (issue : RoundFailure baseline (control cut.raw) community (Window.at cut) word [])

variable (seed : Conflict.Root.Cut Party Good Port Technology Instrument) (community : Party → Community)
  (anchor history : Reparation.Actual.Script Party Good Port Technology Instrument)
  (control : RawCurrent Party Good Technology Instrument → List Party)

local notation "baselineCut" => endAt seed anchor
local notation "current" => endAt seed history
local notation "people" => roster seed community anchor history
local notation "command" => control (Evolving.Epoch.Current.raw (endAt seed history))

def needCells : List Cell := (needsAt baselineCut people ++ needsAt current people).dedup

variable (word : Reparation.Actual.Script Party Good Port Technology Instrument)

/-- This checks one fresh executable exit on the original root. It
preserves the whole roster and pays the original material cells by their
actual next deadline. The option itself is not a material write. -/
structure Certificate : Prop where
  standing : StandingAlong people current word
  own : ∀ item ∈ inventory current word, OwnExposure current control item
  floor : ∀ cell ∈ needCells seed community anchor history, cell.2.2.2 ≤ timelyAt current control word cell
  renewal : ExitAtCut baselineCut command community current word

abbrev Failure := FailureAt baselineCut current community people (needCells seed community anchor history) control word

theorem Failure.refutes (issue : Failure seed community anchor history control word) :
    ¬ Certificate seed community anchor history control word := by
  intro paid
  cases issue with
  | standing issue => exact issue.refutes paid.standing
  | exposure item original refused => exact refused (paid.own item original)
  | shortage issue => exact (not_le_of_gt issue.deficit) (paid.floor issue.cell issue.original)
  | round issue => exact issue.refutes paid.renewal

def inspect : Failure seed community anchor history control word ⊕
    PLift (Certificate seed community anchor history control word) :=
  match inspectStanding people current word with
  | .inl issue => .inl (.standing issue)
  | .inr standing =>
    match Material.inspectList (OwnExposure current control) (inventory current word) with
    | .failure item original refused => .inl (.exposure item original refused)
    | .clear own =>
      match Material.inspectList (fun cell : Cell => cell.2.2.2 ≤ timelyAt current control word cell)
          (needCells seed community anchor history) with
      | .failure cell original refused => .inl (.shortage ⟨cell, original, lt_of_not_ge refused⟩)
      | .clear floor =>
        match inspectRound baselineCut command community (Window.at current) word [] with
        | .inl issue => .inl (.round issue)
        | .inr renewal => .inr ⟨⟨standing.down, own, floor, renewal.down⟩⟩

def Available : Prop := ∃ word : Word, Certificate seed community anchor history control word

theorem no_exit_iff_every_original_word_has_its_exact_failure :
    ¬ Available seed community anchor history control ↔ ∀ word : Word,
      ∃ issue, inspect seed community anchor history control word = .inl issue := by
  constructor
  · intro unavailable word
    cases inspect seed community anchor history control word with
    | inl issue => exact ⟨issue, rfl⟩
    | inr paid => exact (unavailable ⟨word, paid.down⟩).elim
  · rintro failed ⟨word, paid⟩
    obtain ⟨issue, _⟩ := failed word
    exact Failure.refutes seed community anchor history control word issue paid

theorem a_preserved_exit_keeps_the_original_bearers_on_the_candidate_successor
    (available : Available seed community anchor history control) :
    StandingAt people current := by
  obtain ⟨word, checked⟩ := available
  exact checked.standing.at_original_cut (before := []) (tail := word)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Exit
