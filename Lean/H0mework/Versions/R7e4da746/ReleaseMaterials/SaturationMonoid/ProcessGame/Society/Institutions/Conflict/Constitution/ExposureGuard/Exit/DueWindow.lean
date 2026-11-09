import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence.Round

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Due

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Civil.Persistence (Window)

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "W" => Window Party Good Port Technology Instrument
local notation "Word" => Civil.Persistence.Script Party Good Port Technology Instrument
local notation "Cell" => Party × Use × Good × ℚ

variable (origin : Root.Cut Party Good Port Technology Instrument)
  (window : Window Party Good Port Technology Instrument)
  (input : Option (Compile.RawInput Party Good Port Technology Instrument))

/-- Read the existing window and material payments. The personal lanes
are responsible for distinguishing actual assent at the same item. -/
def Step : Prop :=
  window.crosses input → (window.nextCut input).raw.clock ≤ window.deadline ∧ window.Pays origin [] input

inductive Issue
  | late (crossed : window.crosses input) (clock : window.deadline < (window.nextCut input).raw.clock)
  | short (crossed : window.crosses input) (cell : Cell) (listed : cell ∈ window.cells origin [])
      (amount : window.timely [] input cell < cell.2.2.2)

theorem Issue.refutes (issue : Issue origin window input) : ¬ Step origin window input := by
  intro paid
  cases issue with
  | late crossed clock => exact (not_le_of_gt clock) (paid crossed).1
  | short crossed cell listed amount => exact (not_le_of_gt amount) ((paid crossed).2 cell listed)

noncomputable def inspectStep : Issue origin window input ⊕ PLift (Step origin window input) :=
  if crossed : window.crosses input then
    if time : (window.nextCut input).raw.clock ≤ window.deadline then
      match Capitalism.Universal.Abolition.Material.inspectList
          (fun cell : Cell => cell.2.2.2 ≤ window.timely [] input cell) (window.cells origin []) with
      | .failure cell listed deficit => .inl (.short crossed cell listed (lt_of_not_ge deficit))
      | .clear paid => .inr ⟨fun _ => ⟨time, paid⟩⟩
    else .inl (.late crossed (lt_of_not_ge time))
  else .inr ⟨fun yes => (crossed yes).elim⟩

def Checked : W → Word → Prop
  | _, [] => True
  | window, input :: rest => Step origin window input ∧ Checked (window.write input) rest

inductive FirstFailure : W → Word → Type _
  | here {window input rest} (issue : Issue origin window input) : FirstFailure window (input :: rest)
  | later {window input rest} (paid : Step origin window input)
      (issue : FirstFailure (window.write input) rest) : FirstFailure window (input :: rest)

theorem FirstFailure.refutes {window : W} {word : Word} (failed : FirstFailure origin window word) :
    ¬ Checked origin window word := by
  induction failed with
  | here issue => exact fun paid => issue.refutes _ _ _ paid.1
  | later _ _ inherited => exact fun paid => inherited paid.2

noncomputable def inspect : (window : W) → (word : Word) → FirstFailure origin window word ⊕ PLift (Checked origin window word)
  | _, [] => .inr ⟨trivial⟩
  | window, input :: rest =>
    match inspectStep origin window input with
    | .inl issue => .inl (.here issue)
    | .inr paid =>
      match inspect (window.write input) rest with
      | .inl issue => .inl (.later paid.down issue)
      | .inr later => .inr ⟨paid.down, later.down⟩

variable {Community : Type} [DecidableEq Community]

theorem of_original_civilian_check (community : Party → Community) (own : Bool) (word : Word)
    (good : Civil.Persistence.Checked origin [] community own window word) : Checked origin window word := by
  induction word generalizing window with
  | nil => trivial
  | cons input rest prior => exact ⟨fun crossed => ⟨good.1.onTime crossed, good.1.paid crossed⟩, prior _ good.2⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Due
