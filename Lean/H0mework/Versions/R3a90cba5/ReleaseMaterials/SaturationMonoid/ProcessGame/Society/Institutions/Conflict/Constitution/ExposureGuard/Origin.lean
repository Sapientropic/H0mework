import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Run.Disposition

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt)
open Reparation.Actual (originalLosses)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]

local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "Input" => Reparation.Actual.Input Party Good Port Technology Instrument
local notation "Word" => Reparation.Actual.Script Party Good Port Technology Instrument

/-- The original census and the original victims determine whose answers
must be obtained. A successor's office roster cannot remove these people. -/
def bearers (seed : C) (community : Party → Community) (anchor : Word) : List Party :=
  ((endAt seed anchor).members ++ (originalLosses seed community anchor).map (fun loss => loss.key.1)).dedup

theorem every_original_member_is_a_bearer (seed : C) (community : Party → Community)
    (anchor : Word) (person : Party) (member : person ∈ (endAt seed anchor).members) :
    person ∈ bearers seed community anchor :=
  List.mem_dedup.mpr (List.mem_append_left _ member)

theorem every_original_victim_is_a_bearer (seed : C) (community : Party → Community) (anchor : Word)
    (loss : Reparation.Actual.Occurrence seed community)
    (original : loss ∈ originalLosses seed community anchor) :
    loss.key.1 ∈ bearers seed community anchor :=
  List.mem_dedup.mpr (List.mem_append_right _ (List.mem_map_of_mem original))

omit [DecidableEq Community] in
/-- The root's personal input lanes answer the exact material question.
The proposal never carries these answers. -/
abbrev OwnerAnswers (seed : C) :=
  (past : Word) → (input : Input) →
    Fin (Boundary.Actual.items (endAt seed past) input).length → Party → Bool

omit [DecidableEq Community] in
def withhold {seed : C} (answers : OwnerAnswers seed) (person : Party) : OwnerAnswers seed :=
  fun past input position bearer => if bearer = person then false else answers past input position bearer

omit [DecidableEq Community] in
theorem withholding_uses_the_original_personal_lane {seed : C} (answers : OwnerAnswers seed)
    (person : Party) (past : Word) (input : Input)
    (position : Fin (Boundary.Actual.items (endAt seed past) input).length) :
    withhold answers person past input position person = false :=
  if_pos rfl

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard
