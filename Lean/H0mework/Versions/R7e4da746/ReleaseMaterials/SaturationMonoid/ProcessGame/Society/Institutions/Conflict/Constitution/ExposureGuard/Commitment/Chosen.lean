import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment.Admission
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Contract.Exercise

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open PublicFunction.Mandate
open Quantities.Execution (endAt endAt_append endAt_input inventory inventory_append)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]

local notation "M" => State Party Technology
local notation "C" => Root.Cut Party Good Port M Instrument
local notation "Item" => ExecutionItem Party Good Port M Instrument
local notation "Word" => Reparation.Actual.Script Party Good Port M Instrument
local notation "Raw" => RawCurrent Party Good M Instrument

omit [DecidableEq Community] in
private theorem questions_read_the_same_input {first second : C}
    (same : first.native.input = second.native.input) (item : Item) :
    questions first item = questions second item := by
  unfold questions materialQuestions physical Boundary.Actual.materialLaw
  rw [same]

omit [DecidableEq Community] in
private theorem answer_of_own_exposure {cut : C} {control : Raw → List Party} {item : Item}
    (own : Exit.OwnExposure cut control item) (lane : Party → Bool)
    (signed : lane item.request.signer = true) (question : Question Party Good Instrument)
    (asked : question ∈ questions cut item) : lane question.1 = true :=
  (congrArg lane (own.2 question asked)).trans signed

set_option maxHeartbeats 600000 in
theorem of_owned_word (seed : C) (community : Party → Community) (anchor : Word)
    (answers : OwnerAnswers seed) (control : Raw → List Party) (past word : Word)
    (authority : Reparation.Actual.SourceAuthority (endAt seed past) word)
    (own : ∀ item ∈ inventory (endAt seed past) word, Exit.OwnExposure (endAt seed past) control item)
    (authored : Exit.SignersChose answers past word)
    (noGrants : ∀ item ∈ inventory (endAt seed past) word, ¬ Grants item.request) :
    Checked seed community anchor answers past word := by
  induction word generalizing past with
  | nil => trivial
  | cons input tail earlier =>
    have partition : inventory (endAt seed past) (input :: tail) =
        inventory (endAt seed past) [input] ++ inventory (endAt seed (past ++ [input])) tail := by
      change inventory (endAt seed past) ([input] ++ tail) = _
      rw [inventory_append, endAt_append]
    have first (item : Item) (listed : item ∈ inventory (endAt seed past) [input]) :
        item ∈ inventory (endAt seed past) (input :: tail) :=
      partition.symm ▸ List.mem_append_left _ listed
    have later (item : Item) (listed : item ∈ inventory (endAt seed (past ++ [input])) tail) :
        item ∈ inventory (endAt seed past) (input :: tail) :=
      partition.symm ▸ List.mem_append_right _ listed
    have same := (endAt_input seed (past ++ [input])).trans (endAt_input seed past).symm
    refine ⟨⟨fun item listed => authority item (first item listed), ?_⟩, ?_, ?_⟩
    · intro position question asked _
      let item := (originalItems (seed := seed) past input)[position]
      have original := first item (List.getElem_mem position.isLt)
      change question ∈ questions (endAt seed past) item at asked
      change answers past input position question.1 = true
      exact answer_of_own_exposure (own item original) (answers past input position) (authored.1 position) question asked
    · intro position
      exact noGrants _ (first _ (List.getElem_mem position.isLt))
    · refine earlier (past := past ++ [input]) ?_ ?_ authored.2 ?_
      · intro item listed
        rw [same]
        exact authority item (later item listed)
      · intro item listed
        have personal := own item (later item listed)
        exact ⟨personal.1, fun question asked =>
          personal.2 question ((questions_read_the_same_input same item) ▸ asked)⟩
      · exact fun item listed => noGrants item (later item listed)

variable [DecidableEq Technology]
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}
  {seed : Root.Cut Party Good Port (State Party Technology) Instrument}
  {community : Party → Community}
  {anchor : Reparation.Actual.Script Party Good Port (State Party Technology) Instrument}
  {control : RawCurrent Party Good (State Party Technology) Instrument → List Party}
  {prior : GuardedVisit base scope seed community anchor control}
  {answers : OwnerAnswers seed}

theorem of_chosen (chosen : MandateExit.Chosen prior answers) :
    Checked seed community anchor answers prior.history chosen.word :=
  of_owned_word seed community anchor answers control prior.history chosen.word
    chosen.checked.1.1.original_authority chosen.checked.1.1.own chosen.authored
    (fun item listed => (chosen.checked.1.2 item listed).2)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment
