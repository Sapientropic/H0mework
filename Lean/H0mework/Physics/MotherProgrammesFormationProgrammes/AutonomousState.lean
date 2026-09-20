import H0mework.Physics.MotherProgrammesFormationProgrammes.ExecutionRun

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.AutonomousProgrammes

open Stage9C.Revision MotherFamilyOccurrence StageEightDiscreteFormation
open MotherProgrammes MotherProgrammeExecution

noncomputable section

def initialCell : Cell := (0, WholePointFormation.initial.2)

def origin (round : ℕ) (cell : Cell) : MotherVisit :=
  RationalSourceFormation.pastVisit (view cell).1 round

def selected (round : ℕ) (cell : Cell) : List Entry := programmeAt (origin round cell)

/-- The next round continues the entire completed cell and executes one
extra original zero event, including after an empty programme. -/
def advance (round : ℕ) (cell : Cell) : Cell :=
  let completed := MotherProgrammeExecution.run cell (selected round cell)
  (completed.1 + 1, completed.2)

def roundCell : ℕ → Cell
  | 0 => initialCell
  | round + 1 => advance round (roundCell round)

def roundOrigin (round : ℕ) : MotherVisit := origin round (roundCell round)
def roundProgramme (round : ℕ) : List Entry := selected round (roundCell round)

theorem advance_late (round : ℕ) (cell : Cell) : cell.1 < (advance round cell).1 := by
  have bound := index_mono cell (selected round cell)
  change cell.1 < (MotherProgrammeExecution.run cell (selected round cell)).1 + 1
  omega

theorem round_progress (round : ℕ) : (roundCell round).1 < (roundCell (round + 1)).1 :=
  advance_late round (roundCell round)

theorem round_bound (round : ℕ) : round ≤ (roundCell round).1 := by
  induction round with
  | zero => exact Nat.zero_le _
  | succ round induction =>
      exact Nat.succ_le_of_lt (lt_of_le_of_lt induction (round_progress round))

theorem origin_code (round : ℕ) : codeOf (roundOrigin round) = round := by
  apply RationalSourceFormation.past_code
  change round ≤ codeOf (SpinPair.visit (10 + (roundCell round).1))
  rw [code_at]
  exact round_bound round

theorem origin_whole_prefix (round : ℕ) :
    roundOrigin round = ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceNativeTemporalVisitAt.finite
      (RationalSourceFormation.historyPrefix (finiteVisit (view (roundCell round)).1).history
        (originDepth + round)) := rfl

theorem origin_is_past (round : ℕ) :
    temporalDepth (roundOrigin round).history ≤ temporalDepth (view (roundCell round)).1.history :=
  RationalSourceFormation.past_depth_le _ _

private def dataAtShape (visit : MotherVisit) (shape : ℕ × ℕ) : List MotherProgrammes.Datum :=
  (List.ofFn (fun slot : Fin shape.1 => entryAt
    (RationalSourceFormation.pastVisit visit (RationalSourceFormation.unpack shape.1 shape.2 slot)))).map Entry.data

theorem programme_data_same_code (first last : MotherVisit) (same : codeOf first = codeOf last) :
    (programmeAt first).map Entry.data = (programmeAt last).map Entry.data := by
  change dataAtShape first (codeOf first).unpair = dataAtShape last (codeOf last).unpair
  rw [same]
  simp only [dataAtShape, List.map_ofFn]
  apply congrArg List.ofFn
  funext slot
  apply entry_data_same_code
  have bound : RationalSourceFormation.unpack (codeOf last).unpair.1
      (codeOf last).unpair.2 slot ≤ codeOf last :=
    (RationalSourceFormation.unpack_le _ _ slot).trans (Nat.unpair_right_le _)
  rw [RationalSourceFormation.past_code _ _ (by simpa only [same] using bound),
    RationalSourceFormation.past_code _ _ bound]

theorem round_programme_data (round : ℕ) :
    (roundProgramme round).map Entry.data = (programmeAt (SpinPair.visit (10 + round))).map Entry.data :=
  programme_data_same_code (roundOrigin round) (SpinPair.visit (10 + round)) (by rw [origin_code, code_at])

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.AutonomousProgrammes
