import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.TaskShare.Recovery
import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.TaskShare.Solve

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.TaskShare

open Abolition.Root Abolition.Root.Registered Intervals

universe u

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {origin : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {meter : Meter.{u} origin}
  {exposure repair : List (Option (Compile.RawInput Party Good Port Technology Instrument))}

local notation "TaskAt" => Ordinal origin (exposure ++ repair)

structure TaskCatalogue (origin : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
    (exposure repair : List (Option (Compile.RawInput Party Good Port Technology Instrument))) where
  tasks : List (Ordinal origin (exposure ++ repair))
  exhaustive : ∀ task, task ∈ tasks

def TaskCatalogue.fromOriginalCount (count : Nat)
    (exactCount : count = (Execution.inventory origin (exposure ++ repair)).length) :
    TaskCatalogue origin exposure repair where
  tasks := (List.finRange count).map fun task => ⟨task.val, exactCount ▸ task.isLt⟩
  exhaustive := fun task => List.mem_map.mpr
    ⟨⟨task.val, exactCount.symm ▸ task.isLt⟩, by simp, Fin.ext rfl⟩

private def taskEquality : DecidableEq TaskAt := fun first second =>
  if same : first.val = second.val then isTrue (Fin.ext same)
  else isFalse (fun equal => same (congrArg Fin.val equal))

@[instance_reducible]
def TaskCatalogue.finite (catalogue : TaskCatalogue origin exposure repair) : Fintype TaskAt :=
  letI := taskEquality (origin := origin) (exposure := exposure) (repair := repair)
  Fintype.ofList catalogue.tasks catalogue.exhaustive

inductive ChargeOutcome (start : Cohort.Reading origin meter exposure)
    (whole : Cohort.Reading origin meter (exposure ++ repair)) (person : Party) (charges : TaskAt → ℚ)
    (catalogue : TaskCatalogue origin exposure repair)
  | missingExposure (issue : Missing start.source (start.reports.map ClockReading.observation))
  | missingContinuation (issue : Missing whole.source (whole.reports.map ClockReading.observation))
  | evaluated (decision : @Decision TaskAt catalogue.finite taskEquality
      (recoveryLog (repair := repair) start whole person) charges)
      (hours : length (allSpans (recoveryLog (repair := repair) start whole person)) =
        hoursThroughRepair origin meter exposure repair person)

structure AccountedCharges (start : Cohort.Reading origin meter exposure)
    (whole : Cohort.Reading origin meter (exposure ++ repair)) (person : Party) (charges : TaskAt → ℚ)
    (catalogue : TaskCatalogue origin exposure repair) where
  recovery : PaidRecovery origin exposure repair
  outcome : ChargeOutcome (repair := repair) start whole person charges catalogue

/-- Both original meter streams must be complete before the same
person's shared cells are charged. The original repair and its generated
successor accompany either acceptance or an exact rejected charge. -/
def solveRecovery (start : Cohort.Reading origin meter exposure)
    (whole : Cohort.Reading origin meter (exposure ++ repair)) (person : Party)
    (charges : TaskAt → ℚ) (catalogue : TaskCatalogue origin exposure repair)
    (paid : PaidRecovery origin exposure repair) :
    AccountedCharges (repair := repair) start whole person charges catalogue where
  recovery := paid
  outcome :=
    match PersonTime.read start.source (start.reports.map ClockReading.observation) with
    | .missing issue => .missingExposure issue
    | .complete startComplete =>
      match PersonTime.read whole.source (whole.reports.map ClockReading.observation) with
      | .missing issue => .missingContinuation issue
      | .complete wholeComplete =>
        .evaluated (@solve TaskAt catalogue.finite taskEquality
          (recoveryLog (repair := repair) start whole person) charges catalogue.tasks catalogue.exhaustive)
          (recovery_log_has_the_original_paid_personal_clock start whole startComplete wholeComplete person)

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.TaskShare
