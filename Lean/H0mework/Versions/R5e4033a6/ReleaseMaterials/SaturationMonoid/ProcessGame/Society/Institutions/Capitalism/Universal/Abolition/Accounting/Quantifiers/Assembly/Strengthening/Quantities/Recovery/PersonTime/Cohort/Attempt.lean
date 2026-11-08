import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Cohort.Budget
import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Cohort.Metering

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Cohort

open Abolition.Root Abolition.Root.Registered

universe u

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {origin : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {meter : Meter.{u} origin}
  {exposure repair : List (Option (Compile.RawInput Party Good Port Technology Instrument))}

local notation "A" => Address origin meter exposure
local notation "Limits" => List (A × ℚ)

private inductive LimitCheck (values : A → ℚ) (limits : Limits)
  | fit (within : ∀ entry ∈ limits, values entry.1 ≤ entry.2)
  | excess (entry : A × ℚ) (listed : entry ∈ limits) (short : entry.2 < values entry.1)

private def inspectLimits (values : A → ℚ) : (limits : Limits) → LimitCheck values limits
  | [] => .fit (fun _ absent => (List.not_mem_nil absent).elim)
  | entry :: later =>
    if within : values entry.1 ≤ entry.2 then
      match inspectLimits values later with
      | .fit checked =>
        .fit (fun address listed => (List.mem_cons.mp listed).elim (fun equal => equal.symm ▸ within) (checked address))
      | .excess address listed short => .excess address (List.mem_cons_of_mem _ listed) short
    else .excess entry List.mem_cons_self (lt_of_not_ge within)

inductive Attempt (start : Reading origin meter exposure) (full : Reading origin meter (exposure ++ repair))
    (limits : Limits)
  | paid (settlement : PaidRecovery origin exposure repair)
      (values : A → ℚ) (exactValues : ∀ address, values address = amount origin meter exposure repair address)
      (within : ∀ entry ∈ limits, values entry.1 ≤ entry.2)
  | accounting (issue : Obstruction (Execution.endAt origin exposure) repair)
  | shortage (loss : Loss origin exposure repair)
  | missingExposure (issue : Missing start.source (start.reports.map ClockReading.observation))
  | missingContinuation (issue : Missing full.source (full.reports.map ClockReading.observation))
  | excess (entry : A × ℚ) (listed : entry ∈ limits)
      (short : entry.2 < amount origin meter exposure repair entry.1)

structure RecordedAttempt (start : Reading origin meter exposure) (full : Reading origin meter (exposure ++ repair))
    (limits : Limits) where
  whole : Recorded origin (exposure ++ repair)
  outcome : Attempt (repair := repair) start full limits

/-- A submitted repair is checked through its one physical execution.
Verified readings and finite rational allowances are evaluated together
on that same word before it is accepted. -/
noncomputable def inspectMeasured (start : Reading origin meter exposure)
    (full : Reading origin meter (exposure ++ repair)) (limits : Limits) :
    RecordedAttempt (repair := repair) start full limits where
  whole := record origin _
  outcome :=
    match decideAt (Execution.endAt origin exposure) repair with
    | .blocked issue => .accounting issue
    | .feasible paid =>
      match physical : Recovery.inspect origin exposure repair with
      | some loss => .shortage loss
      | none =>
        match readTogether (repair := repair) start full with
        | .missingExposure issue => .missingExposure issue
        | .missingContinuation issue => .missingContinuation issue
        | .ready values exactValues =>
          match inspectLimits values limits with
          | .excess entry listed short => .excess entry listed ((exactValues entry.1) ▸ short)
          | .fit within =>
            .paid ⟨settle _ _ paid,
              (cleared_exactly_when_no_original_actor_loses_stock origin exposure repair).mp physical,
              record origin _⟩ values exactValues within

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Cohort
