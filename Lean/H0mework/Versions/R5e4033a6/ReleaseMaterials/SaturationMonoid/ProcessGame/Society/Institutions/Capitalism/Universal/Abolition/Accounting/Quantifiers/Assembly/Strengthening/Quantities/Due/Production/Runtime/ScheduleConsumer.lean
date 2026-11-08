import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production.Runtime.Schedule
import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production.Consumers.PreparedSource
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.PrimitiveClock

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production.Runtime.ScheduleConsumer

open Source.Program Abolition.Root Abolition.Root.Registered Execution
open Quantities.Consumers (lifeSource lifeTrace)
open Service.Consumers (firstNeed liveClock wholeFee)
open Production.Consumers.Prepared (OriginalLineAt beforePaymentAt
  the_external_row_keeps_its_exact_unpaid_unit_at original_ordered_rows)
open Innovation.Contribution.Pricing.Consumers.Actual (the_actual_quote_cut_comes_from_the_paid_original_food_repair)

private theorem original_clock : liveClock = 4 := by
  change lifeSource.raw.clock = 4
  rw [the_actual_quote_cut_comes_from_the_paid_original_food_repair]
  decide +kernel

private def row (deadline : ℚ) :
    RowRead (beforePaymentAt deadline) (fun _ => wholeFee) where
  row := firstNeed deadline
  remaining := 1
  earliest := min 4 deadline
  deadline := deadline
  bearer := false
  good := false
  purpose := .external
  signed := wholeFee
  remaining_exact := (the_external_row_keeps_its_exact_unpaid_unit_at deadline (firstNeed deadline)).symm
  earliest_exact := by
    change min 4 deadline = min liveClock deadline
    rw [original_clock]
  deadline_exact := rfl
  bearer_exact := rfl
  good_exact := rfl
  purpose_exact := rfl
  signed_exact := rfl

def input (deadline : ℚ) :
    ScheduleRead (beforePaymentAt deadline) (fun _ => wholeFee) where
  clock := 4
  clock_exact := original_clock.symm.trans (a_paid_primitive_trace_keeps_the_actual_clock lifeTrace).symm
  rows := [row deadline]
  rows_exact := (original_ordered_rows deadline).symm

def native (deadline : ℚ) : Sum (OriginalLineAt deadline) (RawEvent Bool Bool Bool Unit Unit) :=
  let loaded := input deadline
  (readWord loaded.clock loaded.rows RowRead.remaining RowRead.earliest RowRead.deadline
      (fun read => nativeRequest read.signed read.bearer read.good read.remaining read.purpose)).map
    RowRead.row id

theorem native_reads_the_original_checked_decision (deadline : ℚ) :
    native deadline = (schedule (input deadline)).readout := by
  have encode : (fun (read : RowRead (beforePaymentAt deadline) (fun _ => wholeFee)) =>
      nativeRequest read.signed read.bearer read.good read.remaining read.purpose) = RowRead.request := by
    funext read
    rfl
  simpa only [native, encode] using readWord_is_the_exact_schedule_readout (input deadline)

theorem the_checked_reader_builds_the_original_native_request : native 4 = .inr [wholeFee] := by
  rfl

theorem the_expired_native_request_names_the_original_row : native 3 = .inl (firstNeed 3) := by
  rfl

theorem the_future_original_row_is_deferred : native 5 = .inr [] := by
  rfl

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production.Runtime.ScheduleConsumer
