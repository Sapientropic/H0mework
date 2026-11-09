import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Exit.DueWindow
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.Drain

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Consumers.Renewable.Native

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Civil.Persistence
open Quantities

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]

local notation "C" => Conflict.Root.Cut Party Good Port Technology Instrument
local notation "W" => Window Party Good Port Technology Instrument
local notation "Word" => Civil.Persistence.Script Party Good Port Technology Instrument
local notation "Cell" => Party × Use × Good × ℚ

abbrev nativePrefix (_cut : C) (count : Nat) : Word := Execution.nativePayments count

private theorem next_original_tick (cut : C) (count : Nat) :
    nativePrefix cut (count + 1) = nativePrefix cut count ++ [none] := List.replicate_succ'

omit [DecidableEq Community] in
theorem at_native_prefix (cut : C) (count : Nat) (within : count ≤ Execution.remainingNative cut) :
    (Window.at cut).run (nativePrefix cut count) = (⟨cut, nativePrefix cut count⟩ : W) := by
  induction count with
  | zero => rfl
  | succ count prior =>
    let window : W := ⟨cut, nativePrefix cut count⟩
    have front := Execution.an_original_native_prefix_preserves_material_and_pays_exactly_its_length
      cut count (by omega : count ≤ Execution.remainingNative cut)
    have whole := Execution.an_original_native_prefix_preserves_material_and_pays_exactly_its_length
      cut (count + 1) within
    have exactNext : window.nextCut none = Execution.endAt cut (nativePrefix cut (count + 1)) := by
      rw [next_original_tick, Execution.endAt_append]
      rfl
    have noCross : ¬ window.crosses none := by
      unfold Window.crosses
      rw [exactNext, whole.2.1]
      change ¬ (Execution.endAt cut (nativePrefix cut count)).raw.clock < cut.raw.clock
      rw [front.2.1]
      exact lt_irrefl _
    rw [next_original_tick, Window.run_append, prior (by omega)]
    change (window.run [none]) = _
    simp only [Window.run, Window.write, if_neg noCross]
    rfl

omit [DecidableEq Community] in
theorem the_native_drain_keeps_the_actual_open_window (cut : C) :
    (Window.at cut).run (Execution.drain cut) = (⟨cut, Execution.drain cut⟩ : W) :=
  at_native_prefix cut _ le_rfl

omit [DecidableEq Community] in
theorem timely_after_native_prefix (cut : C) (count : Nat) (within : count ≤ Execution.remainingNative cut)
    (deadline : ℚ) (command : List Party) (cell : Cell) (tail : Word) :
    timelyUses deadline command cell cut (nativePrefix cut count ++ tail) =
      timelyUses deadline command cell (Execution.endAt cut (nativePrefix cut count)) tail := by
  induction count generalizing cut with
  | zero => rfl
  | succ count prior =>
    have pending := (Execution.pending_iff_positive_original_positions cut).mpr (by omega)
    have spent := Execution.a_native_payment_spends_one_original_position cut pending
    have items : Boundary.Actual.items cut none = [] :=
      (Execution.an_original_native_prefix_preserves_material_and_pays_exactly_its_length
        cut 1 (by omega)).2.2
    change (if (Execution.next cut none).raw.clock ≤ deadline then
      (((Boundary.Actual.items cut none).filter (fun item => decide (OwnMaterial cut command item))).map
        (fun item => flowAt (Optimality.Cost.actualPart cut.native.handlerFace.rootRead item.before item.request
          (.use cell.2.1)) cell.1 cell.2.2.1)).sum else 0) +
      timelyUses deadline command cell (Execution.next cut none) (nativePrefix cut count ++ tail) = _
    simp only [items, List.filter_nil, List.map_nil, List.sum_nil, ite_self, zero_add]
    exact prior (Execution.next cut none) (by omega)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Consumers.Renewable.Native
