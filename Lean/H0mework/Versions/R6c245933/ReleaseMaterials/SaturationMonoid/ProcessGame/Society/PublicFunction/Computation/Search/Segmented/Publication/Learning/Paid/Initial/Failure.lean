import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Initial

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 800000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Initial.Failure
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt.Information.Inquiry.Replay
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument] {fuel : Nat}
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code))
  (original : Rule model.source.code)
  (baseline : Whole.Program model.source.code fuel)

def legal (point : Cursor model.source.code) (rival : Opponent model.source.code) : Bool :=
  rawLegal point (controller point original baseline rival) (schedule point original baseline)

def complete (point : Cursor model.source.code) (rival : Opponent model.source.code) : Bool :=
  (List.finRange model.source.code.task.slots.length).all fun index =>
    (Identity.firstService (Cut.machine point.source point.entry point.cut
      (controller point original baseline rival) (schedule point original baseline))
      (Cut.finish point.source point.entry point.cut - 1) index).isSome

def row (point : Replanning.Point model domain) (rival : Opponent model.source.code)
    (test : Replanning.Test model domain point) : Replanning.Row model domain :=
  ⟨point,⟨externalTable point.val rival,Residual.restriction_is_generated _ _ _ _⟩,test⟩

theorem legal_is_original (point : Replanning.Point model domain) (rival : Opponent model.source.code) :
    legal model original baseline point.val rival = true ↔
      Selection.holds model domain original baseline baseline (row model domain point rival .legal) := by
  simp only [Selection.holds,Selection.readTable,row]
  rw [one_common_table_preserves_the_entire_actual_evaluation]
  rfl

theorem complete_is_original (point : Replanning.Point model domain) (rival : Opponent model.source.code) :
    complete model original baseline point.val rival = true ↔
      Selection.holds model domain original baseline baseline (row model domain point rival .complete) := by
  simp only [Selection.holds,Selection.readTable,row]
  rw [one_common_table_preserves_the_entire_actual_evaluation]
  rfl

/-- A single generated response can refute the original universal relation.
Its table membership is a proof, so refusal does not enumerate the table catalogue. -/
def inspectAt (point : Replanning.Point model domain) (rival : Opponent model.source.code) :
    Option (Selection.Rejection model domain original baseline baseline) :=
  if lawful : legal model original baseline point.val rival = true then
    if serviced : complete model original baseline point.val rival = true then none
    else some ⟨row model domain point rival .complete,Replanning.every_row_is_source_generated _ _ _,
      fun kept => serviced ((complete_is_original model domain original baseline point rival).mpr kept)⟩
  else some ⟨row model domain point rival .legal,Replanning.every_row_is_source_generated _ _ _,
    fun kept => lawful ((legal_is_original model domain original baseline point rival).mpr kept)⟩

/-- This prefix only generates original failures. Absence of a failure grants nothing. -/
def scan : List (Replanning.Point model domain) → Option (Selection.Rejection model domain original baseline baseline)
  | [] => none
  | point :: later =>
      match inspectAt model domain original baseline point PublicDomain.silent with
      | some rejected => some rejected
      | none => scan later

def generate := scan model domain original baseline (Replanning.points model domain)

theorem rejected_is_original (rejected : Selection.Rejection model domain original baseline baseline) :
    ¬ Selection.acceptable model domain original baseline baseline :=
  fun accepted => rejected.broken (accepted rejected.row rejected.generated)

/-- Failure is decisive; a clean prefix still enters the complete original checker. -/
@[noinline, never_extract] private def fullFallback :
    Decidable (Selection.acceptable model domain original baseline baseline) :=
  Initial.decider model domain original baseline

def decider : Decidable (Selection.acceptable model domain original baseline baseline) :=
  -- Keep the fallback behind a Boolean branch: a nullary match alternative
  -- can otherwise be evaluated before the source counterexample scan.
  if rejected : (generate model domain original baseline).isSome = true then
    .isFalse (by
      cases found : generate model domain original baseline with
      | none => simp only [found,Option.isSome_none,Bool.false_eq_true] at rejected
      | some reason => exact rejected_is_original model domain original baseline reason)
  else fullFallback model domain original baseline

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Initial.Failure
