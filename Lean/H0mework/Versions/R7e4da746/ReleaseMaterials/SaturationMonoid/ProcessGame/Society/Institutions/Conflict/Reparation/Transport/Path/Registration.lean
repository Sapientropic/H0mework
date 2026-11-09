import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport.Path.Run

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (query next)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]
  {source : Root.Cut Party Good Port Technology Instrument}
  {attack : RawEvent Party Good Port Technology Instrument}
  {community : Party → Community} {key : Key Party Good}
  (claim : ClaimAt source attack community key)

local notation "Input" => Option (Compile.RawInput Party Good Port Technology Instrument)
local notation "Script" => List Input

/-- At every registration selected on the original trajectory, the same
filed entry is the action's authority and the next input uses its landing. -/
theorem every_original_registration_transports_the_live_account (past : Script) (input : Input)
    (work : NativeWork (query (originalAt claim past) input))
    {registered : Admission.Registration (query (originalAt claim past) input).native}
    (selected : registrationAt (query (originalAt claim past) input) = some registered) :
    let before := run claim past
    let after := run claim (past ++ [input])
    let action := (step before input).emission
    action = .admission
      (Admission.generated (before.resident.atQuery (cut := originalAt claim past) input) registered work) ∧
    action.next = after.resident.erase ∧
    after.position.phase = before.position.phase ∧
    recordedDue source attack (past ++ [input]) community key =
      recordedDue source attack past community key ∧
    (originalAt claim (past ++ [input])).raw = (originalAt claim past).raw := by
  dsimp only
  refine ⟨the_original_registration_is_consumed_at_this_visit _ _ work selected,
    every_input_consumes_the_original_whole_ledger claim past input, ?_, ?_, ?_⟩
  · rw [run_snoc, step_is_registration _ _ work selected]
    exact Step.registered_keeps_phase _ _ work registered selected
  · apply recordedDue_append_without_receipts
    intro item listed
    rw [native_step_has_no_material_items input work] at listed
    exact (List.not_mem_nil listed).elim
  · have literal := Quantities.Execution.effective_step (originalAt claim past) input
    rw [(Optimality.Programme.Epoch.native_accounting_has_no_second_material_submission
      (query (originalAt claim past) input) work).1] at literal
    have raw := congrArg (fun state => state.raw) literal
    unfold originalAt
    rw [Quantities.Execution.endAt_append]
    exact raw.symm

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport
