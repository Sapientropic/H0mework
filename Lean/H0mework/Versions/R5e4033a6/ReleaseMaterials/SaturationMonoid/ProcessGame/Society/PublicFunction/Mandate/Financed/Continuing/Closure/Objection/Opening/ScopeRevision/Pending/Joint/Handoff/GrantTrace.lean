import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.GrantInventory

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Grant

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
variable {oldScope : Mandate.Scope (Party := Bool) (Good := Good) (Port := Mandate.Source.Port)}
  {bound : BoundSource base oldScope} {inputs : List (List Action)} (fresh : Handoff.Ready bound inputs)
  (prior : NativeResponsibilityProcess V)
noncomputable section

def edgeTrace {source : ResponsibilityState V} (edge : (process fresh prior).Edge source) : List (Receipt fresh) := by
  cases edge with
  | admit event => exact []
  | reopen slot archive present event => exact []
  | cross slot obligation present event =>
      change Boundary fresh prior obligation at event
      cases event with
      | inherited _ => exact []
      | actual receipt => exact [receipt]

def actualTrace {source target : ResponsibilityState V} : (process fresh prior).Run source target → List (Receipt fresh)
  | .nil => []
  | .step path edge => actualTrace path ++ edgeTrace fresh prior edge

theorem actualTrace_inherited {source target : ResponsibilityState V} (path : prior.Run source target) :
    actualTrace fresh prior (inheritRun fresh prior path) = [] := by
  induction path with
  | nil => rfl
  | step path edge ih =>
    cases edge with
    | admit event => simpa only [inheritRun,actualTrace,edgeTrace,List.append_nil] using ih
    | reopen slot archive present event => simpa only [inheritRun,actualTrace,edgeTrace,List.append_nil] using ih
    | cross slot obligation present event =>
      change actualTrace fresh prior (inheritRun fresh prior path) ++ [] = []
      rw [ih]
      rfl

theorem actualTrace_concat {source middle target : ResponsibilityState V}
    (first : (process fresh prior).Run source middle) (second : (process fresh prior).Run middle target) :
    actualTrace fresh prior (first.concatRuns _ second) = actualTrace fresh prior first ++ actualTrace fresh prior second := by
  induction second with
  | nil => exact (List.append_nil _).symm
  | step path edge ih => simp only [NativeResponsibilityProcess.Run.concatRuns,actualTrace,ih,List.append_assoc]

theorem Thread.consume_actualTrace {origin : ResponsibilityState V} {obligation : AdmittedObligation V}
    (thread : Thread fresh prior origin obligation) (actual : List (Receipt fresh)) :
    actualTrace fresh prior (thread.consume actual).crossing = actualTrace fresh prior thread.crossing ++ actual := by
  induction actual generalizing thread with
  | nil => exact (List.append_nil _).symm
  | cons receipt rest ih =>
    change actualTrace fresh prior ((thread.step receipt).consume rest).crossing = _
    rw [ih]
    change (_ ++ [receipt]) ++ rest = _ ++ (receipt :: rest)
    simp only [List.append_assoc,List.singleton_append]

variable {prior}

theorem fullRun_actualTrace_is_the_complete_original_receipt_list
    (record : Mandate.Challenge.Cross.GrantResident bound inputs) (count : Nat) :
    actualTrace fresh (Grant.prior record) (fullRun fresh record count) = receipts fresh 0 count := by
  rw [fullRun,actualTrace_concat,actualTrace_inherited]
  change [] ++ actualTrace fresh (Grant.prior record)
    ((Thread.begin record.history.state record.history.obligation record.history.slots).consume (receipts fresh 0 count)).crossing = _
  rw [Thread.consume_actualTrace]
  rfl

theorem Receipt.running (receipt : Receipt fresh) : 0 < receipt.ordinal fresh := by
  by_contra notRunning
  have zero := Nat.eq_zero_of_not_pos notRunning
  have empty : wordAt fresh 0 = [] := (OutstandingSource.History.actual_frame (source fresh) (epochInputs fresh) 0).2
  let raw := (receipt.item fresh).val
  have member : raw ∈ (law fresh).rawItems (current fresh (receipt.ordinal fresh)) (wordAt fresh (receipt.ordinal fresh)) :=
    (receipt.item fresh).property
  rw [zero,empty] at member
  exact List.not_mem_nil member

theorem Receipt.item_is_in_the_actual_submission (receipt : Receipt fresh) :
    (receipt.item fresh).val ∈ (law fresh).rawItems
      (actual fresh (receipt.ordinal fresh - 1)).before
      (actual fresh (receipt.ordinal fresh - 1)).submitted := by
  have ordinal : receipt.ordinal fresh - 1 + 1 = receipt.ordinal fresh := by have := receipt.running fresh; omega
  change (receipt.item fresh).val ∈ (law fresh).rawItems
    (current fresh (receipt.ordinal fresh - 1 + 1)) (wordAt fresh (receipt.ordinal fresh - 1 + 1))
  rw [ordinal]
  exact (receipt.item fresh).property

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Grant
