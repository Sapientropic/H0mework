import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Scope

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 24000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero

open Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Root

def daughter (index : Fin 2) : Party := index.val + 1

def nextDaughter (index : Fin 2) : Party := index.val + 6

/-- A resource review at the actual frame25, not an executed copy. -/
structure CopyReview (index : Fin 2) where
  attempt : CopyAttempt ((rawFrame 25).raw) (daughter index) (nextDaughter index)
  generated_attempt : attempt = attemptCopy ((rawFrame 25).raw) (daughter index) (nextDaughter index)
  deficit : Feedback.Deficit ((rawFrame 25).raw) (daughter index)
  original_deficit : deficit ∈ Feedback.deficits ((rawFrame 25).raw) (daughter index)
  resources_missing : ¬ CopyResources ((rawFrame 25).raw) (daughter index) (nextDaughter index)
  row : ProgrammeLedger.transferReceiptOf productionSource.input (productionSource.taskWrite 23).2 =
    some (productionSource.writtenReceipt 23)
  actual_after : (productionSource.actualExecution 23).after = (rawFrame 25).raw

theorem actual_next_copy_needs_real_resources : ∀ index : Fin 2,
    ¬ CopyResources ((rawFrame 25).raw) (daughter index) (nextDaughter index) ∧
      (Feedback.deficits ((rawFrame 25).raw) (daughter index)).isEmpty = false ∧
      (attemptCopy ((rawFrame 25).raw) (daughter index) (nextDaughter index)).isPaid = false := by
  decide +kernel

def copyReview (index : Fin 2) : CopyReview index :=
  let absent := actual_next_copy_needs_real_resources index
  let first := (Feedback.deficits ((rawFrame 25).raw) (daughter index)).head
    (List.isEmpty_eq_false_iff.mp absent.2.1)
  { attempt := attemptCopy ((rawFrame 25).raw) (daughter index) (nextDaughter index)
    generated_attempt := rfl
    deficit := first
    original_deficit := List.head_mem _
    resources_missing := absent.1
    row := productionSource.receipt_is_in_original_task_write 23
    actual_after := (productionSource.actualExecution 23).root_next_exact.trans
      (Participation.actual_current_is_the_machine true 25) }

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero
