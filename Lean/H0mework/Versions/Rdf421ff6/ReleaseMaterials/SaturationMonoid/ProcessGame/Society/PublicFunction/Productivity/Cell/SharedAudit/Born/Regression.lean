import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Born.Runtime

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Born

open Institutions.Capitalism.Universal.Source.Program

def withoutNecessity : List Item := (itemsAt 6).filter fun item =>
  match item.request.operation with | .use _ _ .necessity => false | _ => true

def partialNecessity : List Item := (itemsAt 6).map fun item =>
  match item.request.operation with
  | .use actor _ .necessity => {item with request :=
      {item.request with operation := .use actor [(.life, 1 / 2)] .necessity}}
  | _ => item

def forgedSeedRequest : RequestAt := {(born 0).item.request with signer := 3}

theorem a_forged_seed_signature_is_refused :
    ¬ law.Valid (born 0).item.before forgedSeedRequest := by
  decide +kernel

theorem old_startup_payment_cannot_settle_a_newborn_service :
    (payments (born 0) .life 1).isEmpty = true ∧
      (payments (born 0) .maintenance 1).isEmpty = true := by
  decide +kernel

theorem a_real_post_birth_wait_keeps_the_new_duty_live (kind : Kind) :
    (Native.historyAt (born 0) kind 2).state.LiveAt 0 := by
  apply (Native.native_live_iff_unpaid _ _ _).mpr
  have unpaid : ∀ earlier : Fin 2, ¬ Paid (born 0) kind ((born 0).ordinal + earlier.val) := by
    cases kind <;> decide +kernel
  intro earlier bound
  exact unpaid ⟨earlier, bound⟩

theorem deletion_only_loses_the_deleted_service :
    (paymentsFrom (born 0) .life 6 withoutNecessity).isEmpty = true ∧
      (paymentsFrom (born 0) .maintenance 6 withoutNecessity).isEmpty = false := by
  decide +kernel

theorem partial_payment_cannot_close_the_whole_slot :
    (paymentsFrom (born 0) .life 6 partialNecessity).isEmpty = true ∧
      (paymentsFrom (born 0) .maintenance 6 partialNecessity).isEmpty = false := by
  decide +kernel

theorem late_replay_cannot_refresh_the_birth_window :
    (paymentsFrom (born 0) .life 8 (itemsAt 6)).isEmpty = true ∧
      (paymentsFrom (born 0) .maintenance 8 (itemsAt 6)).isEmpty = true := by
  decide +kernel

theorem source_admission_does_not_wait_for_a_successful_service (index : Fin 4) (kind : Kind) :
    (Native.admissionPayload (born index) kind).beneficiary = (born index).child ∧
      (Native.admissionPayload (born index) kind).residual = kind.goods ∧
      (Native.admissionPayload (born index) kind).lineage = (birthKey (born index), kind) ∧
      (Native.initial (born index) kind).state.LiveAt 0 :=
  ⟨rfl, rfl, rfl, newborn_obligation_is_initially_live index kind⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Born
