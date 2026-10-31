import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Runtime

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 48000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero

open ResponsibilityLifecycle
open Institutions.Capitalism.Universal.Source.Program

def withoutDaughterLife : List Occurrence := (occurrences 25).filter fun occurrence =>
  match occurrence.item.request.operation with
  | .use actor _ .necessity => decide (actor ≠ 1)
  | _ => true

theorem removing_life_does_not_remove_maintenance :
    (Raw.payments withoutDaughterLife (Raw.newborn (born ⟨0, by decide⟩) .life)).isEmpty = true ∧
      (Raw.payments withoutDaughterLife (Raw.newborn (born ⟨0, by decide⟩) .maintenance)).isEmpty = false := by
  decide +kernel

def remainingService (kind : Kind) : Prop :=
  (Raw.payments withoutDaughterLife (Raw.newborn (born ⟨0, by decide⟩) kind)).isEmpty = false

instance : DecidablePred remainingService := by intro kind; unfold remainingService; infer_instance

def rejectionKind : Option Kind := match Check.run [.life, .maintenance] remainingService with
  | .accepted _ => none
  | .rejected failure => some failure.row

theorem deletion_generates_the_exact_typed_rejection : rejectionKind = some .life := by
  decide +kernel

theorem half_payment_or_expired_window_cannot_close_the_whole_slot :
    (Raw.payments (occurrences 25) { Raw.newborn (born ⟨0, by decide⟩) .life with goods := [(.life, 2)] }).isEmpty = true ∧
      (Raw.payments (occurrences 25) { Raw.newborn (born ⟨0, by decide⟩) .life with deadline := 0 }).isEmpty = true := by
  decide +kernel

theorem admission_is_live_before_any_payment (index : Fin 4) (kind : Kind) :
    (Newborn.historyAt (born index) kind 0).state.LiveAt 0 :=
  ⟨Newborn.obligation (born index) kind, rfl⟩

theorem new_source_archive_survives_every_finite_successor (index : Fin 4) (kind : Kind) (later : Nat) :
    (Newborn.historyAt (born index) kind (25 - (born index).ordinal + later)).state =
      (Newborn.historyAt (born index) kind (25 - (born index).ordinal)).state := by
  apply Newborn.terminal_state_is_preserved
  apply (Ledger.terminal_flag_iff _).mp
  exact Ledger.actual_ledger_rows_hold (.bornService index kind)

theorem refusing_a_role_does_not_admit_a_fictitious_duty :
    (rawFrame 20).register 2 = .declined ∧ (rawFrame 25).register 2 = .declined ∧
      (Participation.joining true).actor = 1 := by
  decide +kernel

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero
