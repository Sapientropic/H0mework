import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.GrantRegression

/-! Kernel controls distinguish new-window payment, old-window arrears,
literal terminal archives, and an actual visit that is not yet expired. -/

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 24000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Service.Regression

open Institutions.Capitalism.Universal.Source.Program ResponsibilityLifecycle Followup
noncomputable section
abbrev authority := Handoff.Regression.authority
abbrev fresh := Handoff.Regression.fresh
abbrev legacy := Handoff.Regression.reviewed
abbrev oldSource := (Pending.B authority).source

def terminalFlags := (List.finRange oldSource.seed.task.slots.length).map fun index =>
  match (Service.continued fresh (legacy.services index) 3).state.current.slots with
  | [.terminal _] => true
  | _ => false

def appendedKinds := (List.finRange oldSource.seed.task.slots.length).map fun index =>
  ((Service.continued fresh (legacy.services index) 3).state.current.history.drop
    (legacy.services index).state.current.history.length).map LifecycleEvent.kind

def actualDepths := (List.finRange oldSource.seed.task.slots.length).map fun index =>
  (OutstandingSource.History.NativeService.Expired.actualTrace oldSource []
    (Service.continued fresh (legacy.services index) 3).state.generated).map
      OutstandingSource.History.NativeService.ExpiredInput.depth

theorem actual_new_window_payment_maintains_every_expired_original_service :
    (Service.observations fresh 3).map OutstandingSource.History.NativeService.ExpiredInput.depth = [0,1,2] ∧
    terminalFlags = [false,false,false,false] ∧
    appendedKinds = List.replicate 4 [.maintained,.maintained,.maintained] ∧
    actualDepths = List.replicate 4 [0,1,2] := by decide +kernel

theorem new_service_really_pays_the_homologous_content :
    ∀ index, (source fresh).SlotPaid (start fresh) (firstWord fresh) index :=
  Handoff.Regression.reserved_new_epoch_really_pays_each_original_content_and_keeps_the_old_principal.2.1

theorem an_actual_early_visit_cannot_mint_an_expired_maintenance_observation :
    (OutstandingSource.History.NativeService.ExpiredInput.read oldSource oldSource [] 0).isNone = true := by decide +kernel

def archivedLate := Joint.submit authority (Joint.submit authority Joint.Regression.served []) []
def archivedReview := Future.advance authority archivedLate .revision

theorem an_actual_paid_service_archive_can_reach_a_new_scope :
    (Handoff.choose (Pending.B authority) archivedReview.inputs).isSome = true ∧
    Joint.Regression.terminalFlags archivedReview = [true,true,true,true] := by decide +kernel

def archivedFresh := (Handoff.choose (Pending.B authority) archivedReview.inputs).get
  an_actual_paid_service_archive_can_reach_a_new_scope.1

theorem actual_new_source_does_not_append_events_to_old_terminal_services :
    (List.finRange oldSource.seed.task.slots.length).map (fun index =>
      (Service.continued archivedFresh (archivedReview.services index) 3).state.current.history.length -
        (archivedReview.services index).state.current.history.length) = [0,0,0,0] := by decide +kernel

abbrev publicScopeCrossServiceLiveFacade := EpochRuntime.facade authority Handoff.Regression.late fresh
abbrev publicScopeCrossServiceArchivedFacade := EpochRuntime.facade authority archivedLate archivedFresh
abbrev publicScopeCrossServiceCapturedFacade := Grant.Regression.publicScopeCrossGrantRefusedFacade

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Service.Regression
