import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Runtime

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 5000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Regression

open Institutions.Capitalism.Universal.Source.Program
open Source

def start : Current := {initial with stock := fun _ _ => 10, clock := 1}
def proposal := request scope start false (.propose true)
def offered := Source.law.step start proposal
def acceptance := request scope offered true .accept
def held := Source.law.step offered acceptance
def renewalProposal := request scope held false (.propose true)
def reoffered := Source.law.step held renewalProposal
def renewal := request scope reoffered true .renew
def renewed := Source.law.step reoffered renewal
def exit := request scope renewed true .exit
def exited := Source.law.step renewed exit
def review := request scope exited false .review
def lifecycleWord : List Action := [proposal, acceptance, renewalProposal, renewal, exit, review]

theorem only_two_real_signatures_generate_the_holder :
    ¬ Source.law.Valid start (request scope start true .accept) ∧
    Source.law.Valid start proposal ∧ offered.technology.holder = none ∧
    ¬ Source.law.Valid offered (request scope offered false .accept) ∧
    Source.law.Valid offered acceptance ∧ held.technology.holder = some true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem actual_lifecycle_is_paid_and_preserves_original_claims :
    (Source.law.rawItems start lifecycleWord).all (fun item => decide (Source.law.Valid item.before item.request)) = true ∧
    (Source.law.next start lifecycleWord).technology.holder = none ∧
    (Source.law.next start lifecycleWord).technology.version = 6 ∧
    (Source.law.next start lifecycleWord).stock false () = 7 ∧
    (Source.law.next start lifecycleWord).stock true () = 7 ∧
    (Source.law.next start lifecycleWord).claims () false true = 7 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem versioned_acceptance_cannot_be_replayed :
    ¬ Source.law.Valid held acceptance ∧ Source.law.step held acceptance = held := by
  have refused : ¬ Source.law.Valid held acceptance := by decide +kernel
  exact ⟨refused, Source.law.rejected_preserves_current held acceptance refused⟩

theorem missing_gates_and_fresh_consents_do_not_create_a_mandate :
    ¬ Source.law.Valid start {necessity with gates := [], consents := [false]} ∧
    Source.law.Valid held {necessity with gates := [], consents := [false]} ∧
    ¬ Source.law.Valid exited {necessity with gates := [], consents := [false]} := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

def fakeGrant : Action :=
  {proposal with operation := .revise false {advance scope start (.propose true) with holder := some true}}

theorem a_proposal_name_cannot_install_a_holder : ¬ Source.law.Valid start fakeGrant := by decide +kernel

def alternateBase := {base with necessities := fun _ _ => [((), 1/2), ((), 1/2)]}
def alternateLaw := Mandate.law alternateBase scope
def disguised : Action := {necessity with gates := [], operation := .use false [((), 1/2), ((), 1/2)] .necessity}

theorem changing_the_bundle_representation_cannot_bypass_authority :
    ¬ alternateLaw.Valid start disguised ∧ alternateLaw.Valid held disguised := by
  constructor <;> decide +kernel

theorem unaffordable_acceptance_cannot_generate_a_grant :
    ¬ Source.law.Valid {offered with stock := fun _ _ => 0} acceptance ∧
    (grantsAt base scope {start with stock := fun _ _ => 0} [proposal, acceptance]).isEmpty = true := by
  constructor <;> decide +kernel

def late : Current := {held with clock := 11}
def lateReview := request scope late false .review

theorem renewal_never_refreshes_the_original_task_window :
    ¬ Source.law.Valid late necessity ∧
    ¬ Source.law.Valid late (request scope late false (.propose true)) ∧
    Source.law.Valid late lateReview ∧ (Source.law.step late lateReview).technology.holder = none ∧
    (Source.law.step late lateReview).claims () false true = 7 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def lifecycleSource : OutstandingSource Bool Unit Port (State Bool Unit) Unit where
  seed := {
    law := Source.law
    initial := {initial with stock := fun _ _ => 10}
    task := task
    actionsAt := alphabet
    budget := 4
    original := oldRequest :: lifecycleWord
    refused := by decide +kernel }
  positive := positive_task

theorem actual_exit_does_not_discharge_original_service :
    (lifecycleSource.actualExecution 0).after.technology.holder = none ∧
    (lifecycleSource.actualExecution 0).after.technology.version = 6 ∧
    (lifecycleSource.frameAt 2).payments ⟨0, by decide⟩ = none ∧
    (lifecycleSource.frameAt 2).payments ⟨1, by decide⟩ = none ∧
    (lifecycleSource.actualExecution 0).after.claims () false true = 7 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [lifecycleSource.actual_execution_after]; decide +kernel
  · rw [lifecycleSource.actual_execution_after]; decide +kernel
  · decide +kernel
  · decide +kernel
  · rw [lifecycleSource.actual_execution_after]; decide +kernel

theorem source_planner_remains_responsible_after_exit :
    (lifecycleSource.actualExecution 1).after.technology.holder = some true ∧
    lifecycleSource.pendingSlots (lifecycleSource.frameAt 3).payments = [] := by
  constructor
  · rw [lifecycleSource.actual_execution_after]; decide +kernel
  · decide +kernel

theorem actual_exit_keeps_native_service_live :
    (OutstandingSource.NativeService.historyAt lifecycleSource ⟨0, by decide⟩ 1).state.LiveAt 0 ∧
    (OutstandingSource.NativeService.historyAt lifecycleSource ⟨1, by decide⟩ 1).state.LiveAt 0 :=
  ⟨(OutstandingSource.NativeService.native_live_iff_unpaid _ _ _).mpr
      actual_exit_does_not_discharge_original_service.2.2.1,
    (OutstandingSource.NativeService.native_live_iff_unpaid _ _ _).mpr
      actual_exit_does_not_discharge_original_service.2.2.2.1⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Regression
