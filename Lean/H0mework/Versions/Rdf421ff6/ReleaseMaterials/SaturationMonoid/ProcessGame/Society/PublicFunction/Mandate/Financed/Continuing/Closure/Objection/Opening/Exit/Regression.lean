import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Exit.Runtime
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Regression

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Exit.Regression

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle
open Followup

noncomputable section

def initialCut := Opening.Regression.empty
def fundHolder : Action := ⟨false, [], .resource, [], .transfer false true [(.service, 1)]⟩
def first := Joint.submit initialCut [fundHolder]
def exited := advance first

def ownGrant (inventory : Joint.Inventory 3) :=
  (grantsAt base scope (Runtime.mandateCurrentAt 3 (branchInputs inventory.cut (emit inventory)) 0)
    (Runtime.mandateWordAt 3 (branchInputs inventory.cut (emit inventory)) 0)).get ⟨0, by
      change 0 < (grantsAt base scope (law.next (initial 3) [])
        (SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.original 3)).length
      decide +kernel⟩

def released := readRelease first ⟨0, by decide⟩ (ownGrant first) ⟨1, by decide +kernel⟩

theorem source_pays_holder_exit_and_resolves_the_same_word_new_objection :
    first.cut.past.frame.raw.technology.holder = some true ∧
    (choose first.cut.past.frame.raw true).map Ready.method = some .direct ∧
    exited.cut.past.frame.raw.technology.holder = none ∧ released.isSome = true ∧
    Joint.Regression.histories exited = [[.admitted, .obligationTerminal]] ∧
    exited.cut.past.frame.raw.claims () false true = 7 := by decide +kernel

def release := released.get (by decide +kernel)

theorem actual_release_is_a_native_bearer_release :
    release.crossing.events.map LifecycleEvent.kind = [.bearerRelease] := by
  simp only [Lifecycle.Observed.Release.Receipt.crossing, NativeResponsibilityProcess.Run.events,
    List.nil_append, List.map_cons, List.map_nil]
  exact congrArg (fun kind => [kind]) release.native_kind

def legacy := Joint.Regression.legacy
def legacyExited := advance legacy

theorem every_old_objection_consumes_the_same_holder_exit :
    Joint.Regression.histories legacyExited =
      [[.admitted, .progressed, .progressed, .obligationTerminal], [.admitted, .progressed, .obligationTerminal]] ∧
    legacyExited.frame.rows.length = legacy.frame.rows.length := by decide +kernel

def drain (current : Current) : Action :=
  ⟨true, [], .resource, [], .transfer true false [(.service, current.stock true .service)]⟩

def cashless := Joint.submit first [drain first.cut.past.frame.raw]
def financed := advance cashless

theorem holder_borrows_on_its_own_account_before_its_real_exit :
    cashless.cut.past.frame.raw.stock true .service = 0 ∧
    (choose cashless.cut.past.frame.raw true).map Ready.method = some .loan ∧
    financed.cut.past.frame.raw.technology.holder = none ∧
    financed.cut.past.frame.raw.claims () true false = 1 ∧
    financed.cut.past.frame.raw.claims () false true = 7 := by decide +kernel

def productionBase := Joint.initial Response.Regression.repair

theorem the_holder_can_produce_and_exit_without_borrowing :
    (choose productionBase.cut.past.frame.raw true).map Ready.method = some .productive ∧
    (advance productionBase).cut.past.frame.raw.technology.holder = none ∧
    (advance productionBase).cut.past.frame.raw.stock true .service = 2 := by decide +kernel

def returnFeedstock : Action := ⟨true, [], .resource, [], .transfer true false [(.feedstock, 1)]⟩
def repair := Joint.submit productionBase [returnFeedstock]
def supplied := advance repair
def repairedExit := advance supplied

theorem real_feedstock_supply_drives_the_next_holder_owned_exit :
    (choose repair.cut.past.frame.raw true).isSome = false ∧
    (demands repair.cut.past.frame.raw true).map Demand.quantity = [1, 1] ∧
    supplied.cut.past.frame.raw.stock true .feedstock = 1 ∧
    supplied.cut.past.frame.raw.technology.holder = some true ∧
    (choose supplied.cut.past.frame.raw true).map Ready.method = some .productive ∧
    repairedExit.cut.past.frame.raw.technology.holder = none ∧
    Joint.Regression.histories repairedExit = [[.admitted, .progressed, .deferred, .progressed, .obligationTerminal]] := by decide +kernel

def blocked := Joint.initial Response.Regression.blocked
def blockedAgain := run blocked 2

theorem refused_exit_keeps_the_original_objection_and_principal :
    (choose blocked.cut.past.frame.raw true).isSome = false ∧
    (law.rawItems blocked.cut.past.frame.raw (emit blocked)).map (fun item => decide (law.Valid item.before item.request)) =
      [true, false, false, false, false] ∧
    Joint.Regression.histories blockedAgain = [[.admitted, .progressed, .deferred, .progressed, .deferred]] ∧
    blockedAgain.cut.past.frame.raw.claims () false true = 7 ∧
    blockedAgain.cut.past.frame.raw.technology.holder = some true := by decide +kernel

def blockedGrant :=
  (grantsAt base scope (Runtime.mandateCurrentAt 0 (branchInputs blocked.cut (emit blocked)) 0)
    (Runtime.mandateWordAt 0 (branchInputs blocked.cut (emit blocked)) 0)).get ⟨0, by
      change 0 < (grantsAt base scope (law.next (initial 0) [])
        (SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.original 0)).length
      decide +kernel⟩

theorem an_actual_unpaid_exit_does_not_generate_a_grant_release :
    (readRelease blocked ⟨0, by decide⟩ blockedGrant ⟨2, by decide +kernel⟩).isSome = false := by decide +kernel

def selfHeld := Opening.Regression.selfAuthority

theorem a_member_held_seat_also_uses_its_own_literal_exit :
    selfHeld.cut.past.frame.raw.technology.holder = some false ∧
    (advance selfHeld).cut.past.frame.raw.technology.holder = none ∧
    (advance selfHeld).frame.rows.length = 2 := by decide +kernel

theorem no_holder_continuation_preserves_the_first_objection_archive :
    Joint.Regression.histories (advance exited) = Joint.Regression.histories exited := by decide +kernel

def malformed : Action := {request scope first.cut.past.frame.raw true .exit with gates := []}
def nonholder := request scope first.cut.past.frame.raw false .exit
def review := request scope first.cut.past.frame.raw false .review
def staleExit := request scope first.cut.past.frame.raw true .exit

theorem wrong_signer_and_missing_gate_are_not_withdrawal_receipts :
    isHolderExit first.cut.past.frame.raw nonholder = false ∧
    isWithdrawal first.cut.past.frame.raw malformed = false ∧
    ¬ law.Valid first.cut.past.frame.raw nonholder ∧
    isWithdrawal (law.step first.cut.past.frame.raw review) staleExit = false := by decide +kernel

abbrev publicHolderExitFacade := ExitRuntime.facade first
abbrev publicHolderExitFinanceFacade := ExitRuntime.facade cashless
abbrev publicHolderExitBlockedFacade := ExitRuntime.facade blocked

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Exit.Regression
