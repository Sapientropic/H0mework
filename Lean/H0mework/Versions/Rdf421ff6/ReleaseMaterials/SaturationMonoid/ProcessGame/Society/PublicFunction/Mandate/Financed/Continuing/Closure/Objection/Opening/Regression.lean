import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Runtime
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Joint.Regression

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Regression

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle
open Followup

noncomputable section

def empty := Joint.Regression.empty
def first := advance empty

theorem source_signs_without_any_preexisting_objection_and_consumes_its_own_suffix :
    empty.frame.rows.length = 0 ∧ (emit empty).head?.map isSubmission = some true ∧
    Joint.Regression.histories first = [[.admitted, .obligationTerminal]] ∧
    first.cut.past.frame.raw.technology.holder = none := by decide +kernel

def stale := Joint.Regression.changed
def settled := advance stale

theorem one_source_signature_reconfirms_every_old_snapshot_then_retires_the_seat :
    stale.frame.rows.length = 2 ∧ settled.frame.rows.length = 2 ∧
    Joint.Regression.histories settled =
      [[.admitted, .progressed, .progressed, .obligationTerminal], [.admitted, .progressed, .obligationTerminal]] ∧
    settled.cut.past.frame.raw.technology.holder = none := by decide +kernel

def financed := Joint.initial Response.Regression.financed
def funded := advance financed

theorem actual_loan_is_consumed_after_the_same_source_signature :
    (select financed.cut.past.frame.raw).method = .loan true ∧
    Joint.Regression.histories funded = [[.admitted, .progressed, .obligationTerminal]] ∧
    funded.cut.past.frame.raw.claims () false true = 8 ∧
    funded.cut.past.frame.raw.technology.holder = none := by decide +kernel

def repair := Joint.initial Response.Regression.repair
def repaired := advance repair
def released := advance repaired

theorem actual_supply_changes_the_next_cut_and_drives_the_next_paid_opening :
    (select repair.cut.past.frame.raw).isPaid = false ∧ (demands repair.cut.past.frame.raw).length = 2 ∧
    (law.rawItems repair.cut.past.frame.raw (emit repair)).map (fun item => decide (law.Valid item.before item.request)) =
      [true, false, false, true, false] ∧
    repaired.cut.past.frame.raw.stock false .feedstock = 1 ∧
    (select repaired.cut.past.frame.raw).method = .productive ∧
    released.cut.past.frame.raw.technology.holder = none ∧
    Joint.Regression.histories released = [[.admitted, .progressed, .deferred, .progressed, .obligationTerminal]] := by decide +kernel

def blocked := Joint.initial Response.Regression.blocked
def twiceBlocked := run blocked 2

theorem no_resources_still_generates_actual_signatures_and_exact_refused_supplies :
    (select blocked.cut.past.frame.raw).isPaid = false ∧
    (demands blocked.cut.past.frame.raw).map Demand.quantity = [1, 1] ∧
    (law.rawItems blocked.cut.past.frame.raw (emit blocked)).map (fun item => decide (law.Valid item.before item.request)) =
      [true, false, false, false, false] ∧
    Joint.Regression.histories twiceBlocked = [[.admitted, .progressed, .deferred, .progressed, .deferred]] ∧
    twiceBlocked.cut.past.frame.raw.claims () false true = 7 ∧
    twiceBlocked.cut.past.frame.raw.technology.holder = some true := by decide +kernel

def inactive := advance first

theorem an_inactive_seat_preserves_the_original_terminal_archive :
    Joint.Regression.histories inactive = Joint.Regression.histories first ∧
    inactive.frame.rows.length = first.frame.rows.length := by decide +kernel

def selfProposal := request scope first.cut.past.frame.raw false (.propose false)
def selfAcceptance := request scope (law.step first.cut.past.frame.raw selfProposal) false .accept
def selfAuthority := Joint.submit first [selfProposal, selfAcceptance]
def selfOpened := advance selfAuthority

theorem a_member_held_seat_does_not_hide_the_other_supply_address :
    selfAuthority.cut.past.frame.raw.technology.holder = some false ∧
    (emit selfAuthority).head?.map isSubmission = some true ∧
    (.loan true ∈ methods) ∧
    selfOpened.frame.rows.length = 2 := by decide +kernel

abbrev publicSourceOpeningFacade := OpeningRuntime.facade empty
abbrev publicSourceOpeningRepairFacade := OpeningRuntime.facade repair
abbrev publicSourceOpeningBlockedFacade := OpeningRuntime.facade blocked

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Regression
