import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Runtime

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Regression

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle

noncomputable section

def first := start 3 []
def drain : Action := ⟨false, [], .resource, [], .transfer false true [(.service, first.past.frame.raw.stock false .service)]⟩
def challengeWord : List Action := [drain, submission]
def challenged := afterInput first challengeWord

def refusedWord : List Action := [request scope challenged.past.frame.raw false .revoke]
def fund : Action := ⟨true, [], .resource, [], .transfer true false [(.service, 1)]⟩
def fundedWord : List Action := [fund, request scope (law.step challenged.past.frame.raw fund) false .revoke]

def futureWord (funded : Bool) := if funded then fundedWord else refusedWord

def claim (funded : Bool) : Claim 3 (branchInputs challenged (futureWord funded)) :=
  (claimsAt 3 (branchInputs challenged (futureWord funded)) 2).get ⟨0, by
    cases funded <;> decide +kernel⟩

def kinds (funded : Bool) :=
  (through 3 (branchInputs challenged (futureWord funded)) (claim funded) 4).state.current.history.map LifecycleEvent.kind

theorem zero_revision_stock_still_admits_an_actual_challenge :
    challenged.past.frame.raw.stock false .service = 0 ∧
    challenged.past.frame.raw.technology.holder = some true ∧
    challenged.past.frame.raw.clock = first.past.frame.raw.clock + 1 ∧
    (claim false).position.ordinal = 2 ∧
    (claim false).position.index.val = 1 ∧
    (through 3 (branchInputs challenged refusedWord) (claim false) 3).state.current.LiveAt 0 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  apply History.live_of_pending
  decide +kernel

theorem actual_refusal_keeps_the_challenge_live :
    kinds false = [.admitted, .deferred] ∧
    (through 3 (branchInputs challenged refusedWord) (claim false) 4).state.current.LiveAt 0 := by
  refine ⟨by decide +kernel, ?_⟩
  apply History.live_of_pending
  decide +kernel

theorem actual_funding_and_same_snapshot_revoke_settle_the_challenge :
    kinds true = [.admitted, .obligationTerminal] ∧
    (afterInput challenged fundedWord).past.frame.raw.technology.holder = none ∧
    (afterInput challenged fundedWord).past.frame.raw.stock false .service = 0 := by decide +kernel

def malformed : List Action := [{submission with gates := []}]
def nonmember : List Action := [{submission with signer := true}]
def ordinary : List Action := [{submission with purpose := .resource, gates := []}]

theorem received_present_is_not_sufficient_for_native_admission :
    (claimsAt 3 (branchInputs first malformed) 2).length = 0 ∧
    (claimsAt 3 (branchInputs first nonmember) 2).length = 0 ∧
    (claimsAt 3 (branchInputs first ordinary) 2).length = 0 := by decide +kernel

theorem accepted_raw_present_does_not_bypass_the_registered_shape :
    law.Valid first.past.frame.raw {submission with gates := []} ∧
    law.Valid first.past.frame.raw {submission with signer := true} ∧
    law.Valid first.past.frame.raw {submission with purpose := .resource, gates := []} := by decide +kernel

def fundTwo : Action := ⟨true, [], .resource, [], .transfer true false [(.service, 2)]⟩
def review : Action := request scope (law.step challenged.past.frame.raw fundTwo) false .review

def changedSnapshotWord : List Action :=
  [fundTwo, review, request scope (law.step (law.step challenged.past.frame.raw fundTwo) review) false .revoke]

def changedClaim : Claim 3 (branchInputs challenged changedSnapshotWord) :=
  (claimsAt 3 (branchInputs challenged changedSnapshotWord) 2).get ⟨0, by decide +kernel⟩

theorem valid_revoke_of_another_snapshot_cannot_settle_this_challenge :
    (law.rawItems challenged.past.frame.raw changedSnapshotWord).all
      (fun item => decide (law.Valid item.before item.request)) = true ∧
    (afterInput challenged changedSnapshotWord).past.frame.raw.technology.holder = none ∧
    (through 3 (branchInputs challenged changedSnapshotWord) changedClaim 4).state.current.history.map
      LifecycleEvent.kind = [.admitted] ∧
    (through 3 (branchInputs challenged changedSnapshotWord) changedClaim 4).state.current.LiveAt 0 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  apply History.live_of_pending
  decide +kernel

abbrev publicObjectionFacade := ObjectionRuntime.facade challenged refusedWord
abbrev publicResolvedObjectionFacade := ObjectionRuntime.facade challenged fundedWord

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Regression
