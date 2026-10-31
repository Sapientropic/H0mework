import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Plan
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge.Cross.Inventory

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle
open Followup

variable {fuel : ℚ} {inventory : Joint.Inventory fuel} (ready : Ready inventory) (inputs : List (List Action))

abbrev nextInputs := inputs ++ [emit ready inputs]
abbrev sourceInput := OutstandingSource.History.input (epochSource ready) (nextInputs ready inputs)
abbrev execution := OutstandingSource.History.actualExecution (epochSource ready) (nextInputs ready inputs) (inputs.length + 1)
abbrev afterCurrent := OutstandingSource.History.currentAt (epochSource ready) (nextInputs ready inputs) (inputs.length + 3)

theorem emitted_response_is_the_actual_next_word : (execution ready inputs).submitted = emit ready inputs :=
  Mandate.Challenge.Cross.emitted_word_is_actual (B ready) inputs _

theorem emitted_response_uses_the_actual_pending_cut : (execution ready inputs).before = current ready inputs :=
  Mandate.Challenge.Cross.emitted_word_uses_actual_cut (B ready) inputs _

theorem emitted_response_has_its_own_generated_after :
    afterCurrent ready inputs = (epochLaw ready).next (current ready inputs) (emit ready inputs) := by
  have actual := OutstandingSource.History.actual_next (epochSource ready) (nextInputs ready inputs) (inputs.length + 1)
  calc
    afterCurrent ready inputs = (execution ready inputs).after := actual.symm
    _ = (epochLaw ready).next (current ready inputs) (emit ready inputs) := by
      change (epochLaw ready).next (execution ready inputs).before (execution ready inputs).submitted = _
      rw [emitted_response_is_the_actual_next_word, emitted_response_uses_the_actual_pending_cut]

def beforeResidents := Mandate.Challenge.Cross.residentsAt (B ready) inputs

def carriedResidents := (beforeResidents ready inputs).map fun resident =>
  resident.advance (B ready) (emit ready inputs)

def newbornResidents := Mandate.Challenge.Cross.newborn (B ready) (inputs := inputs) (emit ready inputs)

def allResidents := Mandate.Challenge.Cross.advanceAll (B ready) (beforeResidents ready inputs) (emit ready inputs)

theorem whole_old_responsibility_inventory_is_consumed (resident : Mandate.Challenge.Cross.Resident (B ready) inputs)
    (inside : resident ∈ beforeResidents ready inputs) :
    resident.advance (B ready) (emit ready inputs) ∈ allResidents ready inputs :=
  Mandate.Challenge.Cross.every_old_resident_is_actually_consumed _ _ _ resident inside

def actual_response_run (resident : Mandate.Challenge.Cross.Resident (B ready) inputs) :=
  resident.responseRun (B ready) (emit ready inputs)

inductive Outcome where
  | private absent (noPending : request? ready inputs = none)
  | private paid (request : Request ready inputs) (selected : request? ready inputs = some request)
      (payment : Paid ready inputs request) (paid : choose ready inputs request = some payment)
  | private refused (request : Request ready inputs) (selected : request? ready inputs = some request)
      (unpaid : choose ready inputs request = none)
      (failedChecks : ∀ candidate ∈ menu ready inputs, ¬ Legal ready inputs request candidate)

def outcome : Outcome ready inputs :=
  match selected : request? ready inputs with
  | none => .absent selected
  | some request => match paid : choose ready inputs request with
    | some payment => .paid request selected payment paid
    | none => .refused request selected paid (blocked_menu_has_actual_failed_checks ready inputs request paid)

theorem paid_actual_response_removes_holder_and_offer (request : Request ready inputs)
    (selected : request? ready inputs = some request) (paid : Paid ready inputs request)
    (payment : choose ready inputs request = some paid) :
    (afterCurrent ready inputs).technology.holder = none ∧ (afterCurrent ready inputs).technology.offered = none := by
  rw [emitted_response_has_its_own_generated_after]
  change (((epochLaw ready).execute _ 0 _).final).technology.holder = none ∧ _
  simp only [emit, selected]
  exact (selected_word_is_actually_legal ready inputs request paid payment).2.2

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending
