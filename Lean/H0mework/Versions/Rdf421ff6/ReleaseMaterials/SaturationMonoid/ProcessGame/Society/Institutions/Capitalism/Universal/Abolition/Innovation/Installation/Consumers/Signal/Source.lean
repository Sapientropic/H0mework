import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Checks.Work
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Schedule.PreRead

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Source.Program

noncomputable section

def trialBeforeRead (before : Raw) (nature : RequestAt) : PhysicalState :=
  (beforeReadInputs nature).foldl (fun state raw => (Physical.Public.compile input state raw).next)
    ⟨before,.seeking,[]⟩

def discoverySignal (version : Nat) : Fin rule.code.signals :=
  if version = 0 then ⟨0, by change 0 < 3; omega⟩ else ⟨1, by change 1 < 3; omega⟩

local instance (before : Raw) (version : Nat) :
    Decidable ((Physical.Public.interpreter input).Valid (trialBeforeRead before (Control.Scenario.discovery version)).raw rule.request ∧
      rule.code.readLocal rule.site (rule.code.snapshot rule.site (trialBeforeRead before (Control.Scenario.discovery version)).raw) =
        discoverySignal version) := by infer_instance

set_option maxHeartbeats 1200000 in
theorem each_original_trial_branch_pays_its_own_read_and_acquires_the_real_signal :
    firstRawVariants.all (fun before => ([0,1,2] : List Nat).all (fun version => decide
      ((Physical.Public.interpreter input).Valid (trialBeforeRead before (Control.Scenario.discovery version)).raw rule.request ∧
        rule.code.readLocal rule.site (rule.code.snapshot rule.site
          (trialBeforeRead before (Control.Scenario.discovery version)).raw) = discoverySignal version))) = true := by
  decide +kernel

theorem the_original_pre_read_requests_have_no_automatic_advance (nature : RequestAt) :
    ∀ raw ∈ beforeReadInputs nature, raw ≠ .advance := by
  intro raw present
  exact the_actual_trial_read_inputs_have_no_automatic_advance nature raw (List.mem_append_left _ present)

theorem the_explicit_paid_read_is_accepted (before : PhysicalState)
    (paid : (Physical.Public.interpreter input).Valid before.raw rule.request) :
    (Physical.Public.compile input before (.primitive rule.request)).isAccepted = true := by
  unfold Physical.Public.compile
  dsimp only [Physical.Public.wordAt]
  have checked : ∀ item ∈ (Physical.Public.interpreter input).rawItems before.raw [rule.request.resign rule.request.signer],
      (Physical.Public.interpreter input).Valid item.before item.request := by
    intro item member
    have single : item = ⟨0,before.raw,rule.request⟩ := by
      simpa only [rule.public_resigning_keeps_the_original_observation_request, RawLaw.rawItems,
        RawLaw.execute, List.mem_singleton] using member
    subst item
    exact paid
  cases actual : Material.inspectList (fun item : ExecutionItem Party Good Bool Nat Unit =>
      (Physical.Public.interpreter input).Valid item.before item.request)
      ((Physical.Public.interpreter input).rawItems before.raw [rule.request.resign rule.request.signer]) with
  | clear legal => rfl
  | failure item member failed => exact False.elim (failed (checked item member))

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation
