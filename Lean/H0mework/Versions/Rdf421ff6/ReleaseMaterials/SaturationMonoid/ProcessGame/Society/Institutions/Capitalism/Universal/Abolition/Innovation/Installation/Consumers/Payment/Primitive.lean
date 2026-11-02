import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Consumers.Finished.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Source.Program

noncomputable section

theorem the_actual_primitive_acceptance_uses_only_its_original_raw
    (first second : PhysicalState) (same : first.raw = second.raw) (request : RequestAt) :
    (Physical.Public.compile input first (.primitive request)).isAccepted =
      (Physical.Public.compile input second (.primitive request)).isAccepted := by
  rcases first with ⟨before,phase,remaining⟩
  rcases second with ⟨after,otherPhase,otherRemaining⟩
  dsimp only at same
  cases same
  unfold Physical.Public.compile
  dsimp only [Physical.Public.wordAt]
  cases Material.inspectList (fun item : ExecutionItem Party Good Bool Nat Unit =>
    (Physical.Public.interpreter input).Valid item.before item.request)
    ((Physical.Public.interpreter input).rawItems before [request.resign request.signer]) <;> rfl

theorem the_original_public_prefix_and_primitive_own_the_same_result
    (oldPast past : List InputAt) (request : RequestAt) :
    (Physical.Public.resultAt input 0 count 0 0 oldPast
      (Physical.receive (Physical.Prefix.cursor past) (.primitive request))).isAccepted =
        (Physical.Public.compile input (Physical.Public.stateAt input 0 count 0 0 oldPast past)
          (.primitive request)).isAccepted := by
  dsimp only [Physical.Public.resultAt,Physical.receive]
  rw [Physical.Prefix.past_readback]

theorem the_original_performance_prefix_has_its_actual_raw
    (oldPast : List InputAt) (version : Nat) (tail : List InputAt)
    (explicit : ∀ raw ∈ tail, raw ≠ .advance) :
    (Physical.Public.stateAt input 0 count 0 0 oldPast
      ((submittedInputs oldPast (Control.Scenario.discovery version) ++ [.primitive (riskLiability version)]) ++ tail)).raw =
    (tail.foldl (fun state raw => (Physical.Public.compile input state raw).next)
      (⟨trialRawAfterRiskLiability (Physical.stateAt input 0 count 0 0 oldPast).raw
        (Control.Scenario.discovery version) (riskLiability version),.seeking,[]⟩ : PhysicalState)).raw := by
  unfold Physical.Public.stateAt
  rw [List.foldl_append]
  exact an_explicit_prefix_reads_only_its_original_raw
    (Physical.Public.stateAt input 0 count 0 0 oldPast
      (submittedInputs oldPast (Control.Scenario.discovery version) ++ [.primitive (riskLiability version)]))
    ⟨trialRawAfterRiskLiability (Physical.stateAt input 0 count 0 0 oldPast).raw
      (Control.Scenario.discovery version) (riskLiability version),.seeking,[]⟩
    (the_submitted_code_and_actual_risk_issue_have_the_original_checked_raw oldPast _ _) tail explicit

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation
