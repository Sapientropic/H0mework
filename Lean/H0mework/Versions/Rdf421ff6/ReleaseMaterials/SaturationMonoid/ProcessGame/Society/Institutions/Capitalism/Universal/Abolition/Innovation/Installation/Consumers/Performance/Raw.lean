import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Consumers.Performance.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered

noncomputable section

theorem the_submitted_code_and_actual_risk_issue_have_the_original_checked_raw
    (oldPast : List InputAt) (nature liability : RequestAt) :
    (Physical.Public.stateAt input 0 count 0 0 oldPast
      (submittedInputs oldPast nature ++ [.primitive liability])).raw =
        trialRawAfterRiskLiability (Physical.stateAt input 0 count 0 0 oldPast).raw nature liability := by
  let before := Physical.stateAt input 0 count 0 0 oldPast
  let afterRead := (readInputs nature).foldl (fun state raw => (Physical.Public.compile input state raw).next) before
  unfold submittedInputs Physical.Public.stateAt
  rw [List.foldl_append, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  change ((Physical.Public.compile input
    ((Physical.Public.compile input afterRead (.code ⟨observedCode oldPast nature⟩)).next)
    (.primitive liability)).next).raw = _
  exact an_explicit_physical_step_reads_its_original_raw afterRead
    ⟨trialRawAfterRead before.raw nature,.seeking,[]⟩
    (the_original_public_prefix_has_the_checked_real_raw before nature) (.primitive liability)
    (by intro impossible; cases impossible)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation
