import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Consumers.Performance.Risk

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered

noncomputable section

private theorem the_original_unspent_attempt_uses_the_literal_source_association
    (oldPast : List InputAt) (nature : RequestAt) (attempts : List InputAt)
    (noExecute : ∀ raw ∈ oldPast, beforePublic raw = true)
    (original : ∀ raw ∈ attempts, NonCode raw) :
    selected nature (oldPast ++ (submittedInputs oldPast nature ++ attempts)) =
      ((executionInputs (observedCode oldPast nature))[attempts.length]?).getD (.execute Control.Scenario.commonWork) :=
  (congrArg (selected nature) (List.append_assoc oldPast (submittedInputs oldPast nature) attempts)).symm.trans
    (the_submitted_programme_selects_its_original_unspent_attempt oldPast nature attempts noExecute original)

theorem the_actual_performance_cut_selects_only_its_original_unspent_attempt
    (version : Nat) (tested : version ∈ ([0,1,2] : List Nat)) (index : Nat) (attempts : List InputAt)
    (original : ∀ raw ∈ attempts, NonCode raw)
    (snapshot : (actualPublicVisit (Control.Scenario.discovery version) index).snapshot = Physical.Prefix.cursor
      (submittedInputs (firstRaw (Control.Scenario.discovery version)).germ.snapshot.past
        (Control.Scenario.discovery version) ++ attempts)) :
    selected (Control.Scenario.discovery version)
      ((firstOrigin (Control.Scenario.discovery version)).germ.snapshot.past ++
        (actualPublicVisit (Control.Scenario.discovery version) index).snapshot.past) =
      ((performanceInputs version)[attempts.length]?).getD (.execute Control.Scenario.commonWork) := by
  let nature := Control.Scenario.discovery version
  let oldPast := (firstRaw nature).germ.snapshot.past
  have projected := congrArg (fun current : CursorAt => selected nature
    ((firstOrigin nature).germ.snapshot.past ++ current.past)) snapshot
  have sourcePast := congrArg (fun past : List InputAt => selected nature
    ((firstOrigin nature).germ.snapshot.past ++ past))
      (Physical.Prefix.past_readback (submittedInputs oldPast nature ++ attempts))
  have grammar := congrArg (fun inputs : List InputAt => inputs[attempts.length]?.getD (.execute Control.Scenario.commonWork))
    (the_actual_code_carries_its_own_source_generated_risk_liability version tested)
  exact projected.trans (sourcePast.trans ((the_original_unspent_attempt_uses_the_literal_source_association oldPast nature attempts
    (the_original_first_prefix_has_no_unperformed_public_execution nature) original).trans grammar))

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation
