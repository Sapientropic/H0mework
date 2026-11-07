import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.ActualReady
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Contract

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.Actual

open Source.Program
noncomputable section

theorem the_original_capital_total_contract_actually_delivers_its_generated_nonzero_risk_payment :
    ∃ prepared : Root.Prepared source mechanism,
      Root.prepare source mechanism = .ready prepared ∧
      quoted prepared.schedule = some 4 ∧
      ∀ event : prepared.schedule.programme.QuotedNature,
      ∃ afterBody actualBody target actualPrice,
        Root.execute prepared event.val none =
          .delivered afterBody actualBody (.completed target actualPrice) ∧
        Root.attempt source mechanism event.val none = target ∧
        ∃ whole : Root.Runtime.Trace source
            (Root.Runtime.normalise (prepared.schedule.requests event.val mechanism.investmentPort)) target,
          target.raw = ((Root.sourceInput source).law.execute source.raw 0
            (prepared.schedule.requests event.val mechanism.investmentPort)).final ∧
          target.native.input = source.native.input ∧
          (type_of% whole.carries_every_original_row_and_claim_without_refilling) := by
  obtain ⟨prepared,generated⟩ := the_actual_source_preparation_is_ready
  have capital := Root.the_original_capital_root_closes_the_risk_compensation_amount_and_authority.{0,0,0,0}
    Original.seed Original.grossClaim
  have total := capital.everyActualRiskSource source mechanism
  refine ⟨prepared,generated,the_actual_original_root_generates_four_without_loading prepared.schedule,?_⟩
  intro event
  obtain ⟨afterBody,actualBody,target,actualPrice,delivered,whole,endpoint,input,ledger⟩ :=
    total.actualDelivery prepared event source_ready source_review
  refine ⟨afterBody,actualBody,target,actualPrice,delivered,?_,whole,endpoint,input,ledger⟩
  simp only [Root.attempt,generated,delivered,Root.Execution.current,Root.Runtime.Outcome.current]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.Actual

-- Suggestion indexing alone unfolds this concrete current too deeply.
run_cmd Lean.modifyEnv fun env =>
  let names := ["the_original_capital_total_contract_actually_delivers_its_generated_nonzero_risk_payment"]
  names.foldl (fun env name => Lean.LibrarySuggestions.nameDenyListExt.addEntry env name) env
