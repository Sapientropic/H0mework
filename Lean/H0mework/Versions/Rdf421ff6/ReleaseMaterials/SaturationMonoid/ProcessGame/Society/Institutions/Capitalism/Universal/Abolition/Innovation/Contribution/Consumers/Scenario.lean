import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Offer
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Control.Scenario.Source

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Consumers

open Control.Scenario

abbrev model := skeleton false

def belief (_ : model.QuotedNature) : ℚ := 1 / 2
def successSignal (signal : Fin model.code.signals) : Bool := decide (signal.val = 1)

abbrev rows := forecastRows model belief successSignal .material
abbrev reward := quotedReward model belief successSignal .material 0 (1 / 2)
abbrev decision := makeOffer model belief successSignal .material 0 (1 / 2)
abbrev chosen := participationMechanism model belief successSignal .material 0 (1 / 2)

theorem the_original_trials_generate_the_risk_rows :
    rows = [⟨1 / 2, false, 2⟩, ⟨1 / 2, true, 0⟩] := by decide +kernel

theorem the_compensation_is_the_source_derived_finite_reward :
    reward = riskReward ∧ reward = 3 := by decide +kernel

theorem the_funder_selects_participation_before_any_actual_event :
    prefersParticipation rows 0 (1 / 2) = true ∧ expectedChange rows reward = 1 / 2 := by
  decide +kernel

def isOffered : OfferResult model belief successSignal .material 0 (1 / 2) → Bool
  | .offered _ => true
  | .declined _ => false

theorem the_source_really_generates_the_funding_offer : isOffered decision = true := by
  decide +kernel

theorem the_offer_selects_the_original_signed_funding :
    chosen.funding = [issue, payout] ∧ chosen.funded = true := by
  have offered := the_source_really_generates_the_funding_offer
  cases outcome : decision with
  | offered offer =>
      unfold chosen participationMechanism
      change makeOffer model belief successSignal .material 0 (1 / 2) = _ at outcome
      rw [outcome]
      exact ⟨rfl, show model.funded = true from by decide +kernel⟩
  | declined rejection => rw [outcome] at offered; cases offered

abbrev expensiveModel : Trials.Mechanism Party Good Bool Nat Unit :=
  { model with code := { model.code with sendCost := fun _ _ =>
      [request 0 (.use 0 [(.message, 1000)] .contribution)] } }

def quotedDiscovery : expensiveModel.QuotedNature :=
  ⟨discovery 1, List.mem_cons_of_mem _ List.mem_cons_self⟩

theorem the_priced_success_cannot_be_supplied_by_an_unpaid_signal :
    witnessedSuccess expensiveModel successSignal quotedDiscovery = false := by
  decide +kernel

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Consumers
