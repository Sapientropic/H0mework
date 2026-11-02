import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Forecast

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution

open Source.Program
open SaturationMonoid.ProcessGame.Society.PublicFunction

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (mechanism : Trials.Mechanism Party Good Port Technology Instrument)
  (belief : mechanism.QuotedNature → ℚ)
  (successSignal : Fin mechanism.code.signals → Bool) (good : Good) (outside loading : ℚ)

structure ProspectiveOffer where
  private mk ::
  normalized : AdmissibleBelief mechanism belief
  supported : 0 < successMass (forecastRows mechanism belief successSignal good)
  nonnegativeLoading : 0 ≤ loading
  nonnegativeReward : 0 ≤ quotedReward mechanism belief successSignal good outside loading

inductive OfferIssue where
  | negativeWeight (nature : mechanism.QuotedNature)
      (original : nature ∈ natureDomain mechanism) (negative : ¬ 0 ≤ belief nature)
  | wrongTotalWeight (unequal : ((natureDomain mechanism).map belief).sum ≠ 1)
  | noPricedSuccess (unsupported : ¬ 0 < successMass (forecastRows mechanism belief successSignal good))
  | negativeLoading (negative : ¬ 0 ≤ loading)
  | negativeReward (negative : ¬ 0 ≤ quotedReward mechanism belief successSignal good outside loading)

inductive OfferResult where
  | offered (offer : ProspectiveOffer mechanism belief successSignal good outside loading)
  | declined (issue : OfferIssue mechanism belief successSignal good outside loading)

/-- The generator receives no actual nature event. Costs and observed
branches are evaluated from the original finite forecasting grammar. -/
def makeOffer : OfferResult mechanism belief successSignal good outside loading :=
  match Material.inspectList (fun nature : mechanism.QuotedNature => 0 ≤ belief nature) (natureDomain mechanism) with
  | .failure nature original negative => .declined (.negativeWeight nature original negative)
  | .clear nonnegative =>
      if normalized : ((natureDomain mechanism).map belief).sum = 1 then
        if supported : 0 < successMass (forecastRows mechanism belief successSignal good) then
          if paidLoading : 0 ≤ loading then
            if nonnegativeReward : 0 ≤ quotedReward mechanism belief successSignal good outside loading then
              .offered ⟨⟨nonnegative, normalized⟩, supported, paidLoading, nonnegativeReward⟩
            else .declined (.negativeReward nonnegativeReward)
          else .declined (.negativeLoading paidLoading)
        else .declined (.noPricedSuccess supported)
      else .declined (.wrongTotalWeight normalized)

theorem every_offered_quote_generates_its_participation_choice
    (offer : ProspectiveOffer mechanism belief successSignal good outside loading) :
    prefersParticipation (forecastRows mechanism belief successSignal good) outside loading = true ∧
      expectedChange (forecastRows mechanism belief successSignal good)
        (quotedReward mechanism belief successSignal good outside loading) = outside + loading :=
  ⟨the_participation_rule_is_fixed_before_the_actual_nature_event mechanism belief successSignal good
      outside loading offer.supported offer.nonnegativeLoading,
    the_source_derived_quote_has_its_declared_participation_value mechanism belief successSignal good
      outside loading offer.supported⟩

theorem an_exact_quote_issue_excludes_an_admitted_offer
    (issue : OfferIssue mechanism belief successSignal good outside loading) :
    ¬ Nonempty (ProspectiveOffer mechanism belief successSignal good outside loading) := by
  rintro ⟨offer⟩
  cases issue with
  | negativeWeight nature original negative => exact negative (offer.normalized.1 nature original)
  | wrongTotalWeight unequal => exact unequal offer.normalized.2
  | noPricedSuccess unsupported => exact unsupported offer.supported
  | negativeLoading negative => exact negative offer.nonnegativeLoading
  | negativeReward negative => exact negative offer.nonnegativeReward

/-- This choice controls the original signed funding prefix. It is made
once, before the open source receives any actual nature event. -/
def participationMechanism : Trials.Mechanism Party Good Port Technology Instrument :=
  match makeOffer mechanism belief successSignal good outside loading with
  | .offered _ => mechanism
  | .declined _ => { mechanism with funding := [] }

theorem the_funding_submission_is_chosen_before_the_unknown_event :
    match makeOffer mechanism belief successSignal good outside loading with
    | .offered _ =>
        (participationMechanism mechanism belief successSignal good outside loading).funding = mechanism.funding
    | .declined _ =>
        (participationMechanism mechanism belief successSignal good outside loading).funding = [] := by
  unfold participationMechanism
  cases makeOffer mechanism belief successSignal good outside loading <;> rfl

theorem a_declined_offer_cannot_create_a_phantom_disbursement
    (issue : OfferIssue mechanism belief successSignal good outside loading)
    (declined : makeOffer mechanism belief successSignal good outside loading = .declined issue) :
    (participationMechanism mechanism belief successSignal good outside loading).fundingReceipt = none := by
  unfold participationMechanism
  rw [declined]
  simp [Trials.Mechanism.fundingReceipt, Financing.readDisbursement?, RawLaw.rawItems, RawLaw.execute]

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution
