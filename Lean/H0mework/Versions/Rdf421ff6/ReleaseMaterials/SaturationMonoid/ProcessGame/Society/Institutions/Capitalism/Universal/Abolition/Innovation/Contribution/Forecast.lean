import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials.Source.Decision
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.RiskMath
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Control.Physical

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution

open Source.Program
open SaturationMonoid.ProcessGame.Society.PublicFunction

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (mechanism : Trials.Mechanism Party Good Port Technology Instrument)

/-- The uncertainty domain is generated from the original event grammar,
not supplied as a collection of successful histories. -/
def natureDomain : List mechanism.QuotedNature := mechanism.code.eventAlphabet.attach.filterMap fun event =>
  match event with
  | ⟨.adversary request, original⟩ => some ⟨request, original⟩
  | _ => none

theorem every_declared_nature_is_in_the_forecast_domain (nature : mechanism.QuotedNature) :
    nature ∈ natureDomain mechanism := by
  apply List.mem_filterMap.mpr
  refine ⟨⟨Distributed.Event.adversary nature.val, nature.property⟩, List.mem_attach _ _, ?_⟩
  cases nature
  rfl

/-- This is the incurred source prefix before the participant's contingent
reward. Computing the quote therefore cannot presuppose its own payment. -/
def preRewardItems (nature : mechanism.QuotedNature) :=
  mechanism.code.law.rawItems mechanism.code.initial (mechanism.deliveredFrame nature.val).word

def uncoveredPhysicalLoss (nature : mechanism.QuotedNature) (good : Good) : ℚ :=
  max 0 (-Control.net mechanism.code.law (preRewardItems mechanism nature) good)

def witnessedSuccess (successSignal : Fin mechanism.code.signals → Bool)
    (nature : mechanism.QuotedNature) : Bool := match mechanism.paidSignal nature.val with
  | none => false
  | some signal => successSignal signal

/-- Beliefs describe the participant's declared pre-event forecast. Neither
their truth nor a particular future outcome is asserted by this readout. -/
def forecastRows (belief : mechanism.QuotedNature → ℚ)
    (successSignal : Fin mechanism.code.signals → Bool) (good : Good) : List RiskRow :=
  (natureDomain mechanism).map fun nature =>
    ⟨belief nature, witnessedSuccess mechanism successSignal nature,
      uncoveredPhysicalLoss mechanism nature good⟩

theorem the_priced_prefix_does_not_contain_its_own_later_reward
    (policy : mechanism.code.Policy) (closing : RawEvent Party Good Port Technology Instrument)
    (nature : mechanism.QuotedNature) :
    preRewardItems { mechanism with policy := policy, closing := closing } nature =
      preRewardItems mechanism nature := rfl

theorem changing_the_later_work_cannot_change_the_prior_cost_quote
    (belief : mechanism.QuotedNature → ℚ)
    (successSignal : Fin mechanism.code.signals → Bool) (good : Good)
    (policy : mechanism.code.Policy) (closing : RawEvent Party Good Port Technology Instrument) :
    forecastRows { mechanism with policy := policy, closing := closing } belief successSignal good =
      forecastRows mechanism belief successSignal good := by
  let changed := { mechanism with policy := policy, closing := closing }
  have invested : changed.invested = mechanism.invested := rfl
  have sent (nature : mechanism.QuotedNature) :
      changed.sentFrame nature.val = mechanism.sentFrame nature.val := by
    unfold Trials.Mechanism.sentFrame
    rw [invested]
    split <;> rfl
  have delivered (nature : mechanism.QuotedNature) :
      changed.deliveredFrame nature.val = mechanism.deliveredFrame nature.val := by
    unfold Trials.Mechanism.deliveredFrame
    rw [invested, sent]
    split <;> rfl
  have observed (nature : mechanism.QuotedNature) :
      changed.observed nature.val = mechanism.observed nature.val := by
    unfold Trials.Mechanism.observed
    rw [invested, sent]
    rfl
  have signal (nature : mechanism.QuotedNature) :
      changed.paidSignal nature.val = mechanism.paidSignal nature.val := by
    unfold Trials.Mechanism.paidSignal
    rw [observed, delivered]
  change forecastRows changed belief successSignal good = _
  unfold forecastRows
  have domain : natureDomain changed = natureDomain mechanism := by
    unfold natureDomain
    congr 1
    funext event
    rcases event with ⟨event, original⟩
    cases event <;> rfl
  rw [domain]
  apply List.map_congr_left
  intro nature _
  unfold witnessedSuccess uncoveredPhysicalLoss
  rw [signal]
  cases mechanism.paidSignal nature.val <;> rfl

def AdmissibleBelief (belief : mechanism.QuotedNature → ℚ) : Prop :=
  (∀ nature ∈ natureDomain mechanism, 0 ≤ belief nature) ∧
    ((natureDomain mechanism).map belief).sum = 1

def quotedReward (belief : mechanism.QuotedNature → ℚ)
    (successSignal : Fin mechanism.code.signals → Bool) (good : Good) (outside loading : ℚ) : ℚ :=
  contingentReward (forecastRows mechanism belief successSignal good) outside loading

theorem a_forecast_row_uses_the_original_paid_record_and_real_prefix
    (belief : mechanism.QuotedNature → ℚ) (successSignal : Fin mechanism.code.signals → Bool)
    (good : Good) (nature : mechanism.QuotedNature) :
    (⟨belief nature, witnessedSuccess mechanism successSignal nature,
      uncoveredPhysicalLoss mechanism nature good⟩ : RiskRow) ∈
      forecastRows mechanism belief successSignal good := by
  exact List.mem_map.mpr ⟨nature, every_declared_nature_is_in_the_forecast_domain mechanism nature, rfl⟩

theorem an_unpaid_signal_cannot_be_priced_as_a_witnessed_success
    (successSignal : Fin mechanism.code.signals → Bool) (nature : mechanism.QuotedNature)
    (unpaid : mechanism.paidSignal nature.val = none) :
    witnessedSuccess mechanism successSignal nature = false := by
  simp only [witnessedSuccess, unpaid]

theorem the_loss_readout_keeps_every_real_cost_and_excludes_internal_rent
    (nature : mechanism.QuotedNature) (good : Good) :
    uncoveredPhysicalLoss mechanism nature good =
      max 0 (Control.cost mechanism.code.law (preRewardItems mechanism nature) good -
        Control.output mechanism.code.law (preRewardItems mechanism nature) good) := by
  unfold uncoveredPhysicalLoss
  rw [Control.the_complete_original_inventory_counts_every_real_cost]
  congr 1
  ring

theorem the_source_derived_quote_has_its_declared_participation_value
    (belief : mechanism.QuotedNature → ℚ) (successSignal : Fin mechanism.code.signals → Bool)
    (good : Good) (outside loading : ℚ)
    (possible : 0 < successMass (forecastRows mechanism belief successSignal good)) :
    expectedChange (forecastRows mechanism belief successSignal good)
        (quotedReward mechanism belief successSignal good outside loading) = outside + loading :=
  the_source_quote_pays_the_declared_ex_ante_return _ _ _ possible

theorem the_participation_rule_is_fixed_before_the_actual_nature_event
    (belief : mechanism.QuotedNature → ℚ) (successSignal : Fin mechanism.code.signals → Bool)
    (good : Good) (outside loading : ℚ)
    (possible : 0 < successMass (forecastRows mechanism belief successSignal good))
    (nonnegative : 0 ≤ loading) :
    prefersParticipation (forecastRows mechanism belief successSignal good) outside loading = true :=
  the_quoted_participation_choice_precedes_the_actual_outcome _ _ _ possible nonnegative

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution
