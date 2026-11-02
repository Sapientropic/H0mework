import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Control.Scenario.Capital
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Offer
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials.Source.Pricing
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.ProgrammeHistory

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation

open Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

abbrev Party := Control.Scenario.Party
abbrev Good := Control.Scenario.Good
abbrev RequestAt := Control.Scenario.RequestAt
abbrev Raw := RawCurrent Party Good Nat Unit

def baseline (current : Raw) : RawEvent Party Good Bool Nat Unit :=
  if current.round = 1 then Control.Scenario.capitalWord else Control.Scenario.commonWork

/-- Only the original capital occurrence and the common maintenance programme
belong to the genesis emitter. The later experiment is not a stored future. -/
def input : ProgrammeSource.Input Party Good Bool Nat Unit where
  law := Control.Scenario.law
  initial := Control.Scenario.genesis
  instructions := Control.Scenario.commonWork
  emission? := some baseline
  localAttempts := fun _ => Control.Scenario.commonWork
  observedEmission? := some {
    generate := fun current => .original current (baseline current)
    word := ProgrammeSource.ProgrammeReport.word }

abbrev quotedMechanism := Control.Scenario.skeleton false
def belief (_nature : quotedMechanism.QuotedNature) : ℚ := 1 / 2
def successSignal (signal : Fin quotedMechanism.code.signals) : Bool := decide (signal.val = 1)
def offered := Contribution.makeOffer quotedMechanism belief successSignal .material 0 (1 / 2)
def offerAccepted : Bool := match offered with | .offered _ => true | .declined _ => false
def reward : ℚ := Contribution.quotedReward quotedMechanism belief successSignal .material 0 (1 / 2)

def preparation : RawEvent Party Good Bool Nat Unit :=
  match offered with
  | .offered _ => quotedMechanism.funding ++ [quotedMechanism.investmentRequest]
  | .declined _ => []

def programme (signal : Fin quotedMechanism.code.signals) : RawEvent Party Good Bool Nat Unit :=
  Control.Scenario.policyAction signal.val

theorem the_original_input_has_zero_genesis_claims_and_no_trial_future :
    input.initial.claims = (fun _ _ _ => 0) ∧
      ProgrammeSource.wordAt input Control.Scenario.start = Control.Scenario.capitalWord ∧
      ProgrammeSource.wordAt input Control.Scenario.seed = Control.Scenario.commonWork := ⟨rfl, rfl, rfl⟩

theorem the_quote_and_signed_funding_are_fixed_before_any_actual_nature :
    offerAccepted = true ∧ reward = 3 ∧
      preparation = [Control.Scenario.issue,Control.Scenario.payout,quotedMechanism.investmentRequest] := by
  decide +kernel

theorem the_native_risk_premium_is_the_original_prospective_quote :
    reward = Control.Scenario.riskReward ∧
      Control.Scenario.premiumUnits * input.law.settlementRate () = reward ∧
      Control.Scenario.coverageUnits * input.law.settlementRate () = Control.Scenario.exposure := by
  decide +kernel

theorem the_original_capital_occurrence_precedes_every_trial :
    Nonempty (Source.ProgrammeControl.Kernel.CapitalRelationKernel input.law
      (ProgrammeSource.rawCurrent input (ProgrammeHistory.visitAt input 1).current)
      (ProgrammeSource.rawEvent input (ProgrammeHistory.visitAt input 1).current)) :=
  ⟨Control.Scenario.originalCapital⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation
