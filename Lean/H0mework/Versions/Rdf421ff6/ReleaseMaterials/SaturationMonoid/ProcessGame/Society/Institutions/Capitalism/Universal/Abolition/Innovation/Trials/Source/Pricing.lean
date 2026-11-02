import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials.Source.Decision

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials

open Source.Program

deriving instance DecidableEq for Operation
deriving instance DecidableEq for Request

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  [DecidableEq Port] [DecidableEq Technology]

namespace Mechanism

variable (mechanism : Mechanism Party Good Port Technology Instrument) (nature : mechanism.Nature)

inductive PricingStatus where
  | priced (original : nature ∈ mechanism.natureRequests)
  | unpriced (outside : nature ∉ mechanism.natureRequests)

/-- The finite quotation domain has no veto over actual physical events. -/
def pricingStatus : PricingStatus mechanism nature :=
  if original : nature ∈ mechanism.natureRequests then .priced original else .unpriced original

/-- The same open execution result is returned. Pricing adds no event,
payment, second run, physical refusal or authority. -/
def openGenerate := (mechanism.generate nature, mechanism.pricingStatus nature)

theorem quotation_keeps_the_exact_open_source_result :
    (mechanism.openGenerate nature).1 = mechanism.generate nature := rfl

theorem an_unlisted_event_receives_an_unpriced_responsibility
    (outside : nature ∉ mechanism.natureRequests) :
    mechanism.pricingStatus nature = .unpriced outside := by
  simp only [pricingStatus, dif_neg outside]

end Mechanism
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials
