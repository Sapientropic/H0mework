import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.PolicyCode

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program

universe u
variable (Party Good Port Technology Instrument : Type u)

/-- Each interpretation clause is a local source rule.  The programme
contains neither dependence labels nor target stocks nor future histories.
Claim repayment terms determine a real material leg before a claim can be
extinguished. -/
structure RawLaw where
  technique : Technology → Party → Technique Good Port
  controller : Technology → Port → Party
  allowed : Technology → Port → Party → Bool
  stockPort : Technology → Party → Good → Port
  revisionPort : Technology → Port
  revisionCost : Technology → Technology → Bundle Good
  settlementUnit : Instrument → Good
  settlementRate : Instrument → ℚ
  issuerPort : Instrument → Port
  necessities : RawCurrent Party Good Technology Instrument → Party → Bundle Good
  mandatoryMaintenance : RawCurrent Party Good Technology Instrument → Party → Bundle Good
  policy : RawPolicy Party Good Port Technology Instrument := .unrestricted
  duration : RawCurrent Party Good Technology Instrument → ℚ

def RawLaw.operationAllowed {Party Good Port Technology Instrument : Type u} [DecidableEq Party]
    (law : RawLaw Party Good Port Technology Instrument)
    (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) : Bool :=
  law.policy.eval current request

abbrev RawEvent := List (Request Party Good Port Technology Instrument)

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program
