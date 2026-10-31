import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Execution
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Financing
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Scan

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials

open Source.Program
open SaturationMonoid.ProcessGame.Society.PublicFunction

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

/-- Executable code is committed before the nature argument. These fields
contain no successful service, outcome history, endpoint or receipt. -/
structure Mechanism (Party Good Port Technology Instrument : Type)
    [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument] where
  code : Distributed.Code Party Good Port Technology Instrument
  policy : code.Policy
  terms : Financing.Terms Party Instrument
  funding : RawEvent Party Good Port Technology Instrument
  investment : Bundle Good
  investmentPort : Port
  investmentGates : List Port := []
  probe : RawEvent Party Good Port Technology Instrument
  observer : Fin code.sites
  closing : RawEvent Party Good Port Technology Instrument

namespace Mechanism

variable (mechanism : Mechanism Party Good Port Technology Instrument)

abbrev Nature (_source : Mechanism Party Good Port Technology Instrument) :=
  Request Party Good Port Technology Instrument

abbrev QuotedNature := {request : Request Party Good Port Technology Instrument //
  Distributed.Event.adversary request ∈ mechanism.code.eventAlphabet}

def natureRequests := mechanism.code.eventAlphabet.filterMap fun event =>
  match event with | .adversary request => some request | _ => none

def investmentRequest : Request Party Good Port Technology Instrument :=
  ⟨mechanism.terms.borrower, [], mechanism.investmentPort, mechanism.investmentGates,
    .use mechanism.terms.borrower mechanism.investment .investment⟩

def fundingReceipt := Financing.readDisbursement? mechanism.code.law mechanism.code.initial
  mechanism.funding mechanism.terms

def fundingAfter := (mechanism.code.law.execute mechanism.code.initial 0 mechanism.funding).final

def funded : Bool := mechanism.fundingReceipt.isSome

def invested : Bool := mechanism.funded && decide
  (mechanism.code.law.Valid mechanism.fundingAfter mechanism.investmentRequest ∧
    ∃ lot ∈ mechanism.investment, 0 < lot.2)

def investmentWord : RawEvent Party Good Port Technology Instrument :=
  if mechanism.funded then [mechanism.investmentRequest] else []

def beforeProbe (nature : mechanism.Nature) :=
  mechanism.funding ++ mechanism.investmentWord ++ [nature]

def trialPrefix (nature : mechanism.Nature) :=
  mechanism.beforeProbe nature ++ if mechanism.invested then mechanism.probe else []

def initialFrame (nature : mechanism.Nature) : mechanism.code.Frame :=
  { mechanism.code.start with word := mechanism.trialPrefix nature }

end Mechanism
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials
