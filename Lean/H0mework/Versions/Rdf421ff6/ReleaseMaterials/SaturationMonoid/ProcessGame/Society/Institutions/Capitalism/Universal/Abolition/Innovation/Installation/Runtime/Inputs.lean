import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Schedule

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation

open Source.Program
open Abolition.Root Abolition.Root.Registered

noncomputable section

/-- Syntax positions emitted by the fixed source before its own paid read.
They contain the open nature request, not its successful physical result. -/
def beforeReadInputs (nature : RequestAt) : List InputAt :=
  [.execute Control.Scenario.commonWork] ++ preparation.map Compile.RawInput.primitive ++
    [.primitive nature,.primitive (Control.Scenario.production 0)]

def readInputs (nature : RequestAt) : List InputAt :=
  beforeReadInputs nature ++ [.primitive rule.request]

def observedSignal (oldPast : List InputAt) (nature : RequestAt) :=
  Observation.localSignal input 0 count 0 0 oldPast rule (beforeReadInputs nature)

def observedCode (oldPast : List InputAt) (nature : RequestAt) := programme (observedSignal oldPast nature)

def submittedInputs (oldPast : List InputAt) (nature : RequestAt) : List InputAt :=
  readInputs nature ++ [.code ⟨observedCode oldPast nature⟩]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation
