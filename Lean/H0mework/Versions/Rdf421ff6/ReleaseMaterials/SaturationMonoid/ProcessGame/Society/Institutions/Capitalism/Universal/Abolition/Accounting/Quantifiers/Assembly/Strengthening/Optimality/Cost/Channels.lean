import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Programme.Material
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Costs.Vector

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Cost
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Abolition.Root Abolition.Root.Registered
noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

inductive Channel
  | productionInput | productionMaintenance | revision | use (purpose : Use)
  deriving DecidableEq

def channels : List Channel := [.productionInput,.productionMaintenance,.revision,
  .use .necessity,.use .maintenance,.use .investment,.use .contribution,.use .external]

/-- Debits that consume or maintain real resources. Transfer and repayment
legs are retained separately; they are not called destroyed social resources. -/
def part (law : RawLaw Party Good Port Technology Instrument)
    (before : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) (channel : Channel) : Flow Party Good :=
  match request.operation with
  | .produce operator =>
      if channel = .productionInput then locate operator (law.technique before.technology operator).inputs
      else if channel = .productionMaintenance then locate operator (law.technique before.technology operator).maintenance else []
  | .revise _ _ => if channel = .revision then law.debit before request else []
  | .use _ _ purpose => if channel = .use purpose then law.debit before request else []
  | _ => []

def actualPart (law : RawLaw Party Good Port Technology Instrument)
    (before : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) (channel : Channel) : Flow Party Good :=
  if law.Valid before request then part law before request channel else []

attribute [local simp] part actualPart

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Cost
