import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Native.Handler

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Consumers.Issue
open Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root.Registered Abolition.Root.Registered.Macro
noncomputable section

def request : Request Bool Bool Bool Unit Unit := ⟨false,[],false,[],.issue () false true 1⟩

theorem valid_at_every_actual_raw
    (input : ProgrammeSource.Input Bool Bool Bool Unit Unit) (before : RawCurrent Bool Bool Unit Unit) :
    (Physical.Public.interpreter input).Valid before request := by
  simp [request,Physical.Public.interpreter,Society.PublicFunction.physicalLaw,
    RawLaw.Valid,RawLaw.SignerMatches,RawLaw.operationAllowed,RawLaw.requiredPorts,
    RawLaw.ClaimGuard,RawLaw.debit,RawLaw.credit,NonnegativeBundle,RawPolicy.eval]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Consumers.Issue
