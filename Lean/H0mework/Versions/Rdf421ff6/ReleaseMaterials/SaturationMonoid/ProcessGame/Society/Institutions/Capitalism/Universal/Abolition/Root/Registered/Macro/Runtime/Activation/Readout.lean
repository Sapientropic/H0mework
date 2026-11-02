import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Activation.State

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {review : Option (ReviewPhase.ContextAt input)}

namespace ActivatedFrame
variable (frame : ActivatedFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount)

def nativeAccount : (Epoch.Finance.process input depth count).GeneratedState := match frame with
  | .original current => current.account
  | .enacted _ _ current => current.account

def actualState : Abolition.Root.Actual.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) := match frame with
  | .original current => Physical.stateAt input depth count prefixLimit renewalLimit current.snapshot.past
  | .enacted origin _ current => Physical.Public.stateAt input depth count prefixLimit renewalLimit
      origin.germ.snapshot.past current.snapshot.past

def interpreter : Source.Program.RawLaw Party Good Port Technology Instrument := match frame with
  | .original _ => input.law
  | .enacted _ _ _ => Physical.Public.interpreter input

def isPublic : Bool := match frame with
  | .original _ => false
  | .enacted _ _ _ => true

end ActivatedFrame
end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime
