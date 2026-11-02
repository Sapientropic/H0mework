import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Activation.State

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat)
  (review : Option (ReviewPhase.ContextAt input))

variable {input depth count prefixLimit renewalLimit sourceDepth sourceCount review}

namespace ActivatedFrame

variable (frame : ActivatedFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount)

def next : ActivatedFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount := match frame with
  | .enacted origin admission current => .enacted origin admission current.next
  | .original current => match _selected : current.query with
      | .internal work => .original (current.nextAt (.internal work))
      | .raw germ =>
          let origin := Abolition.Functions.Revision.Enactment.Inquiry.contextAt
            current.package (.finite current.visit) current.authority germ
          match Abolition.Functions.Revision.InitialAdmission.select origin with
          | .admitted admission => .enacted origin admission
              (Public.Runtime.Frame.initial current.package (.finite current.visit) current.authority germ admission)
          | .obstructed _ => .original (current.nextAt (.raw germ))

end ActivatedFrame

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime
