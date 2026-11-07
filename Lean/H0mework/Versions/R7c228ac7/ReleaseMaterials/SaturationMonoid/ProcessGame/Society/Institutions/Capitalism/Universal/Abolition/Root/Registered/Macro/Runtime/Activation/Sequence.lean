import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Activation.Next
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress.Continuation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth sourceStart : Nat)
  (datum : Ingress.Datum input depth sourceStart) (prefixLimit renewalLimit : Nat)
  (reader : Raw.Reader input depth (Ingress.cut input depth sourceStart))
  (review : Option (ReviewPhase.ContextAt input) := none)

def activatedFrames : Nat → ActivatedFrame (review := review) input depth (Ingress.cut input depth sourceStart)
    prefixLimit renewalLimit depth (Ingress.cut input depth sourceStart)
  | 0 => .original (frames (nativeOrigin := datum.nativeOrigin) (review := review) input depth
      (Ingress.cut input depth sourceStart) prefixLimit renewalLimit depth (Ingress.cut input depth sourceStart)
      Physical.initial (Ingress.proposal (review := review) input depth sourceStart datum prefixLimit renewalLimit) 0 reader 0)
  | tick + 1 => (activatedFrames tick).next

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime
