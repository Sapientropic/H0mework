import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Frame.State

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Frame

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {review : Option (ReviewPhase.ContextAt input)}
  {origin : Abolition.Functions.Revision.Context (input := input) (review := review)
    depth count prefixLimit renewalLimit sourceDepth sourceCount}
  {admission : Abolition.Functions.Revision.InitialAdmissionAt origin}
  (frame : Frame origin admission)

def reenter (complete : ¬ frame.HasWork) : Frame origin admission where
  start := Continuation.Admitted.selectedStart frame.full frame.actualForFull frame.reader
  reader := frame.reader
  source := Continuation.Admitted.bareFrame origin admission frame.full frame.actualForFull frame.reader
  visit := (Continuation.Admitted.targetInitial origin admission frame.full (.finite frame.visit) frame.actualForFull frame.reader).next
    (Continuation.Admitted.firstSuccessor origin admission frame.full (.finite frame.visit) frame.actualForFull frame.reader).next_eq
  actual := ⟨Continuation.Admitted.bodyNext frame.full frame.actualForFull,
    congrArg some (Continuation.Admitted.first_target_is_the_actual_selected_body origin admission frame.full (.finite frame.visit) frame.actualForFull frame.reader)⟩
  authority := Continuation.Admitted.nextAuthorityForInstalledEntry origin admission frame.full (.finite frame.visit) frame.actualForFull frame.reader complete frame.authority
  paid := rfl

theorem raw_reentry_keeps_the_literal_complete_account (complete : ¬ frame.HasWork) :
    (frame.reenter complete).account = frame.account := rfl

#print axioms reenter
#print axioms raw_reentry_keeps_the_literal_complete_account

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Frame
