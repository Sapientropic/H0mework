import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Frame.State
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Drain.Source

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

private theorem native_next_is_paid :
    (Accounting.nativeNext input depth count prefixLimit renewalLimit origin.germ.snapshot.past frame.start
      frame.actual.actual).bodyPaid = true := by
  rw [Accounting.nativeNext, dif_pos frame.paid]
  cases found : Accounting.item? input depth count prefixLimit renewalLimit origin.germ.snapshot.past frame.start frame.actual.actual with
  | none => exact frame.paid
  | some item => exact (Accounting.Current.after_item_reads_the_source_generated_native_account frame.actual.actual frame.paid item).2.2

def ordinary (_work : frame.HasWork)
    (_noIssue : Accounting.registration? input depth count prefixLimit renewalLimit origin.germ.snapshot.past frame.start frame.actual.actual = none) :
    Frame origin admission where
  start := frame.start
  reader := frame.reader
  source := frame.source
  visit := frame.visit.next (frame.full.successor frame.visit.current).next_eq
  actual := ⟨Accounting.nativeNext input depth count prefixLimit renewalLimit origin.germ.snapshot.past frame.start frame.actual.actual,
    frame.source.cursor_next frame.visit.current frame.actual.actual frame.actual.aligned⟩
  authority := Accounting.Born.Action.nextAuthorityForInstalledEntry frame.full (.finite frame.visit) frame.authority
  paid := native_next_is_paid frame

theorem ordinary_spends_one_source_position (work : frame.HasWork)
    (noIssue : Accounting.registration? input depth count prefixLimit renewalLimit origin.germ.snapshot.past frame.start frame.actual.actual = none) :
    (frame.ordinary work noIssue).sourceMass + 1 = frame.sourceMass :=
  Accounting.Drain.every_actual_internal_restriction_spends_one_position frame.source frame.actual.actual work

#print axioms ordinary
#print axioms ordinary_spends_one_source_position

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Frame
