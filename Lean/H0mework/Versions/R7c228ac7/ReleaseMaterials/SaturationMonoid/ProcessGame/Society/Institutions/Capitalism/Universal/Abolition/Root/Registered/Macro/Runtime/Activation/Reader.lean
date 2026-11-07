import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Registry
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Frame.Conservation

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

def SourceReaderAt
    (current : ActivatedFrame (review := review) input depth (Ingress.cut input depth sourceStart)
      prefixLimit renewalLimit depth (Ingress.cut input depth sourceStart)) : Prop :=
  match current with
  | .original _ => True
  | .enacted _ admission frame => frame.reader = Abolition.Functions.Revision.InitialAdmission.reader admission

private theorem sourceReader_next
    (current : ActivatedFrame (review := review) input depth (Ingress.cut input depth sourceStart)
      prefixLimit renewalLimit depth (Ingress.cut input depth sourceStart))
    (sourced : SourceReaderAt input depth sourceStart prefixLimit renewalLimit review current) :
    SourceReaderAt input depth sourceStart prefixLimit renewalLimit review current.next := by
  cases current with
  | enacted origin admission frame => exact frame.next_keeps_the_same_source_reader.trans sourced
  | original frame =>
      dsimp only [ActivatedFrame.next]
      cases selected : frame.query with
      | internal work => trivial
      | raw germ =>
          dsimp only
          cases chosen : Abolition.Functions.Revision.InitialAdmission.select (Frame.controlOrigin frame germ) with
          | admitted admission => rfl
          | obstructed failed => trivial

theorem every_actual_public_reader_is_source_owned (tick : Nat) :
    SourceReaderAt input depth sourceStart prefixLimit renewalLimit review
      (actualFrame (review := review) input depth sourceStart datum prefixLimit renewalLimit reader tick) := by
  induction tick with
  | zero => trivial
  | succ tick prior => exact sourceReader_next input depth sourceStart prefixLimit renewalLimit review _ prior

theorem the_actual_public_reader_is_the_installed_source
    (tick : Nat)
    (origin : Abolition.Functions.Revision.Context (input := input) (review := review)
      depth (Ingress.cut input depth sourceStart) prefixLimit renewalLimit depth (Ingress.cut input depth sourceStart))
    (admission : Abolition.Functions.Revision.InitialAdmissionAt origin)
    (frame : Public.Runtime.Frame origin admission)
    (selected : actualFrame (review := review) input depth sourceStart datum prefixLimit renewalLimit reader tick =
      .enacted origin admission frame) :
    frame.reader = Abolition.Functions.Revision.InitialAdmission.reader admission := by
  have actual := every_actual_public_reader_is_source_owned (review := review) input depth sourceStart datum prefixLimit renewalLimit reader tick
  rw [selected] at actual
  exact actual

#print axioms every_actual_public_reader_is_source_owned
#print axioms the_actual_public_reader_is_the_installed_source

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime
