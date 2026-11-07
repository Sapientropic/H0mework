import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Activation.Forward
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

private def layoutNext
    (current : ActivatedFrame (review := review) input depth (Ingress.cut input depth sourceStart)
      prefixLimit renewalLimit depth (Ingress.cut input depth sourceStart))
    (layout : current.Layout) : current.next.Layout := by
  cases current with
  | enacted origin admission frame => exact frame.layoutNext layout
  | original frame =>
      cases selected : frame.query with
      | internal work =>
          dsimp only [ActivatedFrame.next]
          rw [selected]
          change (frame.nextAt (.internal work)).Layout
          simpa only [Frame.next, selected] using frame.layoutNext layout
      | raw germ =>
          dsimp only [ActivatedFrame.next]
          rw [selected]
          dsimp only
          cases chosen : Abolition.Functions.Revision.InitialAdmission.select (Frame.controlOrigin frame germ) with
          | admitted admission => cases admission <;> exact ⟨0, rfl⟩
          | obstructed failed => simpa only [ActivatedFrame.Layout, Frame.next, Frame.nextAt, selected] using frame.layoutNext layout

def activatedLayouts : (tick : Nat) →
    (activatedFrames (review := review) input depth sourceStart datum prefixLimit renewalLimit reader tick).Layout
  | 0 => ⟨true, 0, rfl⟩
  | tick + 1 => layoutNext (input := input) (depth := depth) (sourceStart := sourceStart)
      (prefixLimit := prefixLimit) (renewalLimit := renewalLimit) (review := review)
      (activatedFrames (review := review) input depth sourceStart datum prefixLimit renewalLimit reader tick)
      (activatedLayouts tick)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime
