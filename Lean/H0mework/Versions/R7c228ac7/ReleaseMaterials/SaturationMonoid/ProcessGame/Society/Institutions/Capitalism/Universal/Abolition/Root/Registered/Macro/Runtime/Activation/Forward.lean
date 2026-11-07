import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Activation.Rank
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Activation.Sequence
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Activation.Raw

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

private theorem shifted_before (base : Nat) {first second : Nat × (Nat × Nat)}
    (progress : Before first second) : Before (base + first.1, first.2) (base + second.1, second.2) := by
  unfold Before Financial.Installation.Runtime.Before at *
  dsimp only at *
  omega

private theorem legacy_progress
    (current : Frame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount)
    (query : current.presentation.Query) (selected : current.query = query) :
    Before current.rank (current.nextAt query).rank := by
  simpa only [Frame.next, selected] using current.next_progress

namespace ActivatedFrame

variable (frame : ActivatedFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount)

theorem next_progress : Before frame.rank frame.next.rank := by
  cases frame with
  | enacted origin admission current => exact shifted_before origin.germ.snapshot.past.length current.next_progress
  | original current =>
    cases selected : current.query with
    | internal work =>
      dsimp only [next]
      rw [selected]
      exact legacy_progress current (.internal work) selected
    | raw germ =>
      dsimp only [next]
      rw [selected]
      dsimp only
      cases chosen : Abolition.Functions.Revision.InitialAdmission.select (Frame.controlOrigin current germ) with
      | admitted admission =>
        simp only [rank]
        left
        have same := (Raw.input_uses_the_literal_current_account current.package.source current.package.sourceData
          current.package.reader germ).2.1
        change germ.snapshot = current.snapshot at same
        cases admission <;>
          change current.snapshot.past.length < germ.snapshot.past.length + 1 <;>
          rw [same] <;> exact Nat.lt_succ_self _
      | obstructed failed => simpa only [rank, Frame.controlOrigin, chosen] using legacy_progress current (.raw germ) selected

end ActivatedFrame

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime
