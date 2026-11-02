import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Continuation.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Continuation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Financial.Installation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

def OriginalOccurrenceUnique (frame : Runtime.Frame input) : Prop :=
  ∀ current (occurrence : frame.native.root.toAuthoritativeRoot.toRoot.actual.OccurrenceAt current),
    occurrence = frame.native.root.emitted current

theorem actual_frame_occurrence_unique (depth count : Nat) :
    OriginalOccurrenceUnique input (Runtime.frames input depth count) := by
  induction count with
  | zero =>
      exact fun _ occurrence => AccountSource.occurrence_eq_emitted input _ _ occurrence
  | succ count previous =>
      change OriginalOccurrenceUnique input ((Runtime.frames input depth count).next input)
      unfold Runtime.Frame.next
      split
      · exact fun _ occurrence => Admission.occurrence_eq_emitted input _ _ occurrence
      · exact previous

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Continuation
