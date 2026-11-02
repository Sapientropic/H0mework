import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Runtime.Selection

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered
open Functions.Revision

noncomputable section

variable {origin : Context (input := input) (review := none) 0 count 0 0 0 count}
  {admission : InitialAdmissionAt origin}

theorem the_generated_drain_keeps_the_actual_body_and_complete_account_run
    (frame : Macro.Public.Runtime.Frame origin admission) :
    frame.drained.snapshot = frame.snapshot ∧
      frame.account.current.history <+: frame.drained.account.current.history ∧
      frame.account.current.slots.map (Epoch.Finance.slotClaim input 0 count) <+:
        frame.drained.account.current.slots.map (Epoch.Finance.slotClaim input 0 count) :=
  ⟨Observation.the_generated_internal_drain_keeps_the_same_actual_snapshot frame,
    frame.visits_keep_the_complete_original_history _, frame.visits_keep_all_original_claims _⟩

theorem an_actual_public_current_reaches_its_own_native_boundary
    (nature : RequestAt) (frame : Macro.Public.Runtime.Frame origin admission) (tick : Nat)
    (actual : current nature tick = .enacted origin admission frame) :
    current nature (Macro.Runtime.internalBoundaryTick (review := none)
      input 0 0 datum 0 0 (reader nature) tick) =
        .enacted origin admission frame.drained := by
  calc
    current nature (Macro.Runtime.internalBoundaryTick (review := none)
        input 0 0 datum 0 0 (reader nature) tick) =
      Macro.Runtime.ActivatedFrame.after (current nature tick) (current nature tick).complete.steps :=
      (Macro.Runtime.actual_internal_fold_is_the_same_registered_history (review := none)
        input 0 0 datum 0 0 (reader nature) tick _).symm
    _ = .enacted origin admission frame.drained := by
      rw [actual]
      exact Macro.Runtime.ActivatedFrame.enacted_prefix_is_the_same_public_source origin admission frame _

theorem an_actual_public_step_reaches_its_own_next_native_boundary
    (nature : RequestAt) (frame : Macro.Public.Runtime.Frame origin admission) (tick : Nat)
    (actual : current nature tick = .enacted origin admission frame) :
    current nature (Macro.Runtime.internalBoundaryTick (review := none)
      input 0 0 datum 0 0 (reader nature) (tick + 1)) =
        .enacted origin admission frame.next.drained := by
  apply an_actual_public_current_reaches_its_own_native_boundary nature frame.next (tick + 1)
  change (current nature tick).next = _
  rw [actual]
  rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation
