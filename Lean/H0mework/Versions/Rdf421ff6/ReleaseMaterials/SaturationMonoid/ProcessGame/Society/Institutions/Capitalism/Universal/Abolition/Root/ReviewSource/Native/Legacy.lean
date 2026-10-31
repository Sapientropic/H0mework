import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native.Fold
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Native.Micro.Append

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.PublicFunction
open Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (original : OutstandingSource Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (past : List (Compile.RawInput Party Good Port Technology Instrument)) (index : original.Slot)

theorem existing_native_thread_is_the_literal_same_prefix :
    atPast (.outstanding original) depth count prefixLimit renewalLimit past index =
      Macro.Services.Native.Micro.complete original depth count prefixLimit renewalLimit past index := by
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past raw inherited =>
      exact (atPast_append (.outstanding original) depth count prefixLimit renewalLimit past raw index).trans
        ((congrArg (fun prior : Macro.Services.Native.Micro.Attached original
            (Macro.Services.Native.originalWords original depth count) index =>
          prior.advance (Macro.Services.Native.Micro.appendedSource original depth count prefixLimit renewalLimit past raw))
          inherited).trans
          (Macro.Services.Native.Micro.complete_append_is_one_original_native_boundary
            original depth count prefixLimit renewalLimit past raw index).symm)

theorem existing_complete_state_archive_and_run_are_unchanged :
    (OriginAt.outstanding original).state depth count
        (atPast (.outstanding original) depth count prefixLimit renewalLimit past index) =
      (Macro.Services.Native.Micro.complete original depth count prefixLimit renewalLimit past index).state := by
  rw [existing_native_thread_is_the_literal_same_prefix]
  rfl

#print axioms existing_native_thread_is_the_literal_same_prefix
#print axioms existing_complete_state_archive_and_run_are_unchanged

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native
