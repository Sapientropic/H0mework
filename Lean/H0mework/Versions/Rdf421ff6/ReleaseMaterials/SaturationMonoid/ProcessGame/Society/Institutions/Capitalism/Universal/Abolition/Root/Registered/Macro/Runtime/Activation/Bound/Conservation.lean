import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Activation.Bound.Completion
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Conservation
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Frame.Conservation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.ActivatedFrame

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {review : Option (ReviewPhase.ContextAt input)}

local notation "F" => ActivatedFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount

def account : F → (Epoch.Finance.process input depth count).GeneratedState
  | .original current => current.account
  | .enacted _ _ current => current.account

/-- Enactment retains the literal old GS. All other branches use their
existing native Run, including the one original debt admission. -/
def nextNative (frame : F) : (Epoch.Finance.process input depth count).Run
    frame.account.current frame.next.account.current := by
  cases frame with
  | enacted origin admission current => exact current.nextNative
  | original current =>
    dsimp only [ActivatedFrame.next]
    split
    · exact current.nativeNextAt _
    · rename_i germ selected
      split
      · exact .nil
      · exact current.nativeNextAt _

def afterNative (frame : F) : (steps : Nat) → (Epoch.Finance.process input depth count).Run
    frame.account.current (after frame steps).account.current
  | 0 => .nil
  | steps + 1 => by
      rw [after_succ]
      exact (afterNative frame steps).concatRuns (Epoch.Finance.process input depth count) (after frame steps).nextNative

theorem every_actual_prefix_keeps_all_original_claims (frame : F) (steps : Nat) :
    frame.account.current.slots.map (Epoch.Finance.slotClaim input depth count) <+:
      (after frame steps).account.current.slots.map (Epoch.Finance.slotClaim input depth count) :=
  Epoch.Finance.run_retains_all_claims input depth count (afterNative frame steps)

theorem every_actual_prefix_keeps_the_complete_native_history (frame : F) (steps : Nat) :
    frame.account.current.history <+: (after frame steps).account.current.history := by
  rw [(afterNative frame steps).history_eq]
  exact List.prefix_append _ _

#print axioms nextNative
#print axioms afterNative
#print axioms every_actual_prefix_keeps_all_original_claims
#print axioms every_actual_prefix_keeps_the_complete_native_history

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.ActivatedFrame
