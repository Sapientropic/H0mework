import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Context
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Migration.ImplicitReview.Completion.Native.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Trigger

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {review : Option (ReviewPhase.ContextAt input)}
  (context : Context (input := input) (review := review) depth count prefixLimit renewalLimit sourceDepth sourceCount)

/-- The old installed payload is transported only across its proved
same-germ equality. No creator is reconstructed from an Input or task. -/
def nativeAtGerm : Abolition.Root.ReviewSource.Native.ReadoutsAt input depth count prefixLimit renewalLimit context.germ.snapshot :=
  Eq.mp (congrArg (Abolition.Root.ReviewSource.Native.ReadoutsAt input depth count prefixLimit renewalLimit)
    (the_installed_snapshot_is_the_same_original_germ context)) (originalNative context)

def nativeInspection (task : Abolition.Root.ReviewSource.Material.OriginalTask input depth count) :=
  Macro.Services.Migration.ImplicitReview.Completion.Native.produceBoth task context.germ.snapshot (nativeAtGerm context)

def nativePaid (task : Abolition.Root.ReviewSource.Material.OriginalTask input depth count) : Bool :=
  (nativeInspection context task).explicit.hasPaidScope && (nativeInspection context task).registered.hasPaidScope

private theorem paid_result_has_its_original_terminal
    (task : Abolition.Root.ReviewSource.Material.OriginalTask input depth count)
    (readout : Abolition.Root.ReviewSource.Native.ReadoutAt input depth count prefixLimit renewalLimit context.germ.snapshot)
    (result : Macro.Services.Migration.ImplicitReview.Completion.Native.ReadoutResult task context.germ.snapshot readout)
    (paid : result.hasPaidScope = true) :
    Abolition.Root.ReviewSource.Native.OriginalScopePaid input depth count prefixLimit renewalLimit context.germ.snapshot readout := by
  cases result with
  | undisclosed => cases paid
  | unpaid _ _ _ => cases paid
  | recorded scope actual =>
      cases actual with
      | paid terminal => exact terminal
      | residual _ => cases paid

theorem the_source_gate_pays_both_original_creators
    (task : Abolition.Root.ReviewSource.Material.OriginalTask input depth count)
    (paid : nativePaid context task = true) :
    Abolition.Root.ReviewSource.Native.OriginalScopePaid input depth count prefixLimit renewalLimit context.germ.snapshot
        (nativeAtGerm context).explicit ∧
      Abolition.Root.ReviewSource.Native.OriginalScopePaid input depth count prefixLimit renewalLimit context.germ.snapshot
        (nativeAtGerm context).registered := by
  have both := Bool.and_eq_true_iff.mp paid
  exact ⟨paid_result_has_its_original_terminal context task _ _ both.1,
    paid_result_has_its_original_terminal context task _ _ both.2⟩

#print axioms nativeAtGerm
#print axioms nativeInspection
#print axioms the_source_gate_pays_both_original_creators

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Trigger
