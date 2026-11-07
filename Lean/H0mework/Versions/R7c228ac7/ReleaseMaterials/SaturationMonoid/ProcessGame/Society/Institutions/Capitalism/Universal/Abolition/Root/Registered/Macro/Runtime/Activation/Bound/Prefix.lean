import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Activation.Bound.State

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
local notation "O" => Frame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount

theorem original_internal_prefix_is_the_original_paid_inventory
    (frame : O) (steps : Nat) (within : steps ≤ Bound.minor frame) :
    after (.original frame : F) steps = .original (Bound.after frame steps) := by
  induction steps generalizing frame with
  | zero => rfl
  | succ steps inherited =>
    have positive : 0 < Bound.minor frame := by omega
    have spent := (Bound.every_pending_accounting_query_pays_one_original_item frame frame.query positive).1
    have tail : steps ≤ Bound.minor frame.next := by change Bound.minor frame.next + 1 = _ at spent; omega
    calc
      after (.original frame : F) (steps + 1) = after (ActivatedFrame.next (.original frame : F)) steps := (after_next _ _).symm
      _ = after (.original frame.next : F) steps := congrArg (fun current => after current steps)
        (original_next_is_its_actual_internal_step frame positive)
      _ = .original (Bound.after frame.next steps) := inherited frame.next tail
      _ = .original (Bound.after frame (steps + 1)) := congrArg ActivatedFrame.original (Bound.after_next frame steps)

theorem enacted_prefix_is_the_same_public_source
    (origin : Abolition.Functions.Revision.Context (input := input) (review := review)
      depth count prefixLimit renewalLimit sourceDepth sourceCount)
    (admission : Abolition.Functions.Revision.InitialAdmissionAt origin)
    (frame : Public.Runtime.Frame origin admission) (steps : Nat) :
    after (.enacted origin admission frame : F) steps = .enacted origin admission (frame.visits steps) := by
  induction steps with
  | zero => rfl
  | succ steps inherited =>
    rw [after_succ, inherited]
    exact congrArg (ActivatedFrame.enacted origin admission) (Function.iterate_succ_apply' _ _ _).symm

#print axioms original_internal_prefix_is_the_original_paid_inventory
#print axioms enacted_prefix_is_the_same_public_source

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.ActivatedFrame
