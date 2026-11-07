import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Activation.Next
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Bound.Accounting
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Frame.First

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

def internalMass : F → Nat
  | .original current => Bound.minor current
  | .enacted _ _ current => current.sourceMass

def after (frame : F) (steps : Nat) : F := (next^[steps]) frame

theorem after_succ (frame : F) (steps : Nat) : after frame (steps + 1) = (after frame steps).next :=
  Function.iterate_succ_apply' _ _ _

theorem after_next (frame : F) (steps : Nat) : after frame.next steps = after frame (steps + 1) :=
  (Function.iterate_succ_apply _ _ _).symm

theorem original_next_is_its_actual_internal_step (frame : O) (positive : 0 < Bound.minor frame) :
    ActivatedFrame.next (.original frame : F) = .original frame.next := by
  dsimp only [ActivatedFrame.next]
  split
  · rename_i work selected
    exact congrArg ActivatedFrame.original (congrArg frame.nextAt (frame.query_unique (.internal work)))
  · rename_i germ selected
    have zero : Bound.minor frame = 0 :=
      (Bound.zero_rank_iff_complete (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
        frame.start frame.proposal frame.sourcePosition frame.cursor).mpr germ.complete
    omega

theorem every_pending_internal_next_spends_one (frame : F) (positive : 0 < internalMass frame) :
    internalMass frame.next + 1 = internalMass frame := by
  cases frame with
  | original current =>
    rw [original_next_is_its_actual_internal_step current positive]
    exact (Bound.every_pending_accounting_query_pays_one_original_item current current.query positive).1
  | enacted origin admission current =>
    exact current.next_spends_one_source_position (current.work_iff_positive_mass.mpr positive)

#print axioms original_next_is_its_actual_internal_step
#print axioms every_pending_internal_next_spends_one

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.ActivatedFrame
