import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Consumers.Evolving
import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Root.Menus

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Consumers.Evolving

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered

noncomputable section

private theorem excludes_refusal (word : W) (blocked : ¬ Conflict.Root.Paid source word) :
    Conflict.Root.admit source word = none := by
  unfold Conflict.Root.admit
  cases Conflict.Root.inspect source word with
  | paid actual => exact (blocked actual).elim
  | rejected failure => rfl

def unauthorisedLevy : R := ⟨false, [], false, [true], .transfer false true [(false, 6)]⟩

theorem the_real_menu_filters_the_unsigned_control_and_finds_the_flip :
    Conflict.Root.pressure source decisionStock [[unauthorisedLevy], conflict] [peace] = some 4 ∧
      Conflict.Root.pressure source decisionStock [restored 4] [peace] = some 0 ∧
      Conflict.Root.pressure source decisionStock [restored 6] [peace] = some (-2) := by
  have blocked : ¬ Conflict.Root.Paid source [unauthorisedLevy] := by
    intro paid
    have guard : source.native.input.law.Valid source.raw unauthorisedLevy :=
      paid.authorized ⟨0, source.raw, unauthorisedLevy⟩ List.mem_cons_self
    rw [sourceInput, sourceRead] at guard
    have denied : ¬ compact.law.Valid oldRaw unauthorisedLevy := by decide +kernel
    exact denied guard
  have pruned : Conflict.Root.admitted source [[unauthorisedLevy], conflict] =
      Conflict.Root.admitted source [conflict] := by
    simp only [Conflict.Root.admitted, List.filterMap_cons, excludes_refusal _ blocked]
  refine ⟨?_, (Conflict.Root.pressure_of_two_paid_words decisionStock bindingReturnPaid peacePaid).trans (congrArg some binding_return_is_a_paid_tie),
    (Conflict.Root.pressure_of_two_paid_words decisionStock fullReturnPaid peacePaid).trans (congrArg some restored_war_peace_gap)⟩
  change Threshold.gap _ _ (Conflict.Root.admitted source [[unauthorisedLevy], conflict]) _ = _
  rw [pruned]
  exact (Conflict.Root.pressure_of_two_paid_words decisionStock conflictPaid peacePaid).trans (congrArg some old_war_peace_gap)

#print axioms the_real_menu_filters_the_unsigned_control_and_finds_the_flip

end
end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Consumers.Evolving
