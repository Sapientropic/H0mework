import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Trigger.Model

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

/-- The original current chooses the route. There is no caller mode,
replacement certificate, actor inventory or promised continuation. -/
def select : Selection context :=
  match Mandatory.CurrentScope.inspect input depth count prefixLimit renewalLimit context.germ.snapshot with
  | .seeking phase => .seeking phase
  | .rejected failure => .scopeResidual failure
  | .accepted word phase checked =>
      let scope : ScopedAt context := ⟨word, phase, checked⟩
      match source : Abolition.Root.ReviewSource.Control.boundary? input depth count prefixLimit renewalLimit context.germ.snapshot with
      | none => .ordinary source
      | some boundary =>
          if fresh : currentPaidBoundaryFlag context boundary = true then
            let material : CurrentMaterialAt context :=
              ⟨boundary, source, the_finite_source_clock_test_recovers_the_exact_paid_current context boundary fresh⟩
            .enactment ⟨material, scope, nativeInspection context (material.task context), rfl⟩
          else .boundaryResidual boundary source (Bool.eq_false_iff.mpr fresh)

theorem every_enactment_carries_both_original_native_dispositions (ready : ReadyAt context) :
    ready.services = nativeInspection context (ready.material.task context) := ready.services_exact

theorem every_enactment_has_the_original_whole_current_scope (ready : ReadyAt context) :
    Mandatory.CurrentScope.Checks input depth count prefixLimit renewalLimit
      context.germ.snapshot ready.scope.word := ready.scope.checked

#print axioms select
#print axioms every_enactment_carries_both_original_native_dispositions
#print axioms every_enactment_has_the_original_whole_current_scope

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Trigger
