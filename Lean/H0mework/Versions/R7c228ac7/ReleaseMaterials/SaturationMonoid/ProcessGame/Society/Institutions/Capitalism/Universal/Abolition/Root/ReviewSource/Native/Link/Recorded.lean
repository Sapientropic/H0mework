import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native.Link.Scope
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native.Readout

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native.Link

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.PublicFunction
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Registered Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (code : SourceCode Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  {task : Material.OriginalTask code.input depth count}
  (identity : SameBirth code depth count task)
  (current : Physical.Cursor Party Good Port Technology Instrument)

include identity in
/-- The equality identifies an already recorded creator. This consumer
never upgrades an undisclosed input into a known native scope. -/
theorem the_already_recorded_source_scope_consumes_its_actual_material_payments
    (scope : RecordedAt code.input depth count prefixLimit renewalLimit current)
    (sameCreator : scope.origin = .source code)
    (paid : ∀ index : Material.Slot code.input depth count task,
      (Material.payment? code.input depth count prefixLimit renewalLimit task current index).isSome = true) :
    OriginalScopePaid code.input depth count prefixLimit renewalLimit current (.recorded scope) := by
  rcases scope with ⟨origin, state, generated⟩
  change origin = .source code at sameCreator
  cases sameCreator
  intro index
  change (state index).current.TerminalAt 0
  rw [generated index]
  exact SameBirth.the_whole_paid_material_scope_consumes_the_whole_original_native_scope
    code depth count prefixLimit renewalLimit identity current paid index

#print axioms the_already_recorded_source_scope_consumes_its_actual_material_payments

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native.Link
