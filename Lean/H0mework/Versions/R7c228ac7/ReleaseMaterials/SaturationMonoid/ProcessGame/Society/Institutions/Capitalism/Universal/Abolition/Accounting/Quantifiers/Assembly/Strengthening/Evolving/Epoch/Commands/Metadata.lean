import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Complete

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Current

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution

noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (current : Current (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
  (complete : ¬ Public.Inquiry.HasWork current.native.frame current.native.actual.actual)

/-- This consumes the real empty physical inventory, not a proposed target
account or an assertion that the next responsibility is already settled. -/
theorem an_empty_actual_body_has_no_native_head
    (empty : current.physicalResult.execution.items = []) :
    ¬ Public.Inquiry.HasWork (Transition.next current complete).native.frame
      (Transition.next current complete).native.actual.actual := by
  have physical : (Physical.Public.execution current.native.input current.native.depth current.native.count current.native.prefixLimit
      current.native.renewalLimit current.native.oldPast
      (Factory.Direct.selectedStart current.native.full current.native.sourceActual current.executionReader)).items = [] := empty
  have items : Public.Accounting.items current.native.input current.native.depth current.native.count current.native.prefixLimit
      current.native.renewalLimit current.native.oldPast
      (Factory.Direct.selectedStart current.native.full current.native.sourceActual current.executionReader) = [] :=
    List.map_eq_nil_iff.mp ((Public.Accounting.actual_items_are_the_same_public_execution _ _ _ _ _ _ _).trans physical)
  change ¬ (true = false ∨
    (Public.Accounting.items current.native.input current.native.depth current.native.count current.native.prefixLimit
      current.native.renewalLimit current.native.oldPast
      (Factory.Direct.selectedStart current.native.full current.native.sourceActual current.executionReader))[0]?.isSome = true)
  rw [items]
  simp
  rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Current
