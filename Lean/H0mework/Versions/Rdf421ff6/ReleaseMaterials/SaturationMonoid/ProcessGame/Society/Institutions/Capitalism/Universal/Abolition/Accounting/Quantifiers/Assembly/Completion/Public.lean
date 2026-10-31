import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Completion.Root
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Public.Complete

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Completion

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Source.Program Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type} {N : WorldRelationNetwork}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (source : Evolution.Factory.Context (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) N)

theorem every_registered_source_has_its_actual_capital_excluding_public_next :
    Evolution.Factory.Public.EnactedAt source ∧
      Global.NoCapital (Evolution.Factory.Context.readLaw (Evolution.Factory.Public.next source)) := by
  have actual := Evolution.Factory.Public.every_source_continuation_has_an_actual_public_context source
  exact ⟨actual,Global.noCapitalOfOpen _ actual.no_private_permission⟩

theorem no_bound_continuation_recreates_capital_under_its_actual_active_interpreter
    (bound : Evolution.Factory.Public.BoundContinuation (Evolution.Factory.Public.next source)) :
    Global.NoCapital bound.program.law := by
  have actual := every_registered_source_has_its_actual_capital_excluding_public_next source
  rw [actual.1.native_continuation_binding bound]
  rw [← actual.1.active_interpreter]
  exact actual.2

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Completion
