import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Native.Raw

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (current : Evolving.NativeCurrent (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (request : Request Party Good Port Technology Instrument)
  (selected : current.actual.proposal current.reader = .primitive request)

include selected

theorem the_current_primitive_uses_the_original_scope_delegate :
    Factory.Direct.selectedStart current.full current.sourceActual current.reader =
      Physical.receive current.actual.snapshot (.primitive request) := by
  change Public.Scope.selectedCursor current.input current.depth current.count current.prefixLimit
    current.renewalLimit current.oldPast current.actual.snapshot (current.actual.proposal current.reader) = _
  rw [selected]
  unfold Public.Scope.selectedCursor
  rw [(Public.Scope.every_nonperiod_proposal_keeps_its_actual_route current.input current.depth current.count
    current.prefixLimit current.renewalLimit current.oldPast current.actual.snapshot (.primitive request) rfl).1]

theorem the_source_keeps_the_same_primitive_failure_channel :
    Public.Scope.failure? current.input current.depth current.count current.prefixLimit current.renewalLimit
      current.oldPast current.actual.snapshot (current.actual.proposal current.reader) = none ∧
    Public.Scope.deferred current.input current.depth current.count current.prefixLimit current.renewalLimit
      current.oldPast current.actual.snapshot (current.actual.proposal current.reader) = none := by
  rw [selected]
  exact (Public.Scope.every_nonperiod_proposal_keeps_its_actual_route current.input current.depth current.count
    current.prefixLimit current.renewalLimit current.oldPast current.actual.snapshot (.primitive request) rfl).2

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing
