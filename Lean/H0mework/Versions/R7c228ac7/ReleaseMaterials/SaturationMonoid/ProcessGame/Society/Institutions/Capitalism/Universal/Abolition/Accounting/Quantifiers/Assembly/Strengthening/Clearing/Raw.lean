import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing.Physical

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

theorem the_actual_raw_records_the_original_submitted_primitive
    (complete : ¬ Public.Inquiry.HasWork current.frame current.actual.actual) :
    (current.raw complete).actual.readerCursor.past =
      current.actual.readerCursor.past ++ [.primitive request] := by
  change (Physical.receive (Physical.Prefix.cursor (current.oldPast ++
    (Physical.next (Factory.Direct.selectedStart current.full current.sourceActual current.reader)).past)) .advance).past = _
  rw [the_current_primitive_uses_the_original_scope_delegate current request selected]
  simp only [Physical.receive,Physical.next,Physical.Prefix.past_readback,
    Public.Inquiry.ActualAt.readerCursor,List.append_assoc]

omit request selected in
theorem the_actual_raw_starts_at_zero_financial_position
    (complete : ¬ Public.Inquiry.HasWork current.frame current.actual.actual) :
    (current.raw complete).actual.actual.position = 0 ∧
      (current.raw complete).actual.actual.bodyPaid = true := ⟨rfl,rfl⟩

theorem the_actual_raw_retains_the_original_physical_source
    (complete : ¬ Public.Inquiry.HasWork current.frame current.actual.actual) :
    Public.Accounting.physical (current.raw complete).input (current.raw complete).depth (current.raw complete).count
      (current.raw complete).prefixLimit (current.raw complete).renewalLimit (current.raw complete).oldPast
      (current.raw complete).start (current.raw complete).actual.actual =
    (Physical.Public.compile current.input
      (Public.Scope.actualState current.input current.depth current.count current.prefixLimit current.renewalLimit
        current.oldPast current.actual.snapshot) (.primitive request)).next := by
  change Public.Accounting.physical current.input current.depth current.count current.prefixLimit current.renewalLimit
    current.oldPast (Factory.Direct.selectedStart current.full current.sourceActual current.reader)
      (Factory.Direct.bodyNext current.full current.sourceActual) = _
  refine (Factory.Direct.the_new_body_is_the_current_readers_actual_public_result
    current.full current.sourceActual current.reader).trans ?_
  change (Public.Scope.actualResult current.input current.depth current.count current.prefixLimit current.renewalLimit
    current.oldPast current.actual.snapshot (current.actual.proposal current.reader)).next = _
  rw [selected]
  unfold Public.Scope.actualResult Public.Scope.selectedCursor
  rw [(Public.Scope.every_nonperiod_proposal_keeps_its_actual_route current.input current.depth current.count
    current.prefixLimit current.renewalLimit current.oldPast current.actual.snapshot (.primitive request) rfl).1]
  rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing
