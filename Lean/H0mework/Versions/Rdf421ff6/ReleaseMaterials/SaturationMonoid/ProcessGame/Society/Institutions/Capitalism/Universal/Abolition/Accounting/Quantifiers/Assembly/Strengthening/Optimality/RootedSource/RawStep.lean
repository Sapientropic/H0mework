import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.RootedSource.Head

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.RootedSource
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger
noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  (current : Position input)

theorem the_paid_body_retains_its_exact_actual_history
    (history : List (Compile.RawInput Party Good Port Technology Instrument))
    (request : Request Party Good Port Technology Instrument)
    (sameStart : current.start = Primitive.start history request)
    (bodyPaid : current.actual.actual.bodyPaid = true) :
    current.actual.readerCursor.past = history ++ [.primitive request] := by
  simp only [Public.Inquiry.ActualAt.readerCursor,Physical.receive,Physical.Prefix.past_readback,List.nil_append]
  simp only [Public.Inquiry.ActualAt.snapshot,bodyPaid,if_true]
  rw [sameStart]
  simp only [Physical.next,Primitive.start,Physical.receive,Physical.Prefix.past_readback]

theorem the_current_root_selects_the_identical_original_primitive
    (complete : ¬ Public.Inquiry.HasWork current.frame current.actual.actual)
    (history : List (Compile.RawInput Party Good Port Technology Instrument))
    (request : Request Party Good Port Technology Instrument)
    (past : current.actual.readerCursor.past = history)
    (selected : current.actual.proposal current.reader = .primitive request) :
    (current.raw complete).start = Primitive.start history request := by
  change Public.Scope.selectedCursor input 0 0 0 0 [] current.actual.snapshot
    (current.actual.proposal current.reader) = _
  rw [selected,Public.Scope.selectedCursor,
    (Primitive.the_existing_raw_scope_preserves_each_original_primitive input 0 0 current.actual.snapshot request).1]
  have same : current.actual.snapshot.past = history := by
    simpa only [Public.Inquiry.ActualAt.readerCursor,Physical.receive,Physical.Prefix.past_readback,List.nil_append] using past
  unfold Primitive.start Physical.receive
  rw [same,Physical.Prefix.past_readback]

theorem the_actual_raw_body_uses_the_same_account_and_initial_native_position
    (complete : ¬ Public.Inquiry.HasWork current.frame current.actual.actual) :
    (current.raw complete).actual.actual.account = current.actual.actual.account ∧
      (current.raw complete).actual.actual.bodyPaid = true ∧
      (current.raw complete).actual.actual.position = 0 := ⟨rfl,rfl,rfl⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.RootedSource
