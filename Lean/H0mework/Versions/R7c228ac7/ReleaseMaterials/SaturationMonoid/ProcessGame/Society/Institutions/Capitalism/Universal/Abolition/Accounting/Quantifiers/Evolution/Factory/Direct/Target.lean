import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Direct.Frame
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress.Next

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Direct

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit : Nat}
  {oldPast : List (Compile.RawInput Party Good Port Technology Instrument)}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  (frame : Public.NativeFrame input depth count prefixLimit renewalLimit oldPast start)
  (visit : SourceNativeTemporalVisitAt frame.root.toAuthoritativeRoot.toLedgerRoot)
  (atCurrent : Public.Inquiry.ActualAt frame visit.current)
  (reader : Macro.Raw.Reader input depth count)

def occurrencePresentation : ConstructivePresentation
    (frame.root.toAuthoritativeRoot.toRoot.actual.OccurrenceAt visit.current)
    ((targetRoot frame atCurrent reader).toAuthoritativeRoot.toRoot.actual.OccurrenceAt
      (targetInitial frame atCurrent reader).current) where
  forward := fun _ => (targetRoot frame atCurrent reader).emitted (bodyInitial frame atCurrent)
  backward := fun _ => frame.root.emitted visit.current
  backward_forward := fun occurrence => (frame.occurrence_eq_emitted occurrence).symm
  forward_backward := fun occurrence => ((targetFrame frame atCurrent reader).occurrence_eq_emitted occurrence).symm

variable (complete : ¬ Public.Inquiry.HasWork frame atCurrent.actual)
  (entry : OpenResponsibilityAt frame.N (frame.sourceSupport visit.current))
  (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt frame.root visit entry)

def targetAt (event : ExactTemporalCausalRootEventAt frame.root.toAuthoritativeRoot.toLedgerRoot visit) :
    SourceNativeSequentialActualActionTargetAt frame.root visit event entry authority := by
  rw [event.eq_generated]
  exact {
    TargetN := frame.N
    translation := translation frame
    TargetV := (targetFrame frame atCurrent reader).V
    targetRoot := targetRoot frame atCurrent reader
    targetTheory := TheoryState.rootSemantic frame.N
    lawSurface_heq := HEq.rfl
    targetTheory_rootSemantic := ⟨id,fun _ => rfl⟩
    occurrencePresentation := occurrencePresentation frame visit atCurrent reader
    occurrence_commutes := rfl
    initialSupport_heq := heq_of_eq (the_target_starts_with_the_same_whole_source_support frame atCurrent reader)
    initialOpenLedger := initialLedger frame atCurrent reader
    initialOpenLedger_heq := initial_ledger_is_the_original_identity frame atCurrent reader
    initialLedger_responsibility_commutes := fun row => (initial_ledger_preserves_every_original_row frame atCurrent reader row).1.symm
    initialLedger_claim_commutes := fun row => (initial_ledger_preserves_every_original_row frame atCurrent reader row).2.1.symm
    initialLedger_budget_conservative := fun row => (initial_ledger_preserves_every_original_row frame atCurrent reader row).2.2.le
    initialLedgerNoFresh := fun row => ⟨⟨(initialLedger frame atCurrent reader).backward row,
      ⟨initial_ledger_has_no_fresh_row frame atCurrent reader row⟩⟩⟩
    translatedSourceEntryRow := initialRow frame atCurrent reader entry
    firstSuccessor := firstSuccessor frame atCurrent reader
    canonical_targetNextVisit_eq := Ingress.next_is_the_same_generated_successor
      (targetRoot frame atCurrent reader) (.finite (targetInitial frame atCurrent reader)) (firstSuccessor frame atCurrent reader)
    Answer := atCurrent.RawAnswer reader
    answer := atCurrent.rawAnswer reader
    Receipt := fun answer => ULift.{3,0} (PLift
      ((firstSuccessor frame atCurrent reader).targetCurrent = bodyNext frame atCurrent ∧
        (bodyNext frame atCurrent).account = atCurrent.actual.account ∧
        ¬ Public.Inquiry.HasWork frame atCurrent.actual ∧ answer = atCurrent.rawAnswer reader))
    receipt := ⟨⟨first_target_is_the_actual_selected_body frame atCurrent reader,rfl,complete,rfl⟩⟩ }

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Direct
