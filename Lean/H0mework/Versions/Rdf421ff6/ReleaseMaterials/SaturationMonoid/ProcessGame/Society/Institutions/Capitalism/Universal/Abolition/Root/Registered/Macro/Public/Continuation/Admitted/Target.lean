import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Continuation.Admitted.Report
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Continuation.Admitted.Ledger
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Inquiry.Faces.Component
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress.Next

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Continuation.Admitted

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {review : Option (ReviewPhase.ContextAt input)}
  (origin : Abolition.Functions.Revision.Context (input := input) (review := review)
    depth count prefixLimit renewalLimit sourceDepth sourceCount)
  (admission : Abolition.Functions.Revision.InitialAdmissionAt origin)
  {oldPast : List (Compile.RawInput Party Good Port Technology Instrument)}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  (frame : NativeFrame input depth count prefixLimit renewalLimit oldPast start)
  (visit : SourceNativeTemporalVisitAt frame.root.toAuthoritativeRoot.toLedgerRoot)
  (atCurrent : Inquiry.ActualAt frame visit.current)
  (reader : Macro.Raw.Reader input depth count)

def targetFrame := Inquiry.installedFrame (bareFrame origin admission frame atCurrent reader) reader
abbrev targetRoot := (targetFrame origin admission frame visit atCurrent reader).root
abbrev targetInitial := (targetRoot origin admission frame visit atCurrent reader).toAuthoritativeRoot.toRoot.initialVisit

def occurrencePresentation : ConstructivePresentation
    (frame.root.toAuthoritativeRoot.toRoot.actual.OccurrenceAt visit.current)
    ((targetRoot origin admission frame visit atCurrent reader).toAuthoritativeRoot.toRoot.actual.OccurrenceAt
      (targetInitial origin admission frame visit atCurrent reader).current) where
  forward := fun _ => (targetRoot origin admission frame visit atCurrent reader).emitted (bodyInitial frame atCurrent)
  backward := fun _ => frame.root.emitted visit.current
  backward_forward := fun occurrence => (frame.occurrence_eq_emitted occurrence).symm
  forward_backward := fun occurrence =>
    ((targetFrame origin admission frame visit atCurrent reader).occurrence_eq_emitted occurrence).symm

def firstSuccessor := (targetFrame origin admission frame visit atCurrent reader).successor
  (targetInitial origin admission frame visit atCurrent reader).current

theorem first_target_is_the_actual_selected_body :
    (firstSuccessor origin admission frame visit atCurrent reader).targetCurrent = bodyNext frame atCurrent :=
  Source.successor_current input depth count prefixLimit renewalLimit oldPast
    (selectedStart frame atCurrent reader) (family frame atCurrent) (bodyInitial frame atCurrent)

variable (complete : ¬ Inquiry.HasWork frame atCurrent.actual)
  (entry : OpenResponsibilityAt frame.N (frame.sourceSupport visit.current))
  (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt frame.root visit entry)

def targetAt (event : ExactTemporalCausalRootEventAt frame.root.toAuthoritativeRoot.toLedgerRoot visit) :
    SourceNativeSequentialActualActionTargetAt frame.root visit event entry authority := by
  rw [event.eq_generated]
  exact {
    TargetN := frame.N
    translation := translation frame
    TargetV := (targetFrame origin admission frame visit atCurrent reader).V
    targetRoot := targetRoot origin admission frame visit atCurrent reader
    targetTheory := TheoryState.rootSemantic frame.N
    lawSurface_heq := HEq.rfl
    targetTheory_rootSemantic := ⟨id, fun _ => rfl⟩
    occurrencePresentation := occurrencePresentation origin admission frame visit atCurrent reader
    occurrence_commutes := rfl
    initialSupport_heq := heq_of_eq (initial_support_is_the_same_original_current origin admission frame atCurrent reader)
    initialOpenLedger := initialLedger origin admission frame atCurrent reader
    initialOpenLedger_heq := initial_ledger_is_the_original_identity origin admission frame atCurrent reader
    initialLedger_responsibility_commutes := fun row =>
      (initial_ledger_preserves_every_original_row origin admission frame atCurrent reader row).1.symm
    initialLedger_claim_commutes := fun row =>
      (initial_ledger_preserves_every_original_row origin admission frame atCurrent reader row).2.1.symm
    initialLedger_budget_conservative := fun row =>
      (initial_ledger_preserves_every_original_row origin admission frame atCurrent reader row).2.2.le
    initialLedgerNoFresh := fun row => ⟨⟨(initialLedger origin admission frame atCurrent reader).backward row,
      ⟨initial_ledger_has_no_fresh_row origin admission frame atCurrent reader row⟩⟩⟩
    translatedSourceEntryRow := initialRow origin admission frame atCurrent reader entry
    firstSuccessor := firstSuccessor origin admission frame visit atCurrent reader
    canonical_targetNextVisit_eq := Ingress.next_is_the_same_generated_successor
      (targetRoot origin admission frame visit atCurrent reader)
      (.finite (targetInitial origin admission frame visit atCurrent reader))
      (firstSuccessor origin admission frame visit atCurrent reader)
    Answer := atCurrent.RawAnswer reader
    answer := atCurrent.rawAnswer reader
    Receipt := fun answer => ULift.{3, 0} (PLift
      ((firstSuccessor origin admission frame visit atCurrent reader).targetCurrent = bodyNext frame atCurrent ∧
        (bodyNext frame atCurrent).account = atCurrent.actual.account ∧
        ¬ Inquiry.HasWork frame atCurrent.actual ∧ answer = atCurrent.rawAnswer reader)) ×
      ULift.{3, 0} (RenewalReport origin frame atCurrent)
    receipt := ⟨⟨⟨first_target_is_the_actual_selected_body origin admission frame visit atCurrent reader,
      rfl, complete, rfl⟩⟩, ⟨renewalReport origin frame atCurrent⟩⟩ }

#print axioms targetAt

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Continuation.Admitted
