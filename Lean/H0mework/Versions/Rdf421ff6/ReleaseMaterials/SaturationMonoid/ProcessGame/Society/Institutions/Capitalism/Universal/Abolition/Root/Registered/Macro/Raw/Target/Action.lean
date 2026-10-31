import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Raw.Target.Ledger
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Raw.Component
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress.Next

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Raw.Target

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  {proposal : Compile.RawInput Party Good Port Technology Instrument} {sourcePosition : Nat}
  {review : Option (ReviewPhase.ContextAt input)}
  (frame : NativeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)
  (data : Continuation.FinancialData frame) (reader : Reader input depth count)
  (sourceBasis : Inquiry.Basis frame.N)

abbrev sourceFrame := installCompleteFrame frame data reader sourceBasis
abbrev sourceRoot := (sourceFrame frame data reader sourceBasis).root

variable (visit : SourceNativeTemporalVisitAt (sourceRoot frame data reader sourceBasis).toAuthoritativeRoot.toLedgerRoot)
  (germ : GermAt frame data reader visit.current)

def targetFrame := installCompleteFrame (bareFrame frame data reader germ)
  (financialData frame data reader germ) reader (basis frame data reader germ)
abbrev targetRoot := (targetFrame frame data reader sourceBasis visit germ).root
abbrev targetInitial := (targetRoot frame data reader sourceBasis visit germ).toAuthoritativeRoot.toRoot.initialVisit

def sourceEntry := sourceBasis.entry (frame.sourceSupport visit.current)

def occurrencePresentation : ConstructivePresentation
    ((sourceRoot frame data reader sourceBasis).toAuthoritativeRoot.toRoot.actual.OccurrenceAt visit.current)
    ((targetRoot frame data reader sourceBasis visit germ).toAuthoritativeRoot.toRoot.actual.OccurrenceAt
      (targetInitial frame data reader sourceBasis visit germ).current) where
  forward := fun _ => (targetRoot frame data reader sourceBasis visit germ).emitted
    (bodyInitial frame data reader germ)
  backward := fun _ => (sourceRoot frame data reader sourceBasis).emitted visit.current
  backward_forward := fun occurrence => (data.occurrence_eq_emitted visit.current occurrence).symm
  forward_backward := fun occurrence =>
    (Reentry.occurrence_eq_emitted (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
      germ.snapshot germ.raw (family frame data reader germ) (seedEq frame data reader germ) occurrence).symm

def firstSuccessor := (targetFrame frame data reader sourceBasis visit germ).successor
  (targetInitial frame data reader sourceBasis visit germ).current

theorem first_target_is_the_same_body_next :
    (firstSuccessor frame data reader sourceBasis visit germ).targetCurrent = bodyNext frame data reader germ :=
  Reentry.successor_current (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
    germ.snapshot germ.raw (family frame data reader germ) (seedEq frame data reader germ) (bodyInitial frame data reader germ)

def targetAt
    (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt (sourceRoot frame data reader sourceBasis)
      visit (sourceEntry frame data reader sourceBasis visit))
    (event : ExactTemporalCausalRootEventAt (sourceRoot frame data reader sourceBasis).toAuthoritativeRoot.toLedgerRoot visit) :
    SourceNativeSequentialActualActionTargetAt (sourceRoot frame data reader sourceBasis) visit event
      (sourceEntry frame data reader sourceBasis visit) authority := by
  rw [event.eq_generated]
  exact {
    TargetN := frame.N
    translation := translation frame
    TargetV := (bareFrame frame data reader germ).V
    targetRoot := targetRoot frame data reader sourceBasis visit germ
    targetTheory := TheoryState.rootSemantic frame.N
    lawSurface_heq := HEq.rfl
    targetTheory_rootSemantic := ⟨id, fun _ => rfl⟩
    occurrencePresentation := occurrencePresentation frame data reader sourceBasis visit germ
    occurrence_commutes := rfl
    initialSupport_heq := heq_of_eq (initial_support_is_the_original_current frame data reader germ)
    initialOpenLedger := initialLedger frame data reader germ
    initialOpenLedger_heq := initial_ledger_is_the_original_identity frame data reader germ
    initialLedger_responsibility_commutes := fun entry =>
      (initial_ledger_preserves_responsibility frame data reader germ entry).symm
    initialLedger_claim_commutes := fun entry =>
      (initial_ledger_preserves_claim frame data reader germ entry).symm
    initialLedger_budget_conservative := fun entry =>
      (initial_ledger_preserves_budget frame data reader germ entry).le
    initialLedgerNoFresh := fun entry => ⟨⟨(initialLedger frame data reader germ).backward entry,
      ⟨initial_ledger_has_no_fresh_row frame data reader germ entry⟩⟩⟩
    translatedSourceEntryRow := initialRow frame data reader germ (sourceEntry frame data reader sourceBasis visit)
    firstSuccessor := firstSuccessor frame data reader sourceBasis visit germ
    canonical_targetNextVisit_eq := Ingress.next_is_the_same_generated_successor
      (targetRoot frame data reader sourceBasis visit germ)
      (.finite (targetInitial frame data reader sourceBasis visit germ))
      (firstSuccessor frame data reader sourceBasis visit germ)
    Answer := ResultAt frame data reader germ
    answer := reportAt frame data reader germ
    Receipt := fun answer => ULift.{3, 0} (PLift
      ((firstSuccessor frame data reader sourceBasis visit germ).targetCurrent = bodyNext frame data reader germ ∧
        (bodyNext frame data reader germ).account = frame.account visit.current ∧
        answer = reportAt frame data reader germ))
    receipt := ⟨⟨first_target_is_the_same_body_next frame data reader sourceBasis visit germ,
      first_body_retains_the_complete_original_account frame data reader germ, rfl⟩⟩ }

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Raw.Target

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Raw.Target.targetAt
