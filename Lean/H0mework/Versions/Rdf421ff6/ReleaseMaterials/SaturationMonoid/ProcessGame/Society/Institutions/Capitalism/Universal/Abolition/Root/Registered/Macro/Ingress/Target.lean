import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress.FirstBody
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress.Next
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Inquiry.Package

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth sourceStart : Nat)
  (datum : Datum input depth sourceStart) (prefixLimit renewalLimit : Nat)
  (reader : Raw.Reader input depth (cut input depth sourceStart))
  (review : Option (ReviewPhase.ContextAt input) := none)

def targetFrame := (Inquiry.basePackage (review := review) input depth (cut input depth sourceStart) prefixLimit renewalLimit
  depth (cut input depth sourceStart) Physical.initial
  (proposal (review := review) input depth sourceStart datum prefixLimit renewalLimit) 0 reader datum.nativeOrigin).frame

def targetRoot := (targetFrame (review := review) input depth sourceStart datum prefixLimit renewalLimit reader).root

def targetInitial := (targetRoot (review := review) input depth sourceStart datum prefixLimit renewalLimit reader).toAuthoritativeRoot.toRoot.initialVisit

def occurrencePresentation : ConstructivePresentation
    ((root (review := review) input depth sourceStart datum prefixLimit renewalLimit).toAuthoritativeRoot.toRoot.actual.OccurrenceAt
      (visit (review := review) input depth sourceStart datum prefixLimit renewalLimit).current)
    ((targetRoot (review := review) input depth sourceStart datum prefixLimit renewalLimit reader).toAuthoritativeRoot.toRoot.actual.OccurrenceAt
      (targetInitial (review := review) input depth sourceStart datum prefixLimit renewalLimit reader).current) where
  forward := fun _ => (targetRoot (review := review) input depth sourceStart datum prefixLimit renewalLimit reader).emitted
    (bodyInitial (review := review) input depth sourceStart datum prefixLimit renewalLimit)
  backward := fun _ => (frame input depth sourceStart).native.root.emitted (frame input depth sourceStart).visit.current
  backward_forward := fun occurrence =>
    (Continuation.actual_frame_occurrence_unique input depth (cut input depth sourceStart) _ occurrence).symm
  forward_backward := fun occurrence =>
    (Accounting.occurrence_eq_emitted (review := review) input depth (cut input depth sourceStart) prefixLimit renewalLimit
      depth (cut input depth sourceStart) Physical.initial (proposal (review := review) input depth sourceStart datum prefixLimit renewalLimit) 0 occurrence).symm

def initialRow :
    ((targetRoot (review := review) input depth sourceStart datum prefixLimit renewalLimit reader).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (.finite (targetInitial (review := review) input depth sourceStart datum prefixLimit renewalLimit reader))).GeneratedEntryRowAt
      ((initialLedger (review := review) input depth sourceStart datum prefixLimit renewalLimit).forward
        (Continuation.sourceEntry input (frame input depth sourceStart))) := by
  let current := bodyInitial (review := review) input depth sourceStart datum prefixLimit renewalLimit
  let compiler := Accounting.ledgerCompiler (review := review) input depth (cut input depth sourceStart) prefixLimit renewalLimit
    depth (cut input depth sourceStart) Physical.initial (proposal (review := review) input depth sourceStart datum prefixLimit renewalLimit) 0
  let occurrence := Accounting.emitted (review := review) input depth (cut input depth sourceStart) prefixLimit renewalLimit
    depth (cut input depth sourceStart) Physical.initial (proposal (review := review) input depth sourceStart datum prefixLimit renewalLimit) 0 current
  let entry := (initialLedger (review := review) input depth sourceStart datum prefixLimit renewalLimit).forward
    (Continuation.sourceEntry input (frame input depth sourceStart))
  let selected := sourceNativeFiniteLedgerPatchGeneratedEntry? _ compiler.ExactTransitionAt
    compiler.writeRowSource compiler.terminalRowSource (compiler.compile occurrence) (compiler.compilePatch occurrence) entry
  have present : selected.isSome = true := by
    let check (packet : Σ image : SourceNativeLedgerEvolutionAt _ occurrence,
        SourceNativeFiniteLedgerPatchAt _ compiler.ExactTransitionAt compiler.writeRowSource compiler.terminalRowSource image) : Bool :=
      (sourceNativeFiniteLedgerPatchGeneratedEntry? _ compiler.ExactTransitionAt
        compiler.writeRowSource compiler.terminalRowSource packet.1 packet.2 entry).isSome
    change check (Accounting.sourcePacket (review := review) input depth (cut input depth sourceStart) prefixLimit renewalLimit
      depth (cut input depth sourceStart) Physical.initial (proposal (review := review) input depth sourceStart datum prefixLimit renewalLimit) 0 occurrence) = true
    dsimp only [occurrence, Accounting.sourcePacket]
    split <;> rfl
  exact SourceNativeTemporalVisitGeneratedEvolutionAt.GeneratedEntryRowAt.ofSourceRow (selected.get present)

def firstSuccessor : SourceNativeLedgerGeneratedSuccessorAt
    ((targetRoot (review := review) input depth sourceStart datum prefixLimit renewalLimit reader).emitted
      (targetInitial (review := review) input depth sourceStart datum prefixLimit renewalLimit reader).current)
    ((targetRoot (review := review) input depth sourceStart datum prefixLimit renewalLimit reader).toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
      (targetInitial (review := review) input depth sourceStart datum prefixLimit renewalLimit reader).current) :=
  Accounting.successor (review := review) input depth (cut input depth sourceStart) prefixLimit renewalLimit
    depth (cut input depth sourceStart) Physical.initial (proposal (review := review) input depth sourceStart datum prefixLimit renewalLimit) 0
    (bodyInitial (review := review) input depth sourceStart datum prefixLimit renewalLimit)

theorem first_target_is_the_source_body_next :
    (firstSuccessor (review := review) input depth sourceStart datum prefixLimit renewalLimit reader).targetCurrent =
      bodyNext (review := review) input depth sourceStart datum prefixLimit renewalLimit :=
  Accounting.successor_current (review := review) input depth (cut input depth sourceStart) prefixLimit renewalLimit
    depth (cut input depth sourceStart) Physical.initial (proposal (review := review) input depth sourceStart datum prefixLimit renewalLimit) 0
    (bodyInitial (review := review) input depth sourceStart datum prefixLimit renewalLimit)

def targetAt (event : ExactTemporalCausalRootEventAt
    (root (review := review) input depth sourceStart datum prefixLimit renewalLimit).toAuthoritativeRoot.toLedgerRoot
    (visit (review := review) input depth sourceStart datum prefixLimit renewalLimit)) :
    SourceNativeSequentialActualActionTargetAt (root (review := review) input depth sourceStart datum prefixLimit renewalLimit)
      (visit (review := review) input depth sourceStart datum prefixLimit renewalLimit) event
      (Continuation.sourceEntry input (frame input depth sourceStart))
      (authority (review := review) input depth sourceStart datum prefixLimit renewalLimit) := by
  rw [event.eq_generated]
  exact {
    TargetN := targetWorld (review := review) input depth sourceStart datum prefixLimit renewalLimit
    translation := translation input depth sourceStart
    TargetV := Accounting.V (review := review) input depth (cut input depth sourceStart) prefixLimit renewalLimit
      depth (cut input depth sourceStart) Physical.initial (proposal (review := review) input depth sourceStart datum prefixLimit renewalLimit) 0
    targetRoot := targetRoot (review := review) input depth sourceStart datum prefixLimit renewalLimit reader
    targetTheory := TheoryState.rootSemantic (targetWorld (review := review) input depth sourceStart datum prefixLimit renewalLimit)
    lawSurface_heq := HEq.rfl
    targetTheory_rootSemantic := ⟨id, fun _ => rfl⟩
    occurrencePresentation := occurrencePresentation (review := review) input depth sourceStart datum prefixLimit renewalLimit reader
    occurrence_commutes := rfl
    initialSupport_heq := HEq.rfl
    initialOpenLedger := initialLedger (review := review) input depth sourceStart datum prefixLimit renewalLimit
    initialOpenLedger_heq := HEq.rfl
    initialLedger_responsibility_commutes := translated_responsibility_is_the_original_row input
      depth (cut input depth sourceStart) depth (cut input depth sourceStart) (originalSupport input depth sourceStart)
    initialLedger_claim_commutes := (translation input depth sourceStart).oldOpenClaim_commutes (originalSupport input depth sourceStart)
    initialLedger_budget_conservative := fun entry =>
      ((translation input depth sourceStart).oldOpenProgressBudget_commutes (originalSupport input depth sourceStart) entry).le
    initialLedgerNoFresh := fun entry => ⟨⟨(initialLedger (review := review) input depth sourceStart datum prefixLimit renewalLimit).backward entry,
      ⟨initial_ledger_has_no_fresh_row (review := review) input depth sourceStart datum prefixLimit renewalLimit entry⟩⟩⟩
    translatedSourceEntryRow := initialRow (review := review) input depth sourceStart datum prefixLimit renewalLimit reader
    firstSuccessor := firstSuccessor (review := review) input depth sourceStart datum prefixLimit renewalLimit reader
    canonical_targetNextVisit_eq := next_is_the_same_generated_successor
      (targetRoot (review := review) input depth sourceStart datum prefixLimit renewalLimit reader)
      (.finite (targetInitial (review := review) input depth sourceStart datum prefixLimit renewalLimit reader))
      (firstSuccessor (review := review) input depth sourceStart datum prefixLimit renewalLimit reader)
    Answer := ResultAt (review := review) input depth sourceStart datum prefixLimit renewalLimit
      ((frame input depth sourceStart).native.root.emitted (frame input depth sourceStart).visit.current)
    answer := reportAt (review := review) input depth sourceStart datum prefixLimit renewalLimit _
    Receipt := fun answer => ULift.{3, 0} (PLift
      ((firstSuccessor (review := review) input depth sourceStart datum prefixLimit renewalLimit reader).targetCurrent =
          bodyNext (review := review) input depth sourceStart datum prefixLimit renewalLimit ∧
        (bodyNext (review := review) input depth sourceStart datum prefixLimit renewalLimit).account =
          Epoch.Finance.Legacy.generated input depth (cut input depth sourceStart) ((frame input depth sourceStart).cursor input).account ∧
        answer = reportAt (review := review) input depth sourceStart datum prefixLimit renewalLimit _))
    receipt := ⟨⟨first_target_is_the_source_body_next (review := review) input depth sourceStart datum prefixLimit renewalLimit reader,
      (the_first_body_keeps_the_actual_drained_account_and_full_inventory (review := review) input depth sourceStart datum prefixLimit renewalLimit).2.1,
      rfl⟩⟩ }

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress.targetAt
