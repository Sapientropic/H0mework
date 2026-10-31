import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Reentry.Inquiry
import H0mework.Versions.R2.Foundation.Source.SequentialAction

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Reentry

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion DebtActivationWorld
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)} {oldN : WorldRelationNetwork}
  (claim : Responsibility.Family.Claim mechanism past nature response)
  (frame : Frame (oldN := oldN) claim) (word : RawEvent Party Good Port Technology Instrument)

local notation "N" => ExtendedNetwork oldN (Responsibility.Family.activationLaw claim)
local notation "F" => flow claim frame word
local notation "newRoot" => inquiryRoot claim frame word
local notation "stepResult" => Compiler.successor F false

def occurrencePresentation : ConstructivePresentation
    (frame.root.toAuthoritativeRoot.toRoot.actual.OccurrenceAt frame.visit.current)
    ((newRoot).toAuthoritativeRoot.toRoot.actual.OccurrenceAt false) where
  forward := fun _ => (newRoot).emitted false
  backward := fun _ => frame.root.emitted frame.visit.current
  backward_forward := fun occurrence => (frame.occurrence_eq _ occurrence).symm
  forward_backward := fun occurrence => (Compiler.occurrence_eq_emitted F occurrence).symm

def targetAt (event : ExactTemporalCausalRootEventAt frame.root.toAuthoritativeRoot.toLedgerRoot frame.visit) :
    SourceNativeSequentialActualActionTargetAt frame.root frame.visit event frame.row frame.authority := by
  rw [event.eq_generated]
  exact {
    TargetN := N
    translation := Financial.Installation.Ingress.identityTranslation N
    TargetV := V claim frame word
    targetRoot := newRoot
    targetTheory := TheoryState.rootSemantic N
    lawSurface_heq := HEq.rfl
    targetTheory_rootSemantic := ⟨id,fun _ => rfl⟩
    occurrencePresentation := occurrencePresentation claim frame word
    occurrence_commutes := rfl
    initialSupport_heq := HEq.rfl
    initialOpenLedger := (Financial.Installation.Ingress.identityTranslation N).oldOpenLedger (Frame.support claim frame)
    initialOpenLedger_heq := HEq.rfl
    initialLedger_responsibility_commutes := fun _ => rfl
    initialLedger_claim_commutes := fun _ => rfl
    initialLedger_budget_conservative := fun _ => Nat.le_refl _
    initialLedgerNoFresh := fun entry => ⟨⟨entry,⟨rfl⟩⟩⟩
    translatedSourceEntryRow := Compiler.generatedRow F (Compiler.initialVisit F) frame.row
    firstSuccessor := stepResult
    canonical_targetNextVisit_eq :=
      Abolition.Root.Registered.Macro.Ingress.next_is_the_same_generated_successor (newRoot) (Compiler.initialVisit F) stepResult
    Answer := Responsibility.Family.State claim
    answer := Frame.updated claim frame word
    Receipt := fun answer => ULift.{3,0} (PLift
      (answer = Frame.updated claim frame word ∧
        (∀ key,answer.remaining key ≤ (Frame.state claim frame).remaining key) ∧
        answer.raw.claims = (Frame.state claim frame).raw.claims)) ×
      ULift.{3,0} (Responsibility.Family.MaterialVerdict claim (Frame.state claim frame) frame.actualLaw word) ×
      ULift.{3,0} (Responsibility.Family.NeedDisposition frame.actualLaw (Frame.state claim frame).raw
        (Responsibility.Family.State.attempt claim (Frame.state claim frame) frame.actualLaw word).actualWord frame.members)
    receipt := ⟨⟨⟨rfl,Responsibility.Family.State.actual_advance_never_refills_any_original_cell _ _ _ _,
        Responsibility.Family.State.actual_advance_retains_every_original_financial_claim _ _ _ _⟩⟩,
      ⟨Responsibility.Family.adjudicate claim (Frame.state claim frame) frame.actualLaw word⟩,
      ⟨Responsibility.Family.inspectActualNeeds claim (Frame.state claim frame) frame.actualLaw word frame.members⟩⟩ }

def program : SourceNativeSequentialActualActionProgramAt frame.root frame.visit frame.row frame.authority where
  targetAt := targetAt claim frame word

def generated := (program claim frame word).generate (frame.root.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt frame.visit)

private theorem canonicalKey_target_eq {network : WorldRelationNetwork} {voc : ConstructiveRoot.Vocabulary}
    (root : SourceNativeLedgerRootClosure network voc) {current leftTarget rightTarget : voc.Current}
    (same : leftTarget = rightTarget)
    (left : (root.toRoot.evolutionAt current).nextCurrent? = some leftTarget)
    (right : (root.toRoot.evolutionAt current).nextCurrent? = some rightTarget)
    (entry : OpenResponsibilityAt network (root.source.source.toRootSource.account.supportOf (root.emitted current))) :
    (root.canonicalTargetEntryAtNext left entry).1 = (root.canonicalTargetEntryAtNext right entry).1 := by
  cases same
  rfl

theorem target_row_keeps_the_same_original_key :
    (generated claim frame word).target.targetEntry.1 = .inr (Responsibility.Family.activationLaw claim).debtId := by
  change ((newRoot).toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext (stepResult).next_eq frame.row).1 = _
  refine (canonicalKey_target_eq (newRoot).toAuthoritativeRoot.toLedgerRoot
    (Compiler.successor_current F false) (stepResult).next_eq (Compiler.nextEq F false) frame.row).trans ?_
  apply Compiler.canonical_key_of_flow F false frame.row _
  exact ((actual_keeps_every_original_responsibility_key claim frame word).1 frame.row).trans frame.rowKey

/-- The returned context reads its new actual native row. Calling reentry again
uses that row's remaining matrix and cursor, never the original atCursor state. -/
def nextFrame : Frame (oldN := oldN) claim where
  V := V claim frame word
  root := newRoot
  visit := (generated claim frame word).target.targetVisit
  row := (generated claim frame word).target.targetEntry
  rowKey := target_row_keeps_the_same_original_key claim frame word
  authority := (generated claim frame word).target.targetAuthority
  finite := entries_finite claim frame word (stepResult).targetCurrent
  occurrence_eq := fun _ occurrence => Compiler.occurrence_eq_emitted F occurrence
  open_fibres := frame.open_fibres
  basis := frame.basis
  actualLaw := frame.actualLaw
  members := frame.members
  contextFace := {
    projection := inquiryOldProjection claim frame word frame.contextFace.projection
    active := frame.contextFace.active
    classifier_eq := frame.contextFace.classifier_eq }
  context_heq := frame.context_heq

theorem next_frame_reads_the_actual_updated_state :
    Frame.state claim (nextFrame claim frame word) = Frame.updated claim frame word := by
  have sameSupport : Frame.support claim (nextFrame claim frame word) =
      ((Frame.support claim frame).1,some (Frame.updated claim frame word)) := by
    change support claim frame word (stepResult).targetCurrent = _
    rw [Compiler.successor_current F false]
    rfl
  have old := (Option.some_get (Frame.active claim (nextFrame claim frame word)))
  exact Option.some.inj (old.trans (congrArg Prod.snd sameSupport))

theorem every_reentry_uses_the_same_world : (generated claim frame word).target.TargetN = N := rfl

theorem actual_next_is_the_same_full_root_successor :
    (generated claim frame word).target.targetAnswerAndNext.nextCurrent =
      ⟨V claim frame word,(newRoot).toAuthoritativeRoot,(nextFrame claim frame word).visit⟩ :=
  (generated claim frame word).target.targetAnswerAndNext_next_eq

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Reentry
