import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Successor.Inquiry.Math
import H0mework.Foundation.Responsibility.JointSource.Native.Request.Target.Common

/-! The actual original packet and registered Step generate the debt-admission
first write. Its complete patch may retain a transported remainder. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Successor.Inquiry
open SourceOperationEffects DebtActivationWorld DebtActivationLedger RootInquiryCompletion CompilerFromPacketSourceLaw
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : RootInquiryStateAt N V) (query : old.Query)
variable (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort)
  old.root.toAuthoritativeRoot.toLedgerRoot old.visit.current)
variable (packetAt : (current : V.Current) → Packet old.root.toAuthoritativeRoot.toLedgerRoot current)
variable (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt old.root old.visit registered.input.owner)

def sourceSuccessor (event : ExactTemporalCausalRootEventAt old.root.toAuthoritativeRoot.toLedgerRoot old.visit) :
    SourceNativeLedgerGeneratedSuccessorAt event.occurrence event.wholeLedgerWriteBack :=
  (packetAt old.visit.current).successor

abbrev initialVisit := temporalVisit old registered packetAt 0

def initialRawFace : SourceNativeRootSemanticFaceAt (targetRoot old registered packetAt) (initialVisit old registered packetAt) where
  projection := (Assembly.rawInstallation old registered packetAt).embed PUnit.unit
  active := PUnit.unit
  classifier_eq := rfl

def sourceAction : SourceOperationExecutionDebt.Settlement (initialEvent registered).state ⊕
    GeneratedStepAt (Idle.law registered.input.environment registered.input.expression) (initialEvent registered).state :=
  SourceOperationExecutionDebt.generate (initialRawFace old registered packetAt).rootRead.environment
    (initialRawFace old registered packetAt).rootRead.expression (initialEvent registered).state

theorem sourceAction_eq : sourceAction old registered packetAt = mathAction (initialEvent registered) := rfl

def firstSuccessor : SourceNativeLedgerGeneratedSuccessorAt
    ((targetRoot old registered packetAt).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (initialVisit old registered packetAt)).occurrence
    ((targetRoot old registered packetAt).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (initialVisit old registered packetAt)).wholeLedgerWriteBack :=
  (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated?
    ((targetRoot old registered packetAt).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (initialVisit old registered packetAt)).wholeLedgerWriteBack).get (by rfl)

def initialOldRow (entry : OpenResponsibilityAt N
    (old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
      (old.root.emitted old.visit.current))) :
    ((targetRoot old registered packetAt).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (initialVisit old registered packetAt)).GeneratedEntryRowAt
      (oldEntry (law := scope registered) (state? := some (initialEvent registered).state) entry) :=
  (((targetRoot old registered packetAt).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
    (initialVisit old registered packetAt)).canonicalGeneratedEntryRow?
      (oldEntry (law := scope registered) (state? := some (initialEvent registered).state) entry)).get (by rfl)

def initialBornRow :
    ((targetRoot old registered packetAt).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (initialVisit old registered packetAt)).GeneratedEntryRowAt
      (CompilerFromPacketSourceLaw.mathEntry registered (initial old registered)) :=
  (((targetRoot old registered packetAt).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
    (initialVisit old registered packetAt)).canonicalGeneratedEntryRow?
      (CompilerFromPacketSourceLaw.mathEntry registered (initial old registered))).get (by rfl)

def oldProjection (projection : old.root.toAuthoritativeRoot.source.projectionLaw.Projection) :
    (targetRoot old registered packetAt).toAuthoritativeRoot.source.projectionLaw.Projection :=
  (Assembly.oldInstallation old registered packetAt).embed (.inl projection)

theorem oldProjection_injective : Function.Injective (oldProjection old registered packetAt) := by
  intro first second same
  exact Sum.inl.inj ((Assembly.oldInstallation old registered packetAt).embed_injective same)

theorem oldOutcome_heq (projection : old.root.toAuthoritativeRoot.source.projectionLaw.Projection) :
    HEq ((targetRoot old registered packetAt).toAuthoritativeRoot.source.projectionLaw.outcomeAt
      (oldProjection old registered packetAt projection) (emitted registered packetAt (initial old registered)))
      (old.root.toAuthoritativeRoot.source.projectionLaw.outcomeAt projection (old.root.emitted old.visit.current)) :=
  ((Assembly.oldInstallation old registered packetAt).outcome_heq _ (.inl projection)).trans
    (Restructuring.projection_original old.root.toAuthoritativeRoot registered packetAt _ projection)

private theorem destination_heq {W : WorldRelationNetwork.{u}}
    {source leftTarget rightTarget : W.Support}
    {left : LedgerWriteEvolutionAt W ⟨source⟩ ⟨leftTarget⟩}
    {right : LedgerWriteEvolutionAt W ⟨source⟩ ⟨rightTarget⟩}
    (supports : leftTarget = rightTarget) (same : HEq left right) :
    HEq left.destination right.destination := by
  cases supports
  cases eq_of_heq same
  rfl

private theorem original_fold_heq {L : SourceNativeLedgerRootClosure N V} {current : V.Current}
    (packet : Packet L current) : HEq (originalFold packet) packet.ledgerEvolution := by
  unfold originalFold
  exact eqRec_heq_iff.mpr HEq.rfl

variable (paid : GeneratedStepAt (scope registered) (initialEvent registered).state)
variable (action : sourceAction old registered packetAt = .inr paid)

def targetAt (event : ExactTemporalCausalRootEventAt old.root.toAuthoritativeRoot.toLedgerRoot old.visit) :
    SourceNativeDebtAdmissionActualActionTargetAt old.root old.visit event registered.input.owner authority where
  law := scope registered
  sourceState := (initialEvent registered).state
  stepEvent := .ofStep paid.2
  sourceSuccessor := sourceSuccessor old packetAt event
  TargetV := JointV registered packetAt
  targetRoot := targetRoot old registered packetAt
  initialSupport_eq := rfl
  initialOldRow := initialOldRow old registered packetAt
  initialBornRow := initialBornRow old registered packetAt
  firstSuccessor := firstSuccessor old registered packetAt
  firstSupport_eq := by
    have next : mathTarget (initialEvent registered) = paid.1 := by
      unfold mathTarget
      rw [(sourceAction_eq old registered packetAt).symm.trans action]
    exact (congrArg (fun occurrence =>
      (old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf occurrence,
        some (mathTarget (initialEvent registered)))) (packetAt old.visit.current).target_emitted.symm).trans
      (congrArg (fun state =>
        (old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
          (packetAt old.visit.current).targetOccurrence, some state)) next)
  firstDestination_heq := by
    have actualAction := (sourceAction_eq old registered packetAt).symm.trans action
    have next : mathTarget (initialEvent registered) = paid.1 := by
      unfold mathTarget
      rw [actualAction]
    have folded := congrArg LedgerWriteEvolutionAt.destination (patch_fold registered packetAt (initial old registered))
    have paidDestination := destination_heq
      (congrArg (fun state => (targetSupport (packetAt old.visit.current), some state)) next)
      (join_whole_paid (packetAt old.visit.current) (initialEvent registered) paid actualAction)
    have originalDestination := Native.Request.TargetCommon.joint_destination
      (congrArg (old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf)
        (packetAt old.visit.current).target_emitted.symm)
      (original_fold_heq (packetAt old.visit.current)) registered.input.owner paid.2
    exact (heq_of_eq folded).trans (paidDestination.trans originalDestination)
  oldProjection := oldProjection old registered packetAt
  oldProjection_injective := oldProjection_injective old registered packetAt
  oldOutcome_heq := oldOutcome_heq old registered packetAt
  canonical_targetNextVisit_eq := by
    apply SourceNativeLivingRootClosure.generatedNextCurrentAt_eq_nativeWriteBranch
    rfl
  Answer := (old.compileInquiry query).AnswerCarrier
  answer := (old.compileInquiry query).answerReadout
  Receipt := fun result => ULift.{u + 3, u} (Sigma fun actual :
    GeneratedStepAt (scope registered) (initialEvent registered).state =>
      PLift (sourceAction old registered packetAt = .inr actual ∧ result = (old.compileInquiry query).answerReadout))
  receipt := ⟨paid, ⟨action, rfl⟩⟩

def birthProgram : SourceNativeDebtAdmissionActualActionProgramAt old.root old.visit registered.input.owner authority where
  targetAt := targetAt old query registered packetAt authority paid action

def generate (event : ExactTemporalCausalRootEventAt old.root.toAuthoritativeRoot.toLedgerRoot old.visit) :
    SourceOperationExecutionDebt.Settlement (initialEvent registered).state ⊕
      SourceNativeDebtAdmissionActualActionTargetAt old.root old.visit event registered.input.owner authority := by
  cases selected : sourceAction old registered packetAt with
  | inl settled => exact .inl settled
  | inr actual => exact .inr (targetAt old query registered packetAt authority actual selected event)

end RootGeneratedDebtActivationJointSource.Successor.Inquiry
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
