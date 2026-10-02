import H0mework.Foundation.Responsibility.JointSource.Native.Request.Target.Common
import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Restructuring.Inquiry.Source
import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Request.Target
import H0mework.Foundation.Responsibility.JointSource.Native.Receipt

set_option autoImplicit false
universe u

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry

open SourceOperationEffects DebtActivationWorld DebtActivationLedger DebtAdmissionFirstWrite RootInquiryCompletion

noncomputable section

variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)]
  {sort : Sorts} {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : RootInquiryStateAt N V) (query : old.Query)
variable (program : Program old.root.toAuthoritativeRoot.toLedgerRoot)
variable (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort)
  old.root.toAuthoritativeRoot.toLedgerRoot old.visit.current)
variable (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt old.root old.visit registered.input.owner)

def sourceSuccessor (event : ExactTemporalCausalRootEventAt old.root.toAuthoritativeRoot.toLedgerRoot old.visit) :=
  Native.Request.sourceSuccessor old program event

open Native.Request.TargetCommon

def firstSuccessor : SourceNativeLedgerGeneratedSuccessorAt
    ((targetRoot old program registered).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (initialVisit old program registered)).occurrence
    ((targetRoot old program registered).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (initialVisit old program registered)).wholeLedgerWriteBack :=
  (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated?
    ((targetRoot old program registered).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (initialVisit old program registered)).wholeLedgerWriteBack).get (by rfl)

def initialOldRow (entry : OpenResponsibilityAt N
    (old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
      (old.root.emitted old.visit.current))) :
    ((targetRoot old program registered).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (initialVisit old program registered)).GeneratedEntryRowAt
      (oldEntry (law := Idle.law registered.input.environment registered.input.expression)
        (state? := some (initialEvent registered).state) entry) :=
  (((targetRoot old program registered).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
    (initialVisit old program registered)).canonicalGeneratedEntryRow?
      (oldEntry (law := Idle.law registered.input.environment registered.input.expression)
        (state? := some (initialEvent registered).state) entry)).get (by rfl)

def initialBornRow :
    ((targetRoot old program registered).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (initialVisit old program registered)).GeneratedEntryRowAt (mathSource registered (initial old registered)) :=
  (((targetRoot old program registered).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
    (initialVisit old program registered)).canonicalGeneratedEntryRow?
      (mathSource registered (initial old registered))).get (by rfl)


variable (paid : GeneratedStepAt (Idle.law registered.input.environment registered.input.expression)
  (initialEvent registered).state)
variable (action : sourceAction old program registered = .inr paid)

def targetAt (event : ExactTemporalCausalRootEventAt old.root.toAuthoritativeRoot.toLedgerRoot old.visit) :
    SourceNativeDebtAdmissionActualActionTargetAt old.root old.visit event registered.input.owner authority where
  law := Idle.law registered.input.environment registered.input.expression
  sourceState := (initialEvent registered).state
  stepEvent := .ofStep paid.2
  sourceSuccessor := sourceSuccessor old program event
  TargetV := JointV program registered
  targetRoot := targetRoot old program registered
  initialSupport_eq := rfl
  initialOldRow := initialOldRow old program registered
  initialBornRow := initialBornRow old program registered
  firstSuccessor := firstSuccessor old program registered
  firstSupport_eq := by
    have next : (targetCurrent program registered (initial old registered)).2.state = paid.1 := by
      exact (native program registered (initial old registered)).next_state.trans (by
        change mathTarget (initialEvent registered) = paid.1
        unfold mathTarget
        rw [(sourceAction_eq old program registered).symm.trans action])
    have supports := successor_support (sourceSuccessor old program event)
      (program.emit old.visit.current).generated_eq
    exact (congrArg (fun occurrence =>
      (old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf occurrence,
        some (targetCurrent program registered (initial old registered)).2.state))
      (program.emit old.visit.current).target_emitted.symm).trans
      ((congrArg (fun state =>
      (old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (program.emit old.visit.current).targetOccurrence, some state)) next).trans
      (congrArg (fun support => (support, some paid.1)) supports.symm))
  firstDestination_heq := by
    have supports := successor_support (sourceSuccessor old program event)
      (program.emit old.visit.current).generated_eq
    have ledger := successor_ledger (sourceSuccessor old program event)
      (program.emit old.visit.current).generated_eq
    exact (paid_destination program registered (initial old registered) paid ((sourceAction_eq old program registered).symm.trans action)).trans
      (joint_destination supports.symm ledger.symm registered.input.owner paid.2)
  oldProjection := oldProjection old program registered
  oldProjection_injective := oldProjection_injective old program registered
  oldOutcome_heq := oldOutcome_heq old program registered
  canonical_targetNextVisit_eq := by
    apply SourceNativeLivingRootClosure.generatedNextCurrentAt_eq_nativeWriteBranch
    rfl
  Answer := (old.compileInquiry query).AnswerCarrier
  answer := (old.compileInquiry query).answerReadout
  Receipt := fun result => ULift.{u + 3, u} (Sigma fun actual :
    GeneratedStepAt (Idle.law registered.input.environment registered.input.expression) (initialEvent registered).state =>
      PLift (sourceAction old program registered = .inr actual ∧ result = (old.compileInquiry query).answerReadout))
  receipt := ⟨paid, ⟨action, rfl⟩⟩

def birthProgram : SourceNativeDebtAdmissionActualActionProgramAt old.root old.visit registered.input.owner authority where
  targetAt := targetAt old query program registered authority paid action

def generate (event : ExactTemporalCausalRootEventAt old.root.toAuthoritativeRoot.toLedgerRoot old.visit) :
    SourceOperationExecutionDebt.Settlement (initialEvent registered).state ⊕
      SourceNativeDebtAdmissionActualActionTargetAt old.root old.visit event registered.input.owner authority := by
  cases selected : sourceAction old program registered with
  | inl settled => exact .inl settled
  | inr actual => exact .inr (targetAt old query program registered authority actual selected event)

end
end RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
