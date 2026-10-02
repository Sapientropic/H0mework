import H0mework.Foundation.Responsibility.JointSource.Native.Request.Target.Common
import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Request.Source
import H0mework.Foundation.Responsibility.JointSource.Native.Receipt

set_option autoImplicit false
universe u

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Native.Request

open SourceOperationEffects DebtActivationWorld DebtActivationLedger DebtAdmissionFirstWrite RootInquiryCompletion

noncomputable section

variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)]
  {sort : Sorts} {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : RootInquiryStateAt N V) (query : old.Query)
variable (program : Program old.root.toAuthoritativeRoot.toLedgerRoot)
variable (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort)
  old.root.toAuthoritativeRoot.toLedgerRoot old.visit.current)
variable (scope : IdentityScope program)
variable (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt old.root old.visit registered.input.owner)

def initial : Current registered := ⟨old.visit.current, initialEvent registered⟩

def sourceSuccessor (event : ExactTemporalCausalRootEventAt old.root.toAuthoritativeRoot.toLedgerRoot old.visit) :
    SourceNativeLedgerGeneratedSuccessorAt event.occurrence event.wholeLedgerWriteBack :=
  (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated? event.wholeLedgerWriteBack).get (by
    change (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated?
      (old.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt old.visit.current)).isSome = true
    rw [(program.emit old.visit.current).generated_eq]
    rfl)

open Native.Request.TargetCommon

def initialVisit := SourceNativeTemporalVisitAt.finite
  (targetRoot old program registered scope).toAuthoritativeRoot.toRoot.initialVisit

def firstSuccessor : SourceNativeLedgerGeneratedSuccessorAt
    ((targetRoot old program registered scope).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (initialVisit old program registered scope)).occurrence
    ((targetRoot old program registered scope).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (initialVisit old program registered scope)).wholeLedgerWriteBack :=
  (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated?
    ((targetRoot old program registered scope).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (initialVisit old program registered scope)).wholeLedgerWriteBack).get (by rfl)

def initialOldRow (entry : OpenResponsibilityAt N
    (old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
      (old.root.emitted old.visit.current))) :
    ((targetRoot old program registered scope).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (initialVisit old program registered scope)).GeneratedEntryRowAt
      (oldEntry (law := Idle.law registered.input.environment registered.input.expression)
        (state? := some (initialEvent registered).state) entry) :=
  (((targetRoot old program registered scope).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
    (initialVisit old program registered scope)).canonicalGeneratedEntryRow?
      (oldEntry (law := Idle.law registered.input.environment registered.input.expression)
        (state? := some (initialEvent registered).state) entry)).get (by rfl)

def initialBornRow :
    ((targetRoot old program registered scope).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (initialVisit old program registered scope)).GeneratedEntryRowAt (mathSource registered (initial old registered)) :=
  (((targetRoot old program registered scope).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
    (initialVisit old program registered scope)).canonicalGeneratedEntryRow?
      (mathSource registered (initial old registered))).get (by rfl)

def oldProjection (projection : old.root.toAuthoritativeRoot.source.projectionLaw.Projection) :
    (targetRoot old program registered scope).toAuthoritativeRoot.source.projectionLaw.Projection :=
  (oldInstallation old program registered scope).embed (.inl projection)

theorem oldProjection_injective : Function.Injective (oldProjection old program registered scope) := by
  intro first second same
  exact Sum.inl.inj ((oldInstallation old program registered scope).embed_injective same)

theorem oldOutcome_heq (projection : old.root.toAuthoritativeRoot.source.projectionLaw.Projection) :
    HEq ((targetRoot old program registered scope).toAuthoritativeRoot.source.projectionLaw.outcomeAt
      (oldProjection old program registered scope projection) (emitted program registered (initial old registered)))
      (old.root.toAuthoritativeRoot.source.projectionLaw.outcomeAt projection (old.root.emitted old.visit.current)) :=
  ((oldInstallation old program registered scope).outcome_heq _ (.inl projection)).trans
    (original_projection_outcome program registered old.root.toAuthoritativeRoot.source.projectionLaw _ projection)

variable (paid : GeneratedStepAt (Idle.law registered.input.environment registered.input.expression)
  (initialEvent registered).state)
variable (action : mathAction (initialEvent registered) = .inr paid)

def targetAt (event : ExactTemporalCausalRootEventAt old.root.toAuthoritativeRoot.toLedgerRoot old.visit) :
    SourceNativeDebtAdmissionActualActionTargetAt old.root old.visit event registered.input.owner authority where
  law := Idle.law registered.input.environment registered.input.expression
  sourceState := (initialEvent registered).state
  stepEvent := .ofStep paid.2
  sourceSuccessor := sourceSuccessor old program event
  TargetV := NewV old program registered
  targetRoot := targetRoot old program registered scope
  initialSupport_eq := rfl
  initialOldRow := initialOldRow old program registered scope
  initialBornRow := initialBornRow old program registered scope
  firstSuccessor := firstSuccessor old program registered scope
  firstSupport_eq := by
    have next : (targetCurrent program registered (initial old registered)).2.state = paid.1 := by
      exact (native program registered (initial old registered)).next_state.trans (by
        change mathTarget (initialEvent registered) = paid.1
        unfold mathTarget
        rw [action])
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
    exact (paid_destination program registered (initial old registered) paid action).trans
      (joint_destination supports.symm ledger.symm registered.input.owner paid.2)
  oldProjection := oldProjection old program registered scope
  oldProjection_injective := oldProjection_injective old program registered scope
  oldOutcome_heq := oldOutcome_heq old program registered scope
  canonical_targetNextVisit_eq := by
    apply SourceNativeLivingRootClosure.generatedNextCurrentAt_eq_nativeWriteBranch
    rfl
  Answer := (old.compileInquiry query).AnswerCarrier
  answer := (old.compileInquiry query).answerReadout
  Receipt := fun result => ULift.{u + 3, u} (Sigma fun actual :
    GeneratedStepAt (Idle.law registered.input.environment registered.input.expression) (initialEvent registered).state =>
      PLift (mathAction (initialEvent registered) = .inr actual ∧ result = (old.compileInquiry query).answerReadout))
  receipt := ⟨paid, ⟨action, rfl⟩⟩

def birthProgram : SourceNativeDebtAdmissionActualActionProgramAt old.root old.visit registered.input.owner authority where
  targetAt := targetAt old query program registered scope authority paid action

def generate (event : ExactTemporalCausalRootEventAt old.root.toAuthoritativeRoot.toLedgerRoot old.visit) :
    SourceOperationExecutionDebt.Settlement (initialEvent registered).state ⊕
      SourceNativeDebtAdmissionActualActionTargetAt old.root old.visit event registered.input.owner authority := by
  cases selected : mathAction (initialEvent registered) with
  | inl settled => exact .inl settled
  | inr actual => exact .inr (targetAt old query program registered scope authority actual selected event)

end
end RootGeneratedDebtActivationJointSource.Native.Request
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
