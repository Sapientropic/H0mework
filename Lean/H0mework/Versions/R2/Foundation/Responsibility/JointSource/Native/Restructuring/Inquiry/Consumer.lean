import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Restructuring.Inquiry.Birth
import H0mework.Versions.R2.Foundation.Runtime.Activation

/-! The original finite-visit runtime mechanism consumes this fixed general
root. Its causal depth supplies registry injection independently of changing
split/merge inventory sizes; the sealed runtime and tick remain unchanged. -/

set_option autoImplicit false
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry
open RootInquiryCompletion SourceOperationEffects DebtActivationWorld DebtActivationLedger
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : RootInquiryStateAt N V)
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable (program : Program old.root.toAuthoritativeRoot.toLedgerRoot)
variable (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort) old.root.toAuthoritativeRoot.toLedgerRoot old.visit.current)

def finiteVisit : Nat → RootVisit (ledgerRoot program registered).toRoot
  | 0 => (ledgerRoot program registered).toRoot.initialVisit
  | depth + 1 => (finiteVisit depth).next rfl

def temporalVisit (depth : Nat) : SourceNativeTemporalVisitAt (ledgerRoot program registered) :=
  .finite (finiteVisit old program registered depth)

private def temporalDepth (current : SourceNativeLivingRootCurrentAt (World registered)) : Option Nat :=
  match current.visit.history with
  | .finite history => some (ProductiveFiniteRootHistoryAt.causalDepth history)
  | .postCofinal _ => none

private theorem visit_depth (depth : Nat) :
    temporalDepth old registered ⟨JointV program registered, targetRoot old program registered,
      temporalVisit old program registered depth⟩ = some depth := by
  induction depth with
  | zero => rfl
  | succ depth prior =>
      change some (ProductiveFiniteRootHistoryAt.causalDepth
        (finiteVisit old program registered depth).history + 1) = some (depth + 1)
      have oldDepth : ProductiveFiniteRootHistoryAt.causalDepth
          (finiteVisit old program registered depth).history = depth := Option.some.inj prior
      exact congrArg some (congrArg (fun count => count + 1) oldDepth)

/-- The fixed root supplies the original process registry and its native next.
This is the existing finite-visit mechanism, with no branch or scheduler field. -/
def process : SourceNativeLivingRootProcess (World registered) where
  State := ULift.{u, 0} Nat
  stateAt := fun depth => ⟨JointV program registered, targetRoot old program registered,
    temporalVisit old program registered depth.down⟩
  stateAt_injective := by
    intro first second same
    have depths := congrArg (temporalDepth old registered) same
    rw [visit_depth old program registered first.down, visit_depth old program registered second.down] at depths
    have values : first.down = second.down := Option.some.inj depths
    cases first
    cases second
    cases values
    rfl
  initial := ⟨0⟩
  successorAt := fun depth => ⟨⟨depth.down + 1⟩, by rfl, by rfl⟩

abbrev Runtime := LivingRuntimeState (process old program registered)

def initialRuntime : Runtime old program registered := LivingRuntimeState.initial (process old program registered)

def runtimeCurrent (runtime : Runtime old program registered) : Current registered :=
  (finiteVisit old program registered runtime.state.down).current

def facade : SourceNativeLivingRuntimeFacade (World registered) where
  process := process old program registered
  FaceAt := fun runtime => runtime.current.root.toAuthoritativeRoot.source.projectionLaw.Projection
  componentAt := fun runtime _ => runtime.current.root.toAuthoritativeRoot.source.projectionLaw
  installationAt := fun _ _ => .refl _
  projectionAt := fun _ face => face

theorem tick_ledger (runtime : Runtime old program registered) :
    HEq runtime.tick.generated.wholeLedgerWriteBack
      ((ledgerCompiler program registered).compile (emitted program registered (runtimeCurrent old program registered runtime))) :=
  HEq.rfl

theorem tick_patch (runtime : Runtime old program registered) :
    HEq runtime.tick.generated.currentPatch
      ((ledgerCompiler program registered).compilePatch (emitted program registered (runtimeCurrent old program registered runtime))) :=
  HEq.rfl

def tickCertificate (runtime : Runtime old program registered) :
    ExactLedgerRestructuringCertificationAt (Native.Restructuring.law old.root.toAuthoritativeRoot program registered)
      (emitted program registered (runtimeCurrent old program registered runtime))
      (patch program registered (runtimeCurrent old program registered runtime)).toLedgerWriteEvolution :=
  runtime.current.root.toAuthoritativeRoot.source.restructuringSource.compiler.certifyRestructuring
    runtime.tick.generated.occurrence

theorem tick_certificate (runtime : Runtime old program registered) : tickCertificate old program registered runtime =
    Native.Restructuring.actualCertificate old.root.toAuthoritativeRoot program registered (runtimeCurrent old program registered runtime) := rfl

def tickSplitConsumer (runtime : Runtime old program registered)
    (left right : OpenResponsibilityAt (World registered) (supportAt registered (targetCurrent program registered (runtimeCurrent old program registered runtime))))
    (same : ((patch program registered (runtimeCurrent old program registered runtime)).toLedgerWriteEvolution.origin left).1 =
      ((patch program registered (runtimeCurrent old program registered runtime)).toLedgerWriteEvolution.origin right).1) :
    PLift (left = right) ⊕
      (Σ coverage : SourceNativeSplitCoverageAt (Native.Restructuring.law old.root.toAuthoritativeRoot program registered) (emitted program registered (runtimeCurrent old program registered runtime))
        (patch program registered (runtimeCurrent old program registered runtime)).toLedgerWriteEvolution left right same,
        DescendantFamily (Native.Restructuring.vocabulary old.root.toAuthoritativeRoot registered) coverage.receipt.sourceEvent
          ((Native.Restructuring.law old.root.toAuthoritativeRoot program registered).obligationAt (emitted program registered (runtimeCurrent old program registered runtime))
            ((patch program registered (runtimeCurrent old program registered runtime)).toLedgerWriteEvolution.origin left).1) coverage.receipt.children) :=
  match (tickCertificate old program registered runtime).split left right same with
  | .identity equality => .inl ⟨equality⟩
  | .split coverage => .inr ⟨coverage, coverage.descendantFamily⟩

def tickMergeConsumer (runtime : Runtime old program registered)
    (left right : OpenResponsibilityAt (World registered) (supportAt registered (runtimeCurrent old program registered runtime)))
    (same : ((patch program registered (runtimeCurrent old program registered runtime)).toLedgerWriteEvolution.destination left).1 =
      ((patch program registered (runtimeCurrent old program registered runtime)).toLedgerWriteEvolution.destination right).1) :
    PLift (left = right) ⊕
      (Σ coverage : SourceNativeMergeCoverageAt (Native.Restructuring.law old.root.toAuthoritativeRoot program registered) (emitted program registered (runtimeCurrent old program registered runtime))
        (patch program registered (runtimeCurrent old program registered runtime)).toLedgerWriteEvolution left right same,
        (parent : (Native.Restructuring.vocabulary old.root.toAuthoritativeRoot registered).Obligation) → parent ∈ coverage.receipt.parents →
          (Native.Restructuring.vocabulary old.root.toAuthoritativeRoot registered).LocalDischargePreservedAt coverage.receipt.sourceEvent
            parent.content coverage.receipt.target.content) :=
  match (tickCertificate old program registered runtime).merge left right same with
  | .identity equality => .inl ⟨equality⟩
  | .merge coverage => .inr ⟨coverage, fun _ member => coverage.receipt.every_parent_retains_localDischarge member⟩

theorem tick_next (runtime : Runtime old program registered) :
    runtimeCurrent old program registered runtime.tick.next =
      targetCurrent program registered (runtimeCurrent old program registered runtime) := rfl

theorem tick_math (runtime : Runtime old program registered) :
    (runtimeCurrent old program registered runtime.tick.next).2.state =
      mathTarget (runtimeCurrent old program registered runtime).2 :=
  (native program registered (runtimeCurrent old program registered runtime)).next_state

def tickSuccessor (runtime : Runtime old program registered) :
    SourceNativeLedgerGeneratedSuccessorAt runtime.tick.generated.occurrence runtime.tick.generated.wholeLedgerWriteBack :=
  (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated? runtime.tick.generated.wholeLedgerWriteBack).get (by rfl)

variable (runtime : Runtime old program registered)
variable (paid : GeneratedStepAt (Native.Restructuring.MathLaw old.root.toAuthoritativeRoot registered) (runtimeCurrent old program registered runtime).2.state)
variable (action : mathAction (runtimeCurrent old program registered runtime).2 = .inr paid)
include action in
theorem tick_full_paid_destination :
    HEq (tickSuccessor old program registered runtime).ledgerEvolution.destination
      (jointStepLedgerEvolution (law := Native.Restructuring.MathLaw old.root.toAuthoritativeRoot registered)
        (native program registered (runtimeCurrent old program registered runtime)).baseLedger
        (runtimeCurrent old program registered runtime).2.owner paid.2).destination :=
  Native.Restructuring.full_paid_destination old.root.toAuthoritativeRoot program registered (runtimeCurrent old program registered runtime) paid action

theorem tick_original_projection (projection : old.root.toAuthoritativeRoot.source.projectionLaw.Projection) :
    HEq (runtime.tick.generated.projectionOutcome (oldProjection old program registered projection))
      (old.root.toAuthoritativeRoot.source.projectionLaw.outcomeAt projection
        (old.root.emitted (runtimeCurrent old program registered runtime).1)) :=
  ((Assembly.oldInstallation old program registered).outcome_heq _ (.inl projection)).trans
    (Native.original_projection_outcome program registered old.root.toAuthoritativeRoot.source.projectionLaw _ projection)

theorem facade_tick_factorizes (face : (facade old program registered).FaceAt runtime) :
    HEq ((facade old program registered).readoutAt runtime face)
      (runtime.tick.generated.projectionOutcome face) ∧
      runtime.tick.nextCurrent = (process old program registered).stateAt ((process old program registered).successor runtime.state) := by
  have actual := (facade old program registered).readoutAt_factorizes runtime face
  exact ⟨actual.2.2.2.1, actual.2.2.2.2⟩

noncomputable section

variable (query : old.Query)
variable (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt old.root old.visit registered.input.owner)
variable (firstPaid : GeneratedStepAt (Idle.law registered.input.environment registered.input.expression)
  (initialEvent registered).state)
variable (firstAction : sourceAction old program registered = .inr firstPaid)
variable (event : ExactTemporalCausalRootEventAt old.root.toAuthoritativeRoot.toLedgerRoot old.visit)

theorem generated_target_root :
    ((birthProgram old query program registered authority firstPaid firstAction).generate event).target.targetRoot =
      (initialRuntime old program registered).current.root := rfl

theorem generated_born_entry :
    ((birthProgram old query program registered authority firstPaid firstAction).generate event).target.bornEntry =
      mathSource registered (initial old registered) := rfl

def generated_born_authority (query : old.Query)
    (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt old.root old.visit registered.input.owner)
    (firstPaid : GeneratedStepAt (Idle.law registered.input.environment registered.input.expression)
      (initialEvent registered).state)
    (firstAction : sourceAction old program registered = .inr firstPaid)
    (event : ExactTemporalCausalRootEventAt old.root.toAuthoritativeRoot.toLedgerRoot old.visit) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt
    (initialRuntime old program registered).current.root
    (initialVisit old program registered) (mathSource registered (initial old registered)) :=
  ((birthProgram old query program registered authority firstPaid firstAction).generate event).target.bornAuthority

theorem generated_first_successor :
    ((birthProgram old query program registered authority firstPaid firstAction).generate event).target.firstSuccessor =
      tickSuccessor old program registered (initialRuntime old program registered) := rfl

include query authority firstAction in
theorem generated_first_destination :
    HEq (tickSuccessor old program registered (initialRuntime old program registered)).ledgerEvolution.destination
      (jointStepLedgerEvolution (sourceSuccessor old program event).ledgerEvolution
        registered.input.owner firstPaid.2).destination :=
  ((birthProgram old query program registered authority firstPaid firstAction).generate event).target.firstDestination_heq

theorem generated_first_next :
    ((birthProgram old query program registered authority firstPaid firstAction).generate event).target.targetAnswerAndNext.nextCurrent =
      ⟨JointV program registered, (targetAuthority old program registered),
        temporalVisit old program registered 1⟩ :=
  ((birthProgram old query program registered authority firstPaid firstAction).generate event).target.targetAnswerAndNext_next_eq

end

end RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
