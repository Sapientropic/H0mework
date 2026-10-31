import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Compiler.SourceGeneratedContributionCapacityPostSettlementRenewalCompiler
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Gate.Birth.Celebration.Bearer.Producer.SourceGeneratedContributionCapacityBirthBearerExit
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Gate.Birth.Celebration.Bearer.Response.Producer.SourceGeneratedContributionCapacityBearerExerciseNoncaptureResponse
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Gate.Birth.Celebration.Bearer.Continuation.Producer.SourceGeneratedContributionCapacityBearerRoleIndependentContinuation
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Gate.Birth.Celebration.Channel.Carrier.Producer.SourceGeneratedContributionCapacityEssentialAccessChannel
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.Universal.Source.SourceGeneratedPostSettlementSocietyFaceTrace

/-!
# Post-settlement renewal root

The unique empty-ledger support remains nonterminal.  This root separates the
vacuous whole-ledger write from the fresh actual-service renewal projection,
retains the root-semantic law surface, and emits a new current-indexed
occurrence at every successor.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open UniversalRootGrammar
open ConstructiveRoot.RootInquiryCompletion
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityJointSettlementWorld
open M14SourceGeneratedContributionCapacityPostSettlementRenewalCompiler
open M14SourceGeneratedContributionCapacityBirthBearerExit
open M14SourceGeneratedContributionCapacityBearerExerciseNoncaptureResponse
open M14SourceGeneratedContributionCapacityBearerLeaveExecution
open M14SourceGeneratedContributionCapacityBearerRoleIndependentContinuation
open M14SourceGeneratedContributionCapacityEssentialAccessChannel
open M14SourceGeneratedPostSettlementSocietyFaceTrace
open M14UBIPeriodicActualServiceCapacity

inductive ContributionCapacityPostSettlementRenewalProjection
  | ledger
  | renewal
  | birthBearerExit
  | bearerExerciseResponse
  | bearerLeaveExecution
  | bearerRoleIndependentContinuation
  | essentialAccessChannel (channel : EssentialAccessChannel)
  | installedSocietyGrammar

def contributionCapacityPostSettlementRenewalTheory
    (oldVisit : OldVisit) : TheoryState (JointSettlementNAt oldVisit) :=
  TheoryState.rootSemantic (JointSettlementNAt oldVisit)

abbrev contributionCapacityPostSettlementRenewalProjectionLaw
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    SourceNativeProjectionLaw
      (contributionCapacityPostSettlementRenewalRestructuringSource oldVisit
        sourceIndex).toLedgerSource where
  Projection := ContributionCapacityPostSettlementRenewalProjection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {current} occurrence _ =>
    match projection with
    | .ledger => postSettlementSocietyFacePayloadAt oldVisit sourceIndex
        occurrence .ledger
    | .renewal => postSettlementSocietyFacePayloadAt oldVisit sourceIndex
        occurrence .renewal
    | .birthBearerExit => postSettlementSocietyFacePayloadAt oldVisit
        sourceIndex occurrence .birthBearerExit
    | .bearerExerciseResponse => postSettlementSocietyFacePayloadAt oldVisit
        sourceIndex occurrence .bearerExerciseResponse
    | .bearerLeaveExecution => postSettlementSocietyFacePayloadAt oldVisit
        sourceIndex occurrence .bearerLeaveExecution
    | .bearerRoleIndependentContinuation =>
        postSettlementSocietyFacePayloadAt oldVisit sourceIndex occurrence
          .bearerRoleIndependentContinuation
    | .essentialAccessChannel channel => PLift (Nonempty
        (SourceGeneratedContributionCapacityEssentialAccessChannelAt
          (show Nat from current) channel
          (Classical.choice occurrence.2.periodicExitGenerated)))
    | .installedSocietyGrammar =>
        SourceNativeInstalledDependentFaceTraceAt
          (postSettlementSocietyVocabulary oldVisit sourceIndex) occurrence
  project := by
    intro projection current occurrence active
    cases projection with
    | ledger =>
        exact postSettlementSocietyFaceReadAt oldVisit sourceIndex occurrence
          .ledger
    | renewal =>
        exact postSettlementSocietyFaceReadAt oldVisit sourceIndex occurrence
          .renewal
    | birthBearerExit =>
        exact postSettlementSocietyFaceReadAt oldVisit sourceIndex occurrence
          .birthBearerExit
    | bearerExerciseResponse =>
        exact postSettlementSocietyFaceReadAt oldVisit sourceIndex occurrence
          .bearerExerciseResponse
    | bearerLeaveExecution =>
        exact postSettlementSocietyFaceReadAt oldVisit sourceIndex occurrence
          .bearerLeaveExecution
    | bearerRoleIndependentContinuation =>
        exact postSettlementSocietyFaceReadAt oldVisit sourceIndex occurrence
          .bearerRoleIndependentContinuation
    | essentialAccessChannel channel =>
        exact PLift.up
          ⟨sourceGeneratedContributionCapacityEssentialAccessChannelAt
            (show Nat from current) channel
            (Classical.choice occurrence.2.periodicExitGenerated)⟩
    | installedSocietyGrammar =>
        exact (postSettlementSocietyFamilyLaw oldVisit sourceIndex
          ).installedTraceAt occurrence

/-- The grammar trace is one pre-emitter component of this exact source. -/
def contributionCapacityPostSettlementSocietyGrammarInstallation
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    SourceNativeProjectionLaw.InstallationAt
      (postSettlementSocietyFamilyLaw oldVisit sourceIndex).toProjectionLaw
      (contributionCapacityPostSettlementRenewalProjectionLaw oldVisit
        sourceIndex) where
  embed := fun _ => .installedSocietyGrammar
  embed_injective := by
    intro left right _equality
    cases left
    cases right
    rfl
  outcome_heq := by
    intro current occurrence projection
    cases projection
    rfl

def contributionCapacityPostSettlementRenewalAuthoritySource
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    SourceNativeAuthoritySource (JointSettlementNAt oldVisit)
      (PostSettlementRenewalVAt oldVisit) where
  restructuringSource :=
    contributionCapacityPostSettlementRenewalRestructuringSource oldVisit
      sourceIndex
  eventInventoryAdmission := .reflOfNoFaithfulTerminal
    (contributionCapacityPostSettlementRenewalRestructuringSource oldVisit
      sourceIndex)
    (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := contributionCapacityPostSettlementRenewalTheory oldVisit
  projectionLaw := contributionCapacityPostSettlementRenewalProjectionLaw
    oldVisit sourceIndex

def contributionCapacityPostSettlementRenewalAuthoritativeRoot
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    SourceNativeAuthoritativeRootClosure (JointSettlementNAt oldVisit)
      (PostSettlementRenewalVAt oldVisit) where
  source := contributionCapacityPostSettlementRenewalAuthoritySource oldVisit
    sourceIndex
  emitted := contributionCapacityPostSettlementRenewalEmitted oldVisit
    sourceIndex
  compiler_commutes := fun _ => rfl

def contributionCapacityPostSettlementRenewalLivingRoot
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    SourceNativeLivingRootClosure (JointSettlementNAt oldVisit)
      (PostSettlementRenewalVAt oldVisit) :=
  (contributionCapacityPostSettlementRenewalAuthoritativeRoot oldVisit
    sourceIndex).toLivingWithoutFaithfulTerminal
      (fun _ => ⟨fun terminal => nomatch terminal⟩)

abbrev ContributionCapacityPostSettlementRenewalRootAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  contributionCapacityPostSettlementRenewalLivingRoot oldVisit sourceIndex

abbrev ContributionCapacityPostSettlementRenewalRootVisitAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  SourceNativeTemporalVisitAt
    ((ContributionCapacityPostSettlementRenewalRootAt oldVisit sourceIndex
      ).toAuthoritativeRoot.toLedgerRoot)

/-- Exact event-selected bearer exit installed in the existing post-settlement
root.  The actual-exit index is chosen from this root occurrence's native
write, not from a caller-supplied period or future table. -/
def contributionCapacityPostSettlementBirthBearerExitFaceAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (visit : ContributionCapacityPostSettlementRenewalRootVisitAt oldVisit
      sourceIndex) :
    SourceNativeRootSemanticFaceAt
      (ContributionCapacityPostSettlementRenewalRootAt oldVisit sourceIndex)
      visit where
  projection := ContributionCapacityPostSettlementRenewalProjection.birthBearerExit
  active := PUnit.unit
  classifier_eq := rfl

/-- Root-read authority of the installed bearer-exit face. -/
def contributionCapacityPostSettlementRootGeneratedBirthBearerExitAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (visit : ContributionCapacityPostSettlementRenewalRootVisitAt oldVisit
      sourceIndex) :=
  (contributionCapacityPostSettlementBirthBearerExitFaceAt oldVisit
    sourceIndex visit).rootRead

/-- Action-indexed noncapture response installed in the same existing
post-settlement root occurrence. -/
def contributionCapacityPostSettlementBearerExerciseResponseFaceAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (visit : ContributionCapacityPostSettlementRenewalRootVisitAt oldVisit
      sourceIndex) :
    SourceNativeRootSemanticFaceAt
      (ContributionCapacityPostSettlementRenewalRootAt oldVisit sourceIndex)
      visit where
  projection :=
    ContributionCapacityPostSettlementRenewalProjection.bearerExerciseResponse
  active := PUnit.unit
  classifier_eq := rfl

/-- Root-read authority of the action-indexed noncapture response. -/
def contributionCapacityPostSettlementRootGeneratedBearerExerciseResponseAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (visit : ContributionCapacityPostSettlementRenewalRootVisitAt oldVisit
      sourceIndex) :=
  (contributionCapacityPostSettlementBearerExerciseResponseFaceAt oldVisit
    sourceIndex visit).rootRead

/-- Exact bearer self-action power installed in the same target outer
occurrence. -/
def contributionCapacityPostSettlementBearerLeaveExecutionFaceAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (visit : ContributionCapacityPostSettlementRenewalRootVisitAt oldVisit
      sourceIndex) :
    SourceNativeRootSemanticFaceAt
      (ContributionCapacityPostSettlementRenewalRootAt oldVisit sourceIndex)
      visit where
  projection :=
    ContributionCapacityPostSettlementRenewalProjection.bearerLeaveExecution
  active := PUnit.unit
  classifier_eq := rfl

/-- Root-read authority of exact bearer leave self-action power. -/
def contributionCapacityPostSettlementRootGeneratedBearerLeaveExecutionAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (visit : ContributionCapacityPostSettlementRenewalRootVisitAt oldVisit
      sourceIndex) :=
  (contributionCapacityPostSettlementBearerLeaveExecutionFaceAt oldVisit
    sourceIndex visit).rootRead

/-- Capture-adjusted role-independent continuation installed in the same
successor outer occurrence. -/
def contributionCapacityPostSettlementBearerRoleIndependentContinuationFaceAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (visit : ContributionCapacityPostSettlementRenewalRootVisitAt oldVisit
      sourceIndex) :
    SourceNativeRootSemanticFaceAt
      (ContributionCapacityPostSettlementRenewalRootAt oldVisit sourceIndex)
      visit where
  projection := ContributionCapacityPostSettlementRenewalProjection.bearerRoleIndependentContinuation
  active := PUnit.unit
  classifier_eq := rfl

/-- Root-read authority of the role-independent target future. -/
def contributionCapacityPostSettlementRootGeneratedBearerRoleIndependentContinuationAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (visit : ContributionCapacityPostSettlementRenewalRootVisitAt oldVisit
      sourceIndex) :=
  (contributionCapacityPostSettlementBearerRoleIndependentContinuationFaceAt
    oldVisit sourceIndex visit).rootRead

/-- One installed dependent essential-access channel face. -/
def contributionCapacityPostSettlementEssentialAccessChannelFaceAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (visit : ContributionCapacityPostSettlementRenewalRootVisitAt oldVisit
      sourceIndex) (channel : EssentialAccessChannel) :
    SourceNativeRootSemanticFaceAt
      (ContributionCapacityPostSettlementRenewalRootAt oldVisit sourceIndex)
      visit where
  projection :=
    ContributionCapacityPostSettlementRenewalProjection.essentialAccessChannel
      channel
  active := PUnit.unit
  classifier_eq := rfl

/-- The channel payload is obtained from the post root's own rootRead. -/
def contributionCapacityPostSettlementRootGeneratedEssentialAccessChannelAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (visit : ContributionCapacityPostSettlementRenewalRootVisitAt oldVisit
      sourceIndex) (channel : EssentialAccessChannel) :=
  (contributionCapacityPostSettlementEssentialAccessChannelFaceAt oldVisit
    sourceIndex visit channel).rootRead

@[simp] theorem contributionCapacityPostSettlementRenewalRoot_lawSurface_exact
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    (ContributionCapacityPostSettlementRenewalRootAt oldVisit sourceIndex).source.base.lawSurface =
      TheoryState.rootSemantic (JointSettlementNAt oldVisit) :=
  rfl

theorem contributionCapacityPostSettlementRenewalFaithfulTerminal_isEmpty
    (oldVisit : OldVisit) (current : Nat) :
    IsEmpty ((PostSettlementRenewalVAt oldVisit).FaithfulTerminalAt current) :=
  ⟨fun terminal => nomatch terminal⟩

def contributionCapacityPostSettlementRenewalInitialVisit
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    SourceNativeTemporalVisitAt
      ((ContributionCapacityPostSettlementRenewalRootAt oldVisit sourceIndex)
        |>.toAuthoritativeRoot.toLedgerRoot) :=
  .finite
    ((ContributionCapacityPostSettlementRenewalRootAt oldVisit sourceIndex)
      |>.toAuthoritativeRoot.toRoot.initialVisit)

@[simp] theorem contributionCapacityPostSettlementRenewalInitialVisit_current
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    (show Nat from
      (contributionCapacityPostSettlementRenewalInitialVisit oldVisit
        sourceIndex).current) =
      contributionCapacityPostSettlementRenewalInitialCurrentAt sourceIndex :=
  rfl

@[simp] theorem contributionCapacityPostSettlementRenewalInitialVisit_one
    (oldVisit : OldVisit) :
    (show Nat from
      (contributionCapacityPostSettlementRenewalInitialVisit oldVisit 1).current) =
      15 :=
  rfl

def contributionCapacityPostSettlementRenewalInitialOccurrencePresentation
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    ConstructivePresentation
      ((ContributionCapacityPostSettlementRenewalRootAt oldVisit sourceIndex).toAuthoritativeRoot
        |>.toRoot.actual.OccurrenceAt
          (contributionCapacityPostSettlementRenewalInitialCurrentAt sourceIndex))
      Unit where
  forward := fun _ => ()
  backward := fun _ =>
    (ContributionCapacityPostSettlementRenewalRootAt oldVisit sourceIndex)
      |>.emitted
        (contributionCapacityPostSettlementRenewalInitialCurrentAt sourceIndex)
  backward_forward := by
    intro occurrence
    exact (contributionCapacityPostSettlementRenewalOccurrence_eq_emitted
      oldVisit sourceIndex occurrence).symm
  forward_backward := fun value => by cases value; rfl

theorem contributionCapacityPostSettlementRenewalProjection_generatesExit
    (oldVisit : OldVisit) (sourceIndex current : Nat) :
    Nonempty (PeriodicActualServiceExitAt current) := by
  have generated :=
    (contributionCapacityPostSettlementRenewalProjectionLaw oldVisit sourceIndex)
      |>.project ContributionCapacityPostSettlementRenewalProjection.renewal
        (contributionCapacityPostSettlementRenewalEmitted oldVisit sourceIndex
          current) PUnit.unit
  exact generated.down

abbrev AnyContributionCapacityPostSettlementRenewalOccurrenceAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  Sigma fun current : Nat =>
    (contributionCapacityPostSettlementRenewalSource oldVisit sourceIndex)
      |>.toRootSource.actual.OccurrenceAt current

def contributionCapacityPostSettlementRenewalOccurrenceAt
    (oldVisit : OldVisit) (sourceIndex current : Nat) :
    AnyContributionCapacityPostSettlementRenewalOccurrenceAt oldVisit
      sourceIndex :=
  ⟨current,
    (ContributionCapacityPostSettlementRenewalRootAt oldVisit sourceIndex)
      |>.emitted current⟩

theorem contributionCapacityPostSettlementRenewalOccurrenceAt_injective
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    Function.Injective
      (contributionCapacityPostSettlementRenewalOccurrenceAt oldVisit
        sourceIndex) := by
  intro left right equality
  exact congrArg Sigma.fst equality

theorem contributionCapacityPostSettlementRenewalAdjacentOccurrences_distinct
    (oldVisit : OldVisit) (sourceIndex current : Nat) :
    contributionCapacityPostSettlementRenewalOccurrenceAt oldVisit sourceIndex
        current ≠
      contributionCapacityPostSettlementRenewalOccurrenceAt oldVisit sourceIndex
        (current + 1) := by
  intro equality
  have current_eq :=
    contributionCapacityPostSettlementRenewalOccurrenceAt_injective oldVisit
      sourceIndex equality
  exact Nat.ne_of_lt (Nat.lt_succ_self current) current_eq

def contributionCapacityPostSettlementRenewalActualServiceOccurrenceAt
    (oldVisit : OldVisit) (sourceIndex current : Nat) :
    AnyPeriodicActualServiceExit :=
  let _rootOccurrence :=
    contributionCapacityPostSettlementRenewalOccurrenceAt oldVisit sourceIndex
      current
  periodicActualServiceExitOccurrenceAt current

@[simp] theorem contributionCapacityPostSettlementRenewalActualServiceOccurrenceAt_exact
    (oldVisit : OldVisit) (sourceIndex current : Nat) :
    contributionCapacityPostSettlementRenewalActualServiceOccurrenceAt oldVisit
        sourceIndex current =
      periodicActualServiceExitOccurrenceAt current :=
  rfl

theorem contributionCapacityPostSettlementRenewalActualServiceOccurrenceAt_injective
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    Function.Injective
      (contributionCapacityPostSettlementRenewalActualServiceOccurrenceAt
        oldVisit sourceIndex) := by
  intro left right equality
  exact periodicActualServiceExitOccurrenceAt_injective equality

end
end M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot.contributionCapacityPostSettlementRenewalLivingRoot
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot.contributionCapacityPostSettlementRootGeneratedBearerExerciseResponseAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot.contributionCapacityPostSettlementRootGeneratedBearerLeaveExecutionAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot.contributionCapacityPostSettlementRootGeneratedBearerRoleIndependentContinuationAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot.contributionCapacityPostSettlementRenewalInitialOccurrencePresentation
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot.contributionCapacityPostSettlementRenewalOccurrenceAt_injective
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot.contributionCapacityPostSettlementRenewalActualServiceOccurrenceAt_injective
