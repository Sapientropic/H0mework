import H0mework.Foundation.Responsibility.NoetherianClosure
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M9.JointRoot.ProofCarryingRenewalInquiryRuntime
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Handoff.NoGo.SourceGeneratedContributionCapacitySettlementNoEmptyHandoff
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.State.SourceGeneratedContributionCapacityJointSettlementState

/-!
# Direct consumer of final joint survivor settlement

Both inherited survivor debts now receive exact compiler-generated terminal
receipts.  The fixed process stays inside the action-generated target network:
its terminal current carries the complete `Fin 2` live ledger, and its
source-fixed successor is the unique empty support of the post-settlement
renewal root.  The society therefore continues without resurrecting either
debt and generates a fresh actual-service exit at every later current.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityJointSettlementConsumer

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M9ProofCarryingRenewalInquiryRuntime
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacitySettlementSupport
open M14SourceGeneratedContributionCapacitySettlementState
open M14SourceGeneratedContributionCapacitySettlementNoEmptyHandoff
open M14SourceGeneratedContributionCapacityJointSettlementWorld
open M14SourceGeneratedContributionCapacityJointSettlementMaterial
open M14SourceGeneratedContributionCapacityJointSettlementCompiler
open M14SourceGeneratedContributionCapacityJointSettlementRestructuring
open M14SourceGeneratedContributionCapacityJointSettlementRoot
open M14SourceGeneratedContributionCapacityPostSettlementRenewalCompiler
open M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot
open M14SourceGeneratedSequentialContributionCapacityJointSettlement
open M14SourceGeneratedContributionCapacityJointSettlementState
open M14UBIPeriodicActualServiceCapacity

abbrev CanonicalJointMaterialAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  CanonicalContributionCapacityJointSettlementMaterialAt oldVisit sourceIndex

abbrev CanonicalJointRootAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  CanonicalContributionCapacityJointSettlementRootAt oldVisit sourceIndex

def contributionCapacityPostSettlementRenewalRootVisitAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    Nat → RootVisit
      (ContributionCapacityPostSettlementRenewalRootAt oldVisit sourceIndex
        ).toAuthoritativeRoot.toRoot
  | 0 =>
      (ContributionCapacityPostSettlementRenewalRootAt oldVisit sourceIndex
        ).toAuthoritativeRoot.toRoot.initialVisit
  | index + 1 =>
      (contributionCapacityPostSettlementRenewalRootVisitAt oldVisit
        sourceIndex index).next rfl

def contributionCapacityPostSettlementRenewalVisitAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    SourceNativeTemporalVisitAt
      (ContributionCapacityPostSettlementRenewalRootAt oldVisit sourceIndex
        ).toAuthoritativeRoot.toLedgerRoot :=
  .finite (contributionCapacityPostSettlementRenewalRootVisitAt oldVisit
    sourceIndex index)

@[simp] theorem contributionCapacityPostSettlementRenewalVisit_current_exact
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    (show Nat from
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index).current) =
      contributionCapacityPostSettlementRenewalInitialCurrentAt sourceIndex +
        index := by
  induction index with
  | zero => rfl
  | succ index inductionHypothesis =>
      change
        (show Nat from
          (contributionCapacityPostSettlementRenewalRootVisitAt oldVisit
            sourceIndex index).current) + 1 =
          contributionCapacityPostSettlementRenewalInitialCurrentAt
              sourceIndex +
            (index + 1)
      change
        (show Nat from
          (contributionCapacityPostSettlementRenewalRootVisitAt oldVisit
            sourceIndex index).current) =
          contributionCapacityPostSettlementRenewalInitialCurrentAt
              sourceIndex + index at inductionHypothesis
      omega

def contributionCapacityJointSettlementDebtStateAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    Option Nat → SourceNativeLivingRootCurrentAt
      (JointSettlementNAt oldVisit)
  | none =>
      ⟨ContributionCapacityJointSettlementVAt oldVisit,
        CanonicalJointRootAt oldVisit sourceIndex,
        contributionCapacityJointSettlementTerminalVisit oldVisit sourceIndex
          (CanonicalJointMaterialAt oldVisit sourceIndex)⟩
  | some index =>
      ⟨PostSettlementRenewalVAt oldVisit,
        ContributionCapacityPostSettlementRenewalRootAt oldVisit sourceIndex,
        contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
          index⟩

def contributionCapacityJointSettlementDebtFiniteDepth?
    {oldVisit : OldVisit}
    (current : SourceNativeLivingRootCurrentAt
      (JointSettlementNAt oldVisit)) : Option Nat :=
  match current.visit.history with
  | .finite history => some (ProductiveFiniteRootHistoryAt.causalDepth history)
  | .postCofinal _ => none

@[simp] theorem contributionCapacityPostSettlementRenewalFiniteDepth_exact
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    contributionCapacityJointSettlementDebtFiniteDepth?
        (contributionCapacityJointSettlementDebtStateAt oldVisit sourceIndex
          (some index)) =
      some index := by
  change
    some
        (ProductiveFiniteRootHistoryAt.causalDepth
          (contributionCapacityPostSettlementRenewalRootVisitAt oldVisit
            sourceIndex index).history) =
      some index
  induction index with
  | zero => rfl
  | succ index inductionHypothesis =>
      change
        some
            (ProductiveFiniteRootHistoryAt.causalDepth
                (contributionCapacityPostSettlementRenewalRootVisitAt oldVisit
                  sourceIndex index).history +
              1) =
          some (index + 1)
      change
        some
            (ProductiveFiniteRootHistoryAt.causalDepth
              (contributionCapacityPostSettlementRenewalRootVisitAt oldVisit
                sourceIndex index).history) =
          some index at inductionHypothesis
      have depth_eq := Option.some.inj inductionHypothesis
      rw [depth_eq]

theorem contributionCapacityJointSettlementBool_ne_nat : Bool ≠ Nat := by
  intro equality
  have card_eq := congrArg (fun carrier : Type => Nat.card carrier) equality
  simp at card_eq

theorem contributionCapacityJointSettlementDebtStateAt_injective
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    Function.Injective
      (contributionCapacityJointSettlementDebtStateAt oldVisit sourceIndex) := by
  intro left right equality
  cases left with
  | none =>
      cases right with
      | none => rfl
      | some right =>
          have vocabulary_eq :=
            congrArg SourceNativeLivingRootCurrentAt.V equality
          have current_eq := congrArg Vocabulary.Current vocabulary_eq
          exact False.elim
            (contributionCapacityJointSettlementBool_ne_nat current_eq)
  | some left =>
      cases right with
      | none =>
          have vocabulary_eq :=
            congrArg SourceNativeLivingRootCurrentAt.V equality
          have current_eq := congrArg Vocabulary.Current vocabulary_eq
          exact False.elim
            (contributionCapacityJointSettlementBool_ne_nat current_eq.symm)
      | some right =>
          have depth_eq := congrArg
            contributionCapacityJointSettlementDebtFiniteDepth? equality
          rw [contributionCapacityPostSettlementRenewalFiniteDepth_exact,
            contributionCapacityPostSettlementRenewalFiniteDepth_exact]
              at depth_eq
          cases Option.some.inj depth_eq
          rfl

def contributionCapacityJointSettlementDebtSuccessor :
    Option Nat → Option Nat
  | none => some 0
  | some index => some (index + 1)

def contributionCapacityJointSettlementDebtProcessAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    SourceNativeLivingRootProcess (JointSettlementNAt oldVisit) where
  State := Option Nat
  stateAt := contributionCapacityJointSettlementDebtStateAt oldVisit
    sourceIndex
  stateAt_injective :=
    contributionCapacityJointSettlementDebtStateAt_injective oldVisit
      sourceIndex
  initial := none
  successorAt := by
    intro state
    refine ⟨contributionCapacityJointSettlementDebtSuccessor state, ?_⟩
    cases state with
    | none => exact ⟨rfl, trivial⟩
    | some index => exact ⟨rfl, HEq.rfl⟩

def contributionCapacityJointSettlementDebtCurrentAt
    (oldVisit : OldVisit) (sourceIndex : Nat) (entryIndex : Fin 2) :
    SourceNativeRootDebtCurrentAt
      (contributionCapacityJointSettlementDebtProcessAt oldVisit sourceIndex)
      (contributionCapacityJointSettlementLiveEntryAt oldVisit entryIndex) where
  state := none
  entry := contributionCapacityJointSettlementLiveEntryAt oldVisit entryIndex
  sameDebt := ⟨rfl, rfl⟩

def generatedContributionCapacityJointDebtSettlementAt
    (oldVisit : OldVisit) (sourceIndex : Nat) (entryIndex : Fin 2) :
    SourceNativeRootDebtSettlementAt
      (contributionCapacityJointSettlementDebtCurrentAt oldVisit sourceIndex
        entryIndex) where
  localTerminal := contributionCapacityJointSettlementExactTerminal oldVisit
    sourceIndex (CanonicalJointMaterialAt oldVisit sourceIndex)
  noSameDebtAtTarget :=
    ⟨fun target => PEmpty.elim target.1.2⟩

def generatedContributionCapacityJointDebtTerminalReceiptAt
    (oldVisit : OldVisit) (sourceIndex : Nat) (entryIndex : Fin 2) :
    LedgerEntryTerminalAt (JointSettlementNAt oldVisit)
      (contributionCapacityJointSettlementDebtCurrentAt oldVisit sourceIndex
        entryIndex).entry :=
  (generatedContributionCapacityJointDebtSettlementAt oldVisit sourceIndex
    entryIndex).receipt

/-- The actual service read at the source settlement current is the canonical
source occurrence, while the post-settlement root regenerates a genuinely
different occurrence at its later initial current.  Thus the handoff neither
stores nor replays an already-completed service event. -/
theorem contributionCapacityJointSettlement_sourceAndPostRenewalActualService_noReplay
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    let material := CanonicalJointMaterialAt oldVisit sourceIndex
    (periodicActualServiceExitOccurrenceAt
        (contributionCapacityJointSettlementDepthAt sourceIndex)).2.actualExit =
        material.sourceActualService ∧
      periodicActualServiceExitOccurrenceAt
          (contributionCapacityJointSettlementDepthAt sourceIndex) ≠
        contributionCapacityPostSettlementRenewalActualServiceOccurrenceAt
          oldVisit sourceIndex
          (contributionCapacityPostSettlementRenewalInitialCurrentAt
            sourceIndex) := by
  let material := CanonicalJointMaterialAt oldVisit sourceIndex
  constructor
  · change
      periodicActualServiceExitAt
          (contributionCapacityJointSettlementDepthAt sourceIndex) =
        material.sourceActualService
    exact material.sourceActualServiceExact.symm
  · rw [contributionCapacityPostSettlementRenewalActualServiceOccurrenceAt_exact]
    intro occurrenceEquality
    have currentEquality :=
      periodicActualServiceExitOccurrenceAt_injective occurrenceEquality
    unfold contributionCapacityJointSettlementDepthAt
      contributionCapacityJointSettlementSurvivorCurrentIndex
      contributionCapacityPostSettlementRenewalInitialCurrentAt at currentEquality
    omega

abbrev ProofCarryingContributionCapacityJointSettlementCertificateAt
    (oldVisit : OldVisit) (sourceIndex : Nat) : Prop :=
  (contributionCapacityJointSettlementDepthAt sourceIndex =
      contributionCapacityPostSettlementRenewalInitialCurrentAt sourceIndex -
        3) ∧
    Nonempty
      (SourceGeneratedSequentialActualActionAt
        (contributionCapacityJointSettlementActionProgramAt oldVisit
          sourceIndex (CanonicalJointMaterialAt oldVisit sourceIndex))
        (CanonicalJointMaterialAt oldVisit sourceIndex).sourceEvent) ∧
    Nonempty
      (Fin 2 ≃
        (contributionCapacityJointSettlementLiveLedger oldVisit).Entry) ∧
    ((contributionCapacityJointSettlementTerminalPatch oldVisit sourceIndex
      (CanonicalJointMaterialAt oldVisit sourceIndex)
      (contributionCapacityJointSettlementEmitted oldVisit sourceIndex
        (CanonicalJointMaterialAt oldVisit sourceIndex) true)).size = 2) ∧
    (∀ entryIndex : Fin 2,
      Nonempty
        (ContributionCapacityJointSettlementTerminalRowEvidenceAt oldVisit
          sourceIndex (CanonicalJointMaterialAt oldVisit sourceIndex)
          entryIndex) ∧
      Nonempty
        (SourceNativeRootDebtSettlementAt
          (contributionCapacityJointSettlementDebtCurrentAt oldVisit
            sourceIndex entryIndex))) ∧
    IsEmpty (contributionCapacityJointSettlementEmptyLedger oldVisit).Entry ∧
    ((CanonicalJointRootAt oldVisit sourceIndex
        |>.generatedTerminalHandoffAt
          (contributionCapacityJointSettlementTerminalVisit oldVisit
            sourceIndex (CanonicalJointMaterialAt oldVisit sourceIndex))
          (contributionCapacityJointSettlementExactTerminal oldVisit
            sourceIndex (CanonicalJointMaterialAt oldVisit sourceIndex))) =
      ⟨PostSettlementRenewalVAt oldVisit,
        contributionCapacityPostSettlementRenewalAuthoritativeRoot oldVisit
          sourceIndex,
        contributionCapacityPostSettlementRenewalInitialVisit oldVisit
          sourceIndex⟩) ∧
    (∀ support : (JointSettlementNAt oldVisit).Support,
      IsEmpty (OpenResponsibilityAt (JointSettlementNAt oldVisit) support) →
        support = contributionCapacityJointSettlementEmptySupport oldVisit) ∧
    IsEmpty (SourceNativeActualOutgoingEventAt
      (contributionCapacityJointSettlementRestructuringSource oldVisit
        sourceIndex (CanonicalJointMaterialAt oldVisit sourceIndex)
          ).toLedgerSource true) ∧
    (∀ index : Nat,
      Nonempty
        (PeriodicActualServiceExitAt
          (contributionCapacityPostSettlementRenewalInitialCurrentAt
              sourceIndex + index))) ∧
    ((periodicActualServiceExitOccurrenceAt
        (contributionCapacityJointSettlementDepthAt sourceIndex)).2.actualExit =
          (CanonicalJointMaterialAt oldVisit sourceIndex).sourceActualService ∧
      periodicActualServiceExitOccurrenceAt
          (contributionCapacityJointSettlementDepthAt sourceIndex) ≠
        contributionCapacityPostSettlementRenewalActualServiceOccurrenceAt
          oldVisit sourceIndex
          (contributionCapacityPostSettlementRenewalInitialCurrentAt
            sourceIndex)) ∧
    Function.Injective
      (contributionCapacityPostSettlementRenewalOccurrenceAt oldVisit
        sourceIndex)

theorem generatedContributionCapacityJointSettlement_closesBoth_renewsSociety
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    ProofCarryingContributionCapacityJointSettlementCertificateAt oldVisit
      sourceIndex := by
  let material := CanonicalJointMaterialAt oldVisit sourceIndex
  exact
    ⟨rfl,
      ⟨generatedContributionCapacityJointSettlementActionAt oldVisit
        sourceIndex material⟩,
      ⟨contributionCapacityJointSettlementLiveEntryEquiv oldVisit⟩,
      rfl,
      fun entryIndex =>
        ⟨⟨contributionCapacityJointSettlementTerminalRowEvidenceAt oldVisit
            sourceIndex material entryIndex⟩,
          ⟨generatedContributionCapacityJointDebtSettlementAt oldVisit
            sourceIndex entryIndex⟩⟩,
      contributionCapacityJointSettlementEmptyLedger_isEmpty oldVisit,
      contributionCapacityJointSettlementGeneratedHandoff_exact oldVisit
        sourceIndex material,
      contributionCapacityJointSettlementEmptySupport_unique oldVisit,
      (contributionCapacityJointSettlementExactTerminal oldVisit sourceIndex
        material).noOutgoingActual,
      fun index =>
        contributionCapacityPostSettlementRenewalProjection_generatesExit
          oldVisit sourceIndex
          (contributionCapacityPostSettlementRenewalInitialCurrentAt
            sourceIndex + index),
      contributionCapacityJointSettlement_sourceAndPostRenewalActualService_noReplay
        oldVisit sourceIndex,
      contributionCapacityPostSettlementRenewalOccurrenceAt_injective oldVisit
        sourceIndex⟩

theorem canonicalContributionCapacityJointSettlement_depths_exact
    (_oldVisit : OldVisit) :
    contributionCapacityJointSettlementDepthAt 1 = 12 ∧
      contributionCapacityPostSettlementRenewalInitialCurrentAt 1 = 15 :=
  ⟨rfl, rfl⟩

@[simp] theorem canonicalRuntime_depthTwelve_is_survivorSearch
    :
    (jointRuntime.stateAt 12).engine.node =
      .active (contributionCapacitySettlementSurvivorPresentationAt
        canonicalOldVisit 1 2) := by
  rfl

theorem jointSettlementActualPlay_search_sameRootVisit
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    (contributionCapacityJointSettlementActionStateAt oldVisit sourceIndex
      ).root =
        (contributionCapacitySettlementSurvivorStateAt oldVisit sourceIndex 2
          ).root ∧
      (contributionCapacityJointSettlementActionStateAt oldVisit sourceIndex
        ).visit =
        (contributionCapacitySettlementSurvivorStateAt oldVisit sourceIndex 2
          ).visit :=
  ⟨rfl, rfl⟩

theorem jointSettlementActualPlay_search_compilations_distinct
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    (contributionCapacityJointSettlementActionStateAt oldVisit sourceIndex
      ).compileInquiry () ≠
      (contributionCapacitySettlementSurvivorStateAt oldVisit sourceIndex 2
        ).compileInquiry () := by
  intro equality
  cases equality

def canonicalContributionCapacityJointSettlementSearchTick :=
  jointRuntime.tickAt 12

@[simp] theorem canonicalContributionCapacityJointSettlementSearchTick_exact :
    canonicalContributionCapacityJointSettlementSearchTick.resolution =
      .directlyAnswered
        (contributionCapacitySettlementSurvivorAnswerFaceAt canonicalOldVisit
          1 2)
        (contributionCapacitySettlementSurvivorAnswerConsumerAt
          canonicalOldVisit 1 2) :=
  rfl

/-- Actual play is activated at the exact canonical runtime occurrence but is
not substituted for the inquiry runtime's search resolution.  The private
certificate stores only provenance/equality facts and the generated action's
inhabitation; it is not a second runtime or occurrence registry. -/
structure ProofCarryingContributionCapacityJointSettlementRuntimeCertificate :
    Prop where
  runtimeNodeExact :
    (jointRuntime.stateAt 12).engine.node =
      .active (contributionCapacitySettlementSurvivorPresentationAt
        canonicalOldVisit 1 2)
  searchResolutionExact :
    canonicalContributionCapacityJointSettlementSearchTick.resolution =
      .directlyAnswered
        (contributionCapacitySettlementSurvivorAnswerFaceAt canonicalOldVisit
          1 2)
        (contributionCapacitySettlementSurvivorAnswerConsumerAt
          canonicalOldVisit 1 2)
  sameRoot :
    (contributionCapacityJointSettlementActionStateAt canonicalOldVisit 1
      ).root =
      (contributionCapacitySettlementSurvivorStateAt canonicalOldVisit 1 2
        ).root
  sameVisit :
    (contributionCapacityJointSettlementActionStateAt canonicalOldVisit 1
      ).visit =
      (contributionCapacitySettlementSurvivorStateAt canonicalOldVisit 1 2
        ).visit
  sourceEventExact :
    (CanonicalJointMaterialAt canonicalOldVisit 1).sourceEvent =
      (contributionCapacityJointSettlementActionStateAt canonicalOldVisit 1
        ).root.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
          (contributionCapacityJointSettlementActionStateAt canonicalOldVisit
            1).visit
  actualActionGenerated :
    Nonempty
      (SourceGeneratedSequentialActualActionAt
        (contributionCapacityJointSettlementActionProgramAt canonicalOldVisit
          1 (CanonicalJointMaterialAt canonicalOldVisit 1))
        (CanonicalJointMaterialAt canonicalOldVisit 1).sourceEvent)
  actualCompilationExact :
    (contributionCapacityJointSettlementActionStateAt canonicalOldVisit 1
      ).compileInquiry () =
      .actualAction
        (generatedContributionCapacityJointSettlementActionAt
          canonicalOldVisit 1
          (CanonicalJointMaterialAt canonicalOldVisit 1))
  searchCompilationExact :
    (contributionCapacitySettlementSurvivorStateAt canonicalOldVisit 1 2
      ).compileInquiry () =
      .answered
        (contributionCapacitySettlementSurvivorAnswerFaceAt canonicalOldVisit
          1 2)
        (contributionCapacitySettlementSurvivorAnswerConsumerAt
          canonicalOldVisit 1 2)
  authoritiesDistinct :
    (contributionCapacityJointSettlementActionStateAt canonicalOldVisit 1
      ).compileInquiry () ≠
      (contributionCapacitySettlementSurvivorStateAt canonicalOldVisit 1 2
        ).compileInquiry ()

theorem generatedContributionCapacityJointSettlement_runtimeSeparation :
    ProofCarryingContributionCapacityJointSettlementRuntimeCertificate where
  runtimeNodeExact := canonicalRuntime_depthTwelve_is_survivorSearch
  searchResolutionExact :=
    canonicalContributionCapacityJointSettlementSearchTick_exact
  sameRoot :=
    (jointSettlementActualPlay_search_sameRootVisit canonicalOldVisit 1).1
  sameVisit :=
    (jointSettlementActualPlay_search_sameRootVisit canonicalOldVisit 1).2
  sourceEventExact :=
    (CanonicalJointMaterialAt canonicalOldVisit 1).sourceEventExact
  actualActionGenerated :=
    ⟨generatedContributionCapacityJointSettlementActionAt canonicalOldVisit
      1 (CanonicalJointMaterialAt canonicalOldVisit 1)⟩
  actualCompilationExact :=
    contributionCapacityJointSettlementActionState_compiles_generated
      canonicalOldVisit 1
  searchCompilationExact :=
    contributionCapacitySettlementSurvivorState_compiles_answered
      canonicalOldVisit 1 2
  authoritiesDistinct :=
    jointSettlementActualPlay_search_compilations_distinct canonicalOldVisit 1

end
end M14SourceGeneratedContributionCapacityJointSettlementConsumer
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityJointSettlementConsumer.contributionCapacityJointSettlementDebtProcessAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityJointSettlementConsumer.generatedContributionCapacityJointDebtSettlementAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityJointSettlementConsumer.contributionCapacityJointSettlement_sourceAndPostRenewalActualService_noReplay
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityJointSettlementConsumer.generatedContributionCapacityJointSettlement_closesBoth_renewsSociety
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityJointSettlementConsumer.jointSettlementActualPlay_search_compilations_distinct
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityJointSettlementConsumer.generatedContributionCapacityJointSettlement_runtimeSeparation
