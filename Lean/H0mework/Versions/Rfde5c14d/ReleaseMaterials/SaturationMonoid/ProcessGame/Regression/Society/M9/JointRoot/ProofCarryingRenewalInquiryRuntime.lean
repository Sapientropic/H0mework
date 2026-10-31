import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M9.JointRoot.ProofCarryingRenewalU8Revision
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M9.JointRoot.ProofCarryingRenewalU8RevisedAuthority
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Action.SourceGeneratedContributionMergeActionState
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Action.SourceGeneratedContributionCapacityCutActionState
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Action.SourceGeneratedContributionCapacityFailureState
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.U8.Action.SourceGeneratedContributionCapacityU8TargetState
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.SourceGeneratedContributionCapacitySupportSeparation
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Action.SourceGeneratedContributionCapacityReopeningState
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Runtime.SourceGeneratedContributionCapacityReopeningSupportSeparation
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Action.SourceGeneratedContributionCapacitySettlementState
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Legislation.ProofCarryingLegislation

/-!
# Canonical inquiry runtime of the proof-carrying joint root

The depth-zero tick reads the inherited inquiry coordinate of the same
pre-emitter renewal uplift, resolves to the literal joint U8 core, and enters
that core's revised living root.  Depth one consumes the exact revised-current
occurrence and generates the cross-root contribution merge.  Depth two spends
the merged contribution's remaining capacity, depth three lets the resulting
narrow-law residual trigger self-U8, and depth four consumes the revised
root's generated-residual answer.  Depth five consumes the exact source-backed
UBI reopening action; depth six enters its action-generated root.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M9ProofCarryingRenewalInquiryRuntime

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open Renewal Legislation Revision
open M9ProofCarryingRenewalInquiryRoot
open M9ProofCarryingRenewalU8Failure
open M9ProofCarryingRenewalU8Revision
open M9ProofCarryingRenewalU8RevisedLedger
open M9ProofCarryingRenewalU8RevisedWorld
open M14SourceGeneratedContributionMergeActionState
open M14SourceGeneratedContributionCapacityCutActionState
open M14SourceGeneratedSequentialContributionCapacityCut
open M14SourceGeneratedContributionCapacityCutWorld
open M14SourceGeneratedContributionCapacityCutRoot
open M14SourceGeneratedContributionCapacityFailureState
open M14SourceGeneratedContributionCapacityU8TargetState
open M14SourceGeneratedContributionCapacityU8Revision
open M14SourceGeneratedContributionCapacityReopeningState
open M14SourceGeneratedSequentialContributionCapacityReopening
open M14SourceGeneratedContributionCapacitySettlementState
open M14SourceGeneratedSequentialContributionCapacitySettlement
open M14SourceGeneratedContributionCapacitySettlementRoot
open M14SourceGeneratedContributionCapacitySettlementActionSource
open M14SourceGeneratedContributionCapacitySettlementSurvivorCompiler
open M14SourceGeneratedContributionMergeSupportSeparation
open M14SourceGeneratedContributionCapacitySupportSeparation
open M14SourceGeneratedContributionCapacityReopeningSupportSeparation

abbrev N := M9ProofCarryingRenewalInquiryRoot.N
abbrev V := M9ProofCarryingRenewalInquiryRoot.V
abbrev U7 := M9ProofCarryingRenewalU8Failure.U7
abbrev NewN := M9ProofCarryingRenewalU8RevisedWorld.NewN
abbrev NewV := M9ProofCarryingRenewalU8RevisedWorld.NewV
abbrev MergeN := M14SourceGeneratedContributionMergeSupportSeparation.MergeN
abbrev MergeV :=
  M14SourceGeneratedContributionMergeCompiler.TargetV
    M9ProofCarryingRenewalU8Failure.rooted
abbrev CapacityN :=
  M14SourceGeneratedContributionCapacitySupportSeparation.CapacityN
abbrev CapacityV :=
  M14SourceGeneratedContributionCapacityCutCompiler.TargetV
    M9ProofCarryingRenewalU8Failure.rooted
abbrev CapacityU8N :=
  M14SourceGeneratedContributionCapacitySupportSeparation.CapacityU8N
abbrev CapacityU8V :=
  M14SourceGeneratedContributionCapacityU8Compiler.CapacityU8VAt
    M14SourceGeneratedContributionCapacitySupportSeparation.canonicalOldVisit
abbrev ReopeningN :=
  M14SourceGeneratedContributionCapacityReopeningSupportSeparation.ReopeningN
abbrev ReopeningV :=
  M14SourceGeneratedContributionCapacityReopeningCompiler.ReopeningVAt
    M14SourceGeneratedContributionCapacitySupportSeparation.canonicalOldVisit 1
abbrev SettlementV :=
  M14SourceGeneratedContributionCapacitySettlementCompiler.SettlementVAt
    M14SourceGeneratedContributionCapacitySupportSeparation.canonicalOldVisit
abbrev SettlementSurvivorV :=
  M14SourceGeneratedContributionCapacitySettlementSurvivorCompiler.ContributionCapacitySettlementSurvivorVAt
    M14SourceGeneratedContributionCapacitySupportSeparation.canonicalOldVisit

def inquiryCompilation : SourceNativeInquiryCompilationAt
    jointRoot jointVisit U7
      RootInquiryU8CompletionRegression.theoryAuditCalculus
      RootInquiryU8CompletionRegression.oldTheory () inquiryEvent entry authority
      :=
  .requiresU8 RootInquiryU8CompletionRegression.obstruction
    RootInquiryU8CompletionRegression.u7Gate
    RootInquiryU8CompletionRegression.failure jointCore

def inquiryCompilationProgram : SourceNativeInquiryCompilationProgramAt
    jointRoot jointVisit U7
      RootInquiryU8CompletionRegression.theoryAuditCalculus
      RootInquiryU8CompletionRegression.oldTheory () inquiryEvent entry authority where
  compile := fun _ => inquiryCompilation

def inheritedInquiryInstallation : SourceNativeProjectionLaw.InstallationAt
    RootInquiryU8CompletionRegression.projectionLaw
    jointRoot.toAuthoritativeRoot.source.projectionLaw :=
  ((inheritedByRenewal
      RootInquiryU8CompletionRegression.root.toAuthoritativeRoot.source
        renewalLaw).trans
      ((inheritedByRenewal proofCarryingAuthoritySource ubiLaw).trans
        ((inheritedByRenewal ubiAuthoritySource recognitionWitnessLaw).trans
          ((inheritedByRenewal recognitionAuthoritySource mandateLaw).trans
            ((inheritedByRenewal mandateAuthoritySource
                essentialServiceRestorationLaw).trans
              (inheritedByRenewal essentialServiceRestorationAuthoritySource
                routeOutageRestorationLaw)))))).trans
    oldInventoryInheritedByCommonClearing

/-- Literal inquiry state of the expanded root.  The named inherited inquiry
coordinate is justified by the pre-emitter installation's whole-outcome law. -/
def jointState : RootInquiryStateAt N V where
  root := jointRoot
  visit := jointVisit
  U7 := U7
  calculus := RootInquiryU8CompletionRegression.theoryAuditCalculus
  Query := Unit
  entryAt := fun _ => entry
  authorityAt := fun _ => authority
  compilationProgramAt := fun _ => inquiryCompilationProgram
  compilationFaceAt := fun _ =>
    { projection := M9ProofCarryingRenewalInquiryRoot.jointInquiryProjection
      active := ()
      classifier_eq := rfl
      project_heq := by
        have outcome := inheritedInquiryInstallation.outcome_heq
          (jointRoot.emitted jointVisit.current) .inquiry
        cases outcome
        exact HEq.rfl }
  u7RootDisposition_commutes := by
    intro _query _obstruction _audit audit_eq
    cases audit_eq
    exact theoryAuditRootDispositionCommutes

def jointEngineState : RootInquiryEngineStateAt N V :=
  RootInquiryEngineStateAt.create jointState

def jointPresentation : RootInquiryStatePresentation where
  N := N
  V := V
  state := jointEngineState

/-! ## Revised-root ordinary inquiry states

The compatibility names below consume the unique visit/entry/authority chain
owned by `M9ProofCarryingRenewalU8RevisedAuthority`. -/

abbrev revisedInquiryEventAt :=
  M9ProofCarryingRenewalU8RevisedAuthority.inquiryEventAt

abbrev revisedInquiryEntryReadoutAt :=
  M9ProofCarryingRenewalU8RevisedAuthority.inquiryEntryReadoutAt

theorem revisedNextEq (index : Nat) :
    (revisedLivingRoot.toAuthoritativeRoot.toRoot.evolutionAt
      (revisedVisitAt index).current).nextCurrent? =
      some (revisedVisitAt (index + 1)).current :=
  M9ProofCarryingRenewalU8RevisedAuthority.nextEq index

theorem revisedTemporalVisit_next_eq (index : Nat) :
    ((SourceNativeTemporalVisitAt.finite (revisedVisitAt index)).next
      (revisedNextEq index)) =
      SourceNativeTemporalVisitAt.finite (revisedVisitAt (index + 1)) :=
  M9ProofCarryingRenewalU8RevisedAuthority.temporalVisit_next_eq index

theorem revisedCanonicalTargetReadout_eq (index : Nat) :
    revisedLivingRoot.toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext
        (revisedNextEq index) (revisedInquiryEntryReadoutAt index) =
      revisedInquiryEntryReadoutAt (index + 1) :=
  M9ProofCarryingRenewalU8RevisedAuthority.canonicalTargetReadout_eq index

abbrev revisedVisitEntryAt :=
  M9ProofCarryingRenewalU8RevisedAuthority.visitEntryAt

theorem revisedVisitEntry_eq_inquiryReadout (index : Nat) :
    revisedVisitEntryAt index = revisedInquiryEntryReadoutAt index :=
  M9ProofCarryingRenewalU8RevisedAuthority.visitEntry_eq_inquiryReadout index

def revisedInitialAuthority :=
  M9ProofCarryingRenewalU8RevisedAuthority.initialAuthority

def revisedAuthorityAt :=
  M9ProofCarryingRenewalU8RevisedAuthority.authorityAt

abbrev revisedInquiryAuthorityAt :=
  M9ProofCarryingRenewalU8RevisedAuthority.inquiryAuthorityAt

def revisedAnswerFaceAt (index : Nat) :
    SourceNativeRootSemanticFaceAt revisedLivingRoot
      (.finite (revisedVisitAt index)) where
  projection := .answer
  active := PUnit.unit
  classifier_eq := rfl

def revisedAnswerConsumerAt (index : Nat) :
    SourceNativeInquiryAnswerConsumerAt () (revisedInquiryEventAt index)
      (revisedInquiryEntryReadoutAt index) (revisedAnswerFaceAt index) where
  projection := .consumer
  active := PUnit.unit
  classifier_eq := rfl
  project_heq := HEq.rfl

abbrev revisedInquiryCompilationAt (index : Nat) :
    SourceNativeInquiryCompilationAt revisedLivingRoot
      (.finite (revisedVisitAt index)) revisedU7 revisedCalculus revisedTheory
      () (revisedInquiryEventAt index) (revisedInquiryEntryReadoutAt index)
        (revisedInquiryAuthorityAt index) :=
  .answered (revisedAnswerFaceAt index) (revisedAnswerConsumerAt index)

def revisedStateAt (index : Nat) : RootInquiryStateAt NewN NewV where
  root := revisedLivingRoot
  visit := .finite (revisedVisitAt index)
  U7 := revisedU7
  calculus := revisedCalculus
  Query := Unit
  entryAt := fun _ => revisedInquiryEntryReadoutAt index
  authorityAt := fun _ => revisedInquiryAuthorityAt index
  compilationProgramAt := fun _ =>
    { compile := fun _ => revisedInquiryCompilationAt index }
  compilationFaceAt := fun _ =>
    { projection := .inquiry
      active := PUnit.unit
      classifier_eq := rfl
      project_heq := HEq.rfl }
  u7RootDisposition_commutes := by
    intro _query _obstruction _audit audit_eq
    cases audit_eq

def revisedEngineStateAt (index : Nat) :
    RootInquiryEngineStateAt NewN NewV :=
  RootInquiryEngineStateAt.create (revisedStateAt index)

def revisedPresentationAt (index : Nat) : RootInquiryStatePresentation where
  N := NewN
  V := NewV
  state := revisedEngineStateAt index

/-! ## One source-owned macro process and runtime -/

def canonicalOldVisit : RootVisit jointRoot.toAuthoritativeRoot.toRoot :=
  jointRoot.toAuthoritativeRoot.toRoot.initialVisit

inductive ProcessState
  | original
  | contributionMergeAction
  | contributionCapacityAction
  | contributionCapacityFailure
  | contributionCapacityRevisedAnswer
  | contributionCapacityReopeningAction
  | contributionCapacityReopened (index : Fin 2)
  | contributionCapacitySettlementAction
  | contributionCapacitySettlementTerminal
  | contributionCapacitySettlementSurvivor (index : Nat)

def processPresentation : ProcessState → RootInquiryStatePresentation
  | .original => jointPresentation
  | .contributionMergeAction => contributionMergeActionPresentation
  | .contributionCapacityAction =>
      contributionCapacityCutActionPresentationAt canonicalOldVisit
  | .contributionCapacityFailure =>
      contributionCapacityFailurePresentationAt canonicalOldVisit
  | .contributionCapacityRevisedAnswer =>
      contributionCapacityU8TargetPresentationAt canonicalOldVisit 0
  | .contributionCapacityReopeningAction =>
      contributionCapacityReopeningActionPresentationAt canonicalOldVisit 1
  | .contributionCapacityReopened index =>
      contributionCapacityReopenedPresentationAt canonicalOldVisit 1 index.val
  | .contributionCapacitySettlementAction =>
      contributionCapacitySettlementActionPresentationAt canonicalOldVisit 1
  | .contributionCapacitySettlementTerminal =>
      contributionCapacitySettlementTerminalPresentationAt canonicalOldVisit 1
  | .contributionCapacitySettlementSurvivor index =>
      contributionCapacitySettlementSurvivorPresentationAt canonicalOldVisit
        1 index

def erasedCurrentLabel (erased : AnyAuthoritativeRootCurrent) :
    Sigma fun Carrier : Type => Carrier :=
  ⟨erased.current.V.Current, erased.current.visit.current⟩

def erasedRootSupport (erased : AnyAuthoritativeRootCurrent) :
    Sigma fun N : WorldRelationNetwork => N.Support :=
  ⟨erased.N,
    erased.current.root.toRoot.supportAt erased.current.visit.current⟩

def processSupportCard : ProcessState → Nat
  | .original => 2
  | .contributionMergeAction => 6
  | .contributionCapacityAction => 12
  | .contributionCapacityFailure => 24
  | .contributionCapacityRevisedAnswer => 25
  | .contributionCapacityReopeningAction => 25
  | .contributionCapacityReopened _ => 50
  | .contributionCapacitySettlementAction => 50
  | .contributionCapacitySettlementTerminal => 50
  | .contributionCapacitySettlementSurvivor _ => 50

def processExpectedCurrentLabel : ProcessState → Sigma fun Carrier : Type => Carrier
  | .original => erasedCurrentLabel (processPresentation .original).erase
  | .contributionMergeAction =>
      erasedCurrentLabel (processPresentation .contributionMergeAction).erase
  | .contributionCapacityAction =>
      erasedCurrentLabel (processPresentation .contributionCapacityAction).erase
  | .contributionCapacityFailure =>
      erasedCurrentLabel (processPresentation .contributionCapacityFailure).erase
  | .contributionCapacityRevisedAnswer => ⟨Nat, 2⟩
  | .contributionCapacityReopeningAction => ⟨Nat, 3⟩
  | .contributionCapacityReopened index => ⟨Nat, index.val + 1⟩
  | .contributionCapacitySettlementAction => ⟨Nat, 3⟩
  | .contributionCapacitySettlementTerminal => ⟨Bool, true⟩
  | .contributionCapacitySettlementSurvivor index =>
      ⟨Nat,
        contributionCapacitySettlementSurvivorInitialCurrentAt 1 + index⟩

theorem processPresentation_support_card (state : ProcessState) :
    Nat.card (processPresentation state).N.Support = processSupportCard state := by
  cases state with
  | original => exact originalSupport_card
  | contributionMergeAction => exact revisedSupport_card
  | contributionCapacityAction => exact mergeSupport_card
  | contributionCapacityFailure => exact capacitySupport_card
  | contributionCapacityRevisedAnswer => exact capacityU8Support_card
  | contributionCapacityReopeningAction => exact capacityU8Support_card
  | contributionCapacityReopened index => exact reopeningSupport_card
  | contributionCapacitySettlementAction => exact reopeningSupport_card
  | contributionCapacitySettlementTerminal => exact reopeningSupport_card
  | contributionCapacitySettlementSurvivor index => exact reopeningSupport_card

theorem processPresentation_currentLabel_exact (state : ProcessState) :
    erasedCurrentLabel (processPresentation state).erase =
      processExpectedCurrentLabel state := by
  cases state with
  | original => rfl
  | contributionMergeAction => rfl
  | contributionCapacityAction => rfl
  | contributionCapacityFailure => rfl
  | contributionCapacityRevisedAnswer => rfl
  | contributionCapacityReopeningAction => rfl
  | contributionCapacityReopened index =>
      unfold erasedCurrentLabel
      dsimp [processPresentation, processExpectedCurrentLabel,
        RootInquiryStatePresentation.erase]
      refine Sigma.ext rfl ?_
      exact heq_of_eq
        (contributionCapacityReopeningVisit_current_exact canonicalOldVisit 1
          (index.val + 1))
  | contributionCapacitySettlementAction =>
      unfold erasedCurrentLabel
      dsimp [processPresentation, processExpectedCurrentLabel,
        RootInquiryStatePresentation.erase]
      refine Sigma.ext rfl ?_
      exact heq_of_eq
        (contributionCapacitySettlementActionVisit_current_exact
          canonicalOldVisit 1)
  | contributionCapacitySettlementTerminal => rfl
  | contributionCapacitySettlementSurvivor index =>
      unfold erasedCurrentLabel
      dsimp [processPresentation, processExpectedCurrentLabel,
        RootInquiryStatePresentation.erase]
      refine Sigma.ext rfl ?_
      exact heq_of_eq
        (contributionCapacitySettlementSurvivorVisit_current_exact
          canonicalOldVisit 1 index)

theorem nat_ne_bool : Nat ≠ Bool := by
  intro equality
  have card_eq := congrArg (fun carrier : Type => Nat.card carrier) equality
  simp at card_eq

theorem processPresentation_erase_injective :
    Function.Injective (fun state => (processPresentation state).erase) := by
  intro left right equality
  have network_eq := congrArg AnyAuthoritativeRootCurrent.N equality
  have support_eq := congrArg WorldRelationNetwork.Support network_eq
  have support_card_eq :=
    congrArg (fun carrier : Type => Nat.card carrier) support_eq
  have card_eq : processSupportCard left = processSupportCard right :=
    (processPresentation_support_card left).symm.trans
      (support_card_eq.trans (processPresentation_support_card right))
  have label_eq := congrArg erasedCurrentLabel equality
  have root_support_eq := congrArg erasedRootSupport equality
  have current_carrier_card_eq := congrArg
    (fun erased : AnyAuthoritativeRootCurrent =>
      Nat.card erased.current.V.Current) equality
  rw [processPresentation_currentLabel_exact left,
    processPresentation_currentLabel_exact right] at label_eq
  cases left <;> cases right
  all_goals simp [processSupportCard] at card_eq
  all_goals try rfl
  all_goals simp [processExpectedCurrentLabel] at label_eq
  all_goals try
    simp [processPresentation, erasedRootSupport] at root_support_eq
  all_goals try
    simp [processPresentation] at current_carrier_card_eq
  all_goals try { exact False.elim (nat_ne_bool label_eq.1) }
  all_goals try { exact False.elim (nat_ne_bool label_eq.1.symm) }
  all_goals try omega
  all_goals try { cases label_eq; rfl }
  rename_i leftIndex rightIndex
  have index_eq : leftIndex = rightIndex := Fin.ext label_eq
  cases index_eq
  rfl

def process : SourceNativeInquiryEngineProcess.{0} where
  State := ProcessState
  stateAt := fun state => .active (processPresentation state)
  erase_injective := by
    intro left right leftState rightState leftActive rightActive equality
    cases leftActive
    cases rightActive
    exact processPresentation_erase_injective equality
  initial := .original
  successorAt := by
    intro state query
    cases state with
    | original => exact ⟨.contributionMergeAction, rfl, HEq.rfl⟩
    | contributionMergeAction =>
        change Unit at query
        cases query
        refine ⟨.contributionCapacityAction, ?_⟩
        exact RootInquiryProcessNode.active_actualAction_successor_valid
          contributionMergeActionPresentation
          (contributionCapacityCutActionPresentationAt canonicalOldVisit)
          PUnit.unit generatedContributionMergeAction rfl rfl HEq.rfl
    | contributionCapacityAction =>
        change Unit at query
        cases query
        refine ⟨.contributionCapacityFailure, ?_⟩
        exact RootInquiryProcessNode.active_actualAction_successor_valid
          (contributionCapacityCutActionPresentationAt canonicalOldVisit)
          (contributionCapacityFailurePresentationAt canonicalOldVisit)
          PUnit.unit
          (generatedContributionCapacityCutActionAt canonicalOldVisit)
          rfl rfl HEq.rfl
    | contributionCapacityFailure =>
        change Unit at query
        cases query
        exact ⟨.contributionCapacityRevisedAnswer, rfl, HEq.rfl⟩
    | contributionCapacityRevisedAnswer =>
        change Unit at query
        cases query
        refine ⟨.contributionCapacityReopeningAction, ?_⟩
        exact RootInquiryProcessNode.active_directlyAnswered_successor_valid
          (contributionCapacityU8TargetPresentationAt
            canonicalOldVisit 0)
          (contributionCapacityReopeningActionPresentationAt
            canonicalOldVisit 1)
          PUnit.unit
          (contributionCapacityU8AnswerFaceAt
            canonicalOldVisit 0)
          (contributionCapacityU8AnswerConsumerAt
            canonicalOldVisit 0)
          rfl rfl HEq.rfl
    | contributionCapacityReopeningAction =>
        change Unit at query
        cases query
        refine ⟨.contributionCapacityReopened 0, ?_⟩
        exact RootInquiryProcessNode.active_actualAction_successor_valid
          (contributionCapacityReopeningActionPresentationAt
            canonicalOldVisit 1)
          (contributionCapacityReopenedPresentationAt canonicalOldVisit 1 0)
          PUnit.unit
          (generatedContributionCapacityReopeningActionAt canonicalOldVisit 1)
          rfl rfl HEq.rfl
    | contributionCapacityReopened index =>
        change Unit at query
        cases query
        refine Fin.cases ?_ (fun tail => ?_) index
        · refine ⟨.contributionCapacityReopened 1, ?_⟩
          exact RootInquiryProcessNode.active_directlyAnswered_successor_valid
            (contributionCapacityReopenedPresentationAt canonicalOldVisit 1 0)
            (contributionCapacityReopenedPresentationAt canonicalOldVisit 1 1)
            PUnit.unit
            (contributionCapacityReopenedAnswerFaceAt canonicalOldVisit 1 0)
            (contributionCapacityReopenedAnswerConsumerAt canonicalOldVisit 1 0)
            rfl rfl HEq.rfl
        · change Fin 1 at tail
          have tail_eq : tail = (0 : Fin 1) := Subsingleton.elim _ _
          subst tail
          refine ⟨.contributionCapacitySettlementAction, ?_⟩
          exact RootInquiryProcessNode.active_directlyAnswered_successor_valid
            (contributionCapacityReopenedPresentationAt canonicalOldVisit 1 1)
            (contributionCapacitySettlementActionPresentationAt
              canonicalOldVisit 1)
            PUnit.unit
            (contributionCapacityReopenedAnswerFaceAt canonicalOldVisit 1 1)
            (contributionCapacityReopenedAnswerConsumerAt canonicalOldVisit 1 1)
            rfl rfl HEq.rfl
    | contributionCapacitySettlementAction =>
        change Unit at query
        cases query
        refine ⟨.contributionCapacitySettlementTerminal, ?_⟩
        exact RootInquiryProcessNode.active_actualAction_successor_valid
          (contributionCapacitySettlementActionPresentationAt
            canonicalOldVisit 1)
          (contributionCapacitySettlementTerminalPresentationAt
            canonicalOldVisit 1)
          PUnit.unit
          (generatedContributionCapacitySettlementActionAt canonicalOldVisit 1)
          rfl rfl HEq.rfl
    | contributionCapacitySettlementTerminal =>
        change Unit at query
        cases query
        refine ⟨.contributionCapacitySettlementSurvivor 0, ?_⟩
        exact
          RootInquiryProcessNode.active_directlyAnswered_terminalHandoff_successor_valid
          (contributionCapacitySettlementTerminalPresentationAt
            canonicalOldVisit 1)
          (contributionCapacitySettlementSurvivorPresentationAt
            canonicalOldVisit 1 0)
          PUnit.unit
          (contributionCapacitySettlementTerminalAnswerFaceAt
            canonicalOldVisit 1)
          (contributionCapacitySettlementTerminalAnswerConsumerAt
            canonicalOldVisit 1)
          rfl
          (contributionCapacitySettlementExactTerminal canonicalOldVisit 1
            (contributionCapacitySettlementActionExactSourceEventAt
              canonicalOldVisit 1))
          rfl
    | contributionCapacitySettlementSurvivor index =>
        change Unit at query
        cases query
        refine ⟨.contributionCapacitySettlementSurvivor (index + 1), ?_⟩
        exact RootInquiryProcessNode.active_directlyAnswered_successor_valid
          (contributionCapacitySettlementSurvivorPresentationAt
            canonicalOldVisit 1 index)
          (contributionCapacitySettlementSurvivorPresentationAt
            canonicalOldVisit 1 (index + 1))
          PUnit.unit
          (contributionCapacitySettlementSurvivorAnswerFaceAt
            canonicalOldVisit 1 index)
          (contributionCapacitySettlementSurvivorAnswerConsumerAt
            canonicalOldVisit 1 index)
          rfl rfl HEq.rfl

def runtimeInitialQuery : (process.stateAt process.initial).Query := ()

theorem runtimeInitialQuery_unique
    (candidate : (process.stateAt process.initial).Query) :
    candidate = runtimeInitialQuery := by cases candidate; rfl

def runtimeNextQueryAt
    (state : ProcessState) (query : (process.stateAt state).Query) :
    (process.stateAt (process.successorAt state query).1).Query := by
  cases state with
  | original => exact ()
  | contributionMergeAction => exact ()
  | contributionCapacityAction => exact ()
  | contributionCapacityFailure => exact ()
  | contributionCapacityRevisedAnswer => exact ()
  | contributionCapacityReopeningAction => exact ()
  | contributionCapacityReopened index =>
      change Unit at query
      cases query
      refine Fin.cases ?_ (fun tail => ?_) index
      · exact ()
      · change Fin 1 at tail
        have tail_eq : tail = (0 : Fin 1) := Subsingleton.elim _ _
        subst tail
        exact ()
  | contributionCapacitySettlementAction => exact ()
  | contributionCapacitySettlementTerminal => exact ()
  | contributionCapacitySettlementSurvivor index => exact ()

theorem runtimeNextQuery_unique
    (state : ProcessState) (query : (process.stateAt state).Query)
    (candidate :
      (process.stateAt (process.successorAt state query).1).Query) :
    candidate = runtimeNextQueryAt state query := by
  cases state with
  | original => cases candidate; rfl
  | contributionMergeAction => cases candidate; rfl
  | contributionCapacityAction => cases candidate; rfl
  | contributionCapacityFailure => cases candidate; rfl
  | contributionCapacityRevisedAnswer => cases candidate; rfl
  | contributionCapacityReopeningAction => cases candidate; rfl
  | contributionCapacityReopened index =>
      change Unit at query
      cases query
      have index_cases : index = 0 ∨ index = 1 := by omega
      rcases index_cases with rfl | rfl
      · change Unit at candidate
        cases candidate
        rfl
      · change Unit at candidate
        cases candidate
        rfl
  | contributionCapacitySettlementAction => cases candidate; rfl
  | contributionCapacitySettlementTerminal => cases candidate; rfl
  | contributionCapacitySettlementSurvivor index =>
      change Unit at candidate
      cases candidate
      rfl

def jointRuntime : SourceNativeInquiryRuntime process where
  activationLaw := Engine.SourceNativeInquiryActivationLaw.ofUnique
    runtimeInitialQuery runtimeInitialQuery_unique
    runtimeNextQueryAt runtimeNextQuery_unique

def firstTick := jointRuntime.tickAt 0

theorem firstTick_resolution_is_jointCore :
    firstTick.resolution =
      .revised RootInquiryU8CompletionRegression.obstruction
        RootInquiryU8CompletionRegression.u7Gate
        RootInquiryU8CompletionRegression.failure jointCore :=
  rfl

theorem cofaceResumption :
    SourceNativeInquiryRuntime.CofaceRealizationResumptionAt
      jointCore jointRuntime 0 where
  contains_core := by rw [firstTick_resolution_is_jointCore]; exact HEq.rfl

set_option linter.defProp false in
def firstTick_next_erases_to_generated :=
  firstTick.next_erases_to_generated

theorem firstTick_next_preserves_revisedLivingRoot : HEq
    (processPresentation .contributionMergeAction).state.base.root
    jointCore.revision.generate.newLivingRoot :=
  firstTick.next_preservesGeneratedLivingLaw

@[simp] theorem secondState_node_is_contributionMergeAction :
    (jointRuntime.stateAt 1).engine.node =
      .active contributionMergeActionPresentation :=
  rfl

theorem secondState_uses_generated_revisedLivingRoot : HEq
    (sourceGeneratedRuntimeInquiryCoordinateAt jointRuntime 1).1.state.base.root
    jointCore.revision.generate.newLivingRoot :=
  HEq.rfl

def secondTick := jointRuntime.tickAt 1

@[simp] theorem secondTick_resolution_is_contributionMerge :
    secondTick.resolution =
      .actualAction generatedContributionMergeAction :=
  rfl

@[simp] theorem secondTick_resolutionKind_is_actualAction :
    secondTick.resolutionKind = .actualAction := by
  rw [SourceNativeInquiryRuntime.ExactActivatedInquiryOccurrenceAt.resolutionKind]
  rw [secondTick_resolution_is_contributionMerge]
  rfl

theorem contributionMergeResumption :
    SourceNativeInquiryRuntime.SequentialActualActionResumptionAt
      generatedContributionMergeAction jointRuntime 1 where
  contains_action := by
    rw [secondTick_resolution_is_contributionMerge]
    exact HEq.rfl

theorem secondTick_next_preserves_contributionMergeRoot : HEq
    (processPresentation .contributionCapacityAction).state.base.root
    generatedContributionMergeAction.target.targetRoot :=
  secondTick.next_preservesGeneratedLivingLaw

@[simp] theorem thirdState_node_is_contributionCapacityAction :
    (jointRuntime.stateAt 2).engine.node =
      .active (contributionCapacityCutActionPresentationAt
        canonicalOldVisit) :=
  rfl

theorem thirdState_uses_generated_contributionMergeRoot : HEq
    (sourceGeneratedRuntimeInquiryCoordinateAt jointRuntime 2).1.state.base.root
    generatedContributionMergeAction.target.targetRoot :=
  HEq.rfl

def thirdTick := jointRuntime.tickAt 2

@[simp] theorem thirdTick_resolution_is_contributionCapacityCut :
    thirdTick.resolution =
      .actualAction
        (generatedContributionCapacityCutActionAt canonicalOldVisit) :=
  rfl

@[simp] theorem thirdTick_resolutionKind_is_actualAction :
    thirdTick.resolutionKind = .actualAction := by
  rw [SourceNativeInquiryRuntime.ExactActivatedInquiryOccurrenceAt.resolutionKind]
  rw [thirdTick_resolution_is_contributionCapacityCut]
  rfl

theorem contributionCapacityCutResumption :
    SourceNativeInquiryRuntime.SequentialActualActionResumptionAt
      (generatedContributionCapacityCutActionAt canonicalOldVisit)
      jointRuntime 2 where
  contains_action := by
    rw [thirdTick_resolution_is_contributionCapacityCut]
    exact HEq.rfl

theorem thirdTick_next_preserves_contributionCapacityRoot : HEq
    (processPresentation .contributionCapacityFailure).state.base.root
    (generatedContributionCapacityCutActionAt
      canonicalOldVisit).target.targetRoot :=
  thirdTick.next_preservesGeneratedLivingLaw

@[simp] theorem fourthState_node_is_contributionCapacityFailure :
    (jointRuntime.stateAt 3).engine.node =
      .active (contributionCapacityFailurePresentationAt
        canonicalOldVisit) :=
  rfl

def fourthTick := jointRuntime.tickAt 3

@[simp] theorem fourthTick_resolution_is_contributionCapacitySelfU8 :
    fourthTick.resolution =
      .revised
        (contributionCapacityResidual rooted)
        (contributionCapacityU7Gate rooted)
        (contributionCapacityOperationalFailure rooted)
        (generatedContributionCapacityU8CoreAt canonicalOldVisit) :=
  rfl

theorem contributionCapacitySelfU8Resumption :
    SourceNativeInquiryRuntime.CofaceRealizationResumptionAt
      (generatedContributionCapacityU8CoreAt canonicalOldVisit)
      jointRuntime 3 where
  contains_core := by
    rw [fourthTick_resolution_is_contributionCapacitySelfU8]
    exact HEq.rfl

theorem fourthTick_next_preserves_contributionCapacityU8Root : HEq
    (processPresentation .contributionCapacityRevisedAnswer).state.base.root
    (generatedContributionCapacityU8CoreAt
      canonicalOldVisit).revision.generate.newLivingRoot :=
  fourthTick.next_preservesGeneratedLivingLaw

@[simp] theorem fifthState_node_is_contributionCapacityRevised :
    (jointRuntime.stateAt 4).engine.node =
      .active (contributionCapacityU8TargetPresentationAt
        canonicalOldVisit 0) :=
  rfl

def fifthTick := jointRuntime.tickAt 4

@[simp] theorem fifthTick_is_generated_selfU8_target_answer :
    fifthTick.resolution =
      .directlyAnswered
        (contributionCapacityU8AnswerFaceAt canonicalOldVisit 0)
        (contributionCapacityU8AnswerConsumerAt canonicalOldVisit 0) :=
  rfl

@[simp] theorem sixthState_node_is_contributionCapacityReopeningAction :
    (jointRuntime.stateAt 5).engine.node =
      .active (contributionCapacityReopeningActionPresentationAt
        canonicalOldVisit 1) :=
  rfl

def sixthTick := jointRuntime.tickAt 5

@[simp] theorem sixthTick_resolution_is_contributionCapacityReopening :
    sixthTick.resolution =
      .actualAction
        (generatedContributionCapacityReopeningActionAt canonicalOldVisit 1) :=
  rfl

@[simp] theorem sixthTick_resolutionKind_is_actualAction :
    sixthTick.resolutionKind = .actualAction := by
  rw [SourceNativeInquiryRuntime.ExactActivatedInquiryOccurrenceAt.resolutionKind]
  rw [sixthTick_resolution_is_contributionCapacityReopening]
  rfl

theorem contributionCapacityReopeningResumption :
    SourceNativeInquiryRuntime.SequentialActualActionResumptionAt
      (generatedContributionCapacityReopeningActionAt canonicalOldVisit 1)
      jointRuntime 5 where
  contains_action := by
    rw [sixthTick_resolution_is_contributionCapacityReopening]
    exact HEq.rfl

theorem sixthTick_next_preserves_contributionCapacityReopeningRoot : HEq
    (processPresentation (.contributionCapacityReopened 0)).state.base.root
    (generatedContributionCapacityReopeningActionAt
      canonicalOldVisit 1).target.targetRoot :=
  sixthTick.next_preservesGeneratedLivingLaw

@[simp] theorem seventhState_node_is_contributionCapacityReopened :
    (jointRuntime.stateAt 6).engine.node =
      .active (contributionCapacityReopenedPresentationAt
        canonicalOldVisit 1 0) :=
  rfl

def seventhTick := jointRuntime.tickAt 6

@[simp] theorem seventhTick_is_generated_reopening_target_answer :
    seventhTick.resolution =
      .directlyAnswered
        (contributionCapacityReopenedAnswerFaceAt canonicalOldVisit 1 0)
        (contributionCapacityReopenedAnswerConsumerAt canonicalOldVisit 1 0) :=
  rfl

@[simp] theorem eighthState_node_is_next_contributionCapacityReopened :
    (jointRuntime.stateAt 7).engine.node =
      .active (contributionCapacityReopenedPresentationAt
        canonicalOldVisit 1 1) :=
  rfl

def eighthTick := jointRuntime.tickAt 7

@[simp] theorem eighthTick_is_next_generated_reopening_target_answer :
    eighthTick.resolution =
      .directlyAnswered
        (contributionCapacityReopenedAnswerFaceAt canonicalOldVisit 1 1)
        (contributionCapacityReopenedAnswerConsumerAt canonicalOldVisit 1 1) :=
  rfl

@[simp] theorem ninthState_node_is_contributionCapacitySettlementAction :
    (jointRuntime.stateAt 8).engine.node =
      .active (contributionCapacitySettlementActionPresentationAt
        canonicalOldVisit 1) :=
  rfl

def ninthTick := jointRuntime.tickAt 8

@[simp] theorem ninthTick_resolution_is_contributionCapacitySettlement :
    ninthTick.resolution =
      .actualAction
        (generatedContributionCapacitySettlementActionAt canonicalOldVisit 1) :=
  rfl

@[simp] theorem ninthTick_resolutionKind_is_actualAction :
    ninthTick.resolutionKind = .actualAction := by
  rw [SourceNativeInquiryRuntime.ExactActivatedInquiryOccurrenceAt.resolutionKind]
  rw [ninthTick_resolution_is_contributionCapacitySettlement]
  rfl

theorem contributionCapacitySettlementResumption :
    SourceNativeInquiryRuntime.SequentialActualActionResumptionAt
      (generatedContributionCapacitySettlementActionAt canonicalOldVisit 1)
      jointRuntime 8 where
  contains_action := by
    rw [ninthTick_resolution_is_contributionCapacitySettlement]
    exact HEq.rfl

theorem ninthTick_next_preserves_contributionCapacitySettlementRoot : HEq
    (processPresentation .contributionCapacitySettlementTerminal).state.base.root
    (generatedContributionCapacitySettlementActionAt
      canonicalOldVisit 1).target.targetRoot :=
  ninthTick.next_preservesGeneratedLivingLaw

@[simp] theorem tenthState_node_is_contributionCapacitySettlementTerminal :
    (jointRuntime.stateAt 9).engine.node =
      .active (contributionCapacitySettlementTerminalPresentationAt
        canonicalOldVisit 1) :=
  rfl

def tenthTick := jointRuntime.tickAt 9

@[simp] theorem tenthTick_is_generated_settlement_terminal_answer :
    tenthTick.resolution =
      .directlyAnswered
        (contributionCapacitySettlementTerminalAnswerFaceAt
          canonicalOldVisit 1)
        (contributionCapacitySettlementTerminalAnswerConsumerAt
          canonicalOldVisit 1) :=
  rfl

def tenthTickExactFaithfulTerminal :
    SourceFaithfulTerminalOccurrenceAt
      (CanonicalContributionCapacitySettlementRootAt
        canonicalOldVisit 1).source.base
      ((CanonicalContributionCapacitySettlementRootAt canonicalOldVisit 1
        ).emitted true) :=
  contributionCapacitySettlementExactTerminal canonicalOldVisit 1
    (contributionCapacitySettlementActionExactSourceEventAt
      canonicalOldVisit 1)

@[simp] theorem eleventhState_node_is_contributionCapacitySettlementSurvivor :
    (jointRuntime.stateAt 10).engine.node =
      .active (contributionCapacitySettlementSurvivorPresentationAt
        canonicalOldVisit 1 0) :=
  rfl

def eleventhTick := jointRuntime.tickAt 10

@[simp] theorem eleventhTick_is_first_survivor_answer :
    eleventhTick.resolution =
      .directlyAnswered
        (contributionCapacitySettlementSurvivorAnswerFaceAt
          canonicalOldVisit 1 0)
        (contributionCapacitySettlementSurvivorAnswerConsumerAt
          canonicalOldVisit 1 0) :=
  rfl

@[simp] theorem twelfthState_node_is_next_contributionCapacitySettlementSurvivor :
    (jointRuntime.stateAt 11).engine.node =
      .active (contributionCapacitySettlementSurvivorPresentationAt
        canonicalOldVisit 1 1) :=
  rfl

def twelfthTick := jointRuntime.tickAt 11

@[simp] theorem twelfthTick_is_next_survivor_answer :
    twelfthTick.resolution =
      .directlyAnswered
        (contributionCapacitySettlementSurvivorAnswerFaceAt
          canonicalOldVisit 1 1)
        (contributionCapacitySettlementSurvivorAnswerConsumerAt
          canonicalOldVisit 1 1) :=
  rfl

@[simp] theorem firstTick_core_row_is_installedRenewalRow :
    jointCore.face.rootEntry = installedRenewal.payload.sourceEntry :=
  jointCore_rootEntry_eq_installedRenewal

theorem runtimeSplice : SourceInstalledRenewalRuntimeSpliceAt
    installedRenewal jointRuntime 0 where
  sameRoot := HEq.rfl
  sameVisit := HEq.rfl
  sameRow := HEq.rfl
  sameOccurrence := HEq.rfl

theorem runtimeSplice_sameRow : HEq
    ((sourceGeneratedRuntimeInquiryCoordinateAt jointRuntime 0).1.state.base.entryAt
      (sourceGeneratedRuntimeInquiryCoordinateAt jointRuntime 0).2)
    installedRenewal.payload.sourceEntry :=
  runtimeSplice.sameRow

theorem runtimeSplice_sameOccurrence : HEq
    ((sourceGeneratedRuntimeInquiryCoordinateAt jointRuntime 0).1.state.base.root
      |>.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
        (sourceGeneratedRuntimeInquiryCoordinateAt jointRuntime 0).1.state.base.visit)
    (jointRoot.toAuthoritativeRoot.toLedgerRoot
      |>.exactTemporalCausalEventAt jointVisit) :=
  runtimeSplice.sameOccurrence

def legislation : ProofCarryingLegislationAt
    installedRenewal jointRuntime 0 runtimeSplice :=
  sourceGeneratedProofCarryingLegislation
    installedRenewal jointRuntime 0 runtimeSplice

def legislationConsumer := legislation.independentConsumer

def dichotomy : SourceGeneratedInstitutionalDichotomyAt jointRuntime 0 :=
  legislation.dichotomy

def revolutionaryTick : SourceGeneratedRevolutionaryTickAt jointRuntime 0 :=
  (dichotomy.revolutionaryTick?).get (by rfl)

@[simp] theorem revolutionaryTick_core_eq_jointCore :
    revolutionaryTick.core = jointCore :=
  rfl

end
end M9ProofCarryingRenewalInquiryRuntime
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M9ProofCarryingRenewalInquiryRuntime.firstTick_resolution_is_jointCore
#print axioms SaturationMonoid.ProcessGame.Society.M9ProofCarryingRenewalInquiryRuntime.secondTick_resolution_is_contributionMerge
#print axioms SaturationMonoid.ProcessGame.Society.M9ProofCarryingRenewalInquiryRuntime.contributionMergeResumption
#print axioms SaturationMonoid.ProcessGame.Society.M9ProofCarryingRenewalInquiryRuntime.secondTick_next_preserves_contributionMergeRoot
#print axioms SaturationMonoid.ProcessGame.Society.M9ProofCarryingRenewalInquiryRuntime.thirdTick_resolution_is_contributionCapacityCut
#print axioms SaturationMonoid.ProcessGame.Society.M9ProofCarryingRenewalInquiryRuntime.fourthTick_resolution_is_contributionCapacitySelfU8
#print axioms SaturationMonoid.ProcessGame.Society.M9ProofCarryingRenewalInquiryRuntime.fifthTick_is_generated_selfU8_target_answer
#print axioms SaturationMonoid.ProcessGame.Society.M9ProofCarryingRenewalInquiryRuntime.sixthTick_resolution_is_contributionCapacityReopening
#print axioms SaturationMonoid.ProcessGame.Society.M9ProofCarryingRenewalInquiryRuntime.contributionCapacityReopeningResumption
#print axioms SaturationMonoid.ProcessGame.Society.M9ProofCarryingRenewalInquiryRuntime.seventhTick_is_generated_reopening_target_answer
#print axioms SaturationMonoid.ProcessGame.Society.M9ProofCarryingRenewalInquiryRuntime.eighthTick_is_next_generated_reopening_target_answer
#print axioms SaturationMonoid.ProcessGame.Society.M9ProofCarryingRenewalInquiryRuntime.ninthTick_resolution_is_contributionCapacitySettlement
#print axioms SaturationMonoid.ProcessGame.Society.M9ProofCarryingRenewalInquiryRuntime.contributionCapacitySettlementResumption
#print axioms SaturationMonoid.ProcessGame.Society.M9ProofCarryingRenewalInquiryRuntime.ninthTick_next_preserves_contributionCapacitySettlementRoot
#print axioms SaturationMonoid.ProcessGame.Society.M9ProofCarryingRenewalInquiryRuntime.tenthTick_is_generated_settlement_terminal_answer
#print axioms SaturationMonoid.ProcessGame.Society.M9ProofCarryingRenewalInquiryRuntime.tenthTickExactFaithfulTerminal
#print axioms SaturationMonoid.ProcessGame.Society.M9ProofCarryingRenewalInquiryRuntime.eleventhTick_is_first_survivor_answer
#print axioms SaturationMonoid.ProcessGame.Society.M9ProofCarryingRenewalInquiryRuntime.twelfthTick_is_next_survivor_answer
