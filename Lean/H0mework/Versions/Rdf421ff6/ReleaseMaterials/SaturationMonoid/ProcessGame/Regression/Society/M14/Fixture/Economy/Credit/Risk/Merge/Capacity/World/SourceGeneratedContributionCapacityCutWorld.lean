import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.SourceGeneratedContributionMergeWorld
import H0mework.Foundation.Semantics.TheoryEvolution

/-!
# Source-generated contribution-capacity cut world

The already generated contribution-merge target is admitted conservatively
at cut phase `false`.  The unique actual cut target retains exactly the same
contribution and obstruction responsibilities while spending the
contribution's live progress budget from `1` to `0`.

Non-emitted representation faces at cut phase `true` reuse their old open
fibres solely to keep the target-world U7 calculus total.  The source emitter
defined downstream selects only the conservative initial support and the
unique two-row cut target.  No pool, capacity registry, participant, bearer,
claim, currency or completed future is introduced.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityCutWorld

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ObstructionGeneratedMinimalCoface
open M14SourceGeneratedLossAllocationWorld
open M14SourceGeneratedContributionMergeWorld

variable
    {OldV : ConstructiveRoot.Vocabulary}
    {oldWorld : SourceNativeAuthoritativeRootClosure
      M14SourceGeneratedLossAllocationWorld.OldN OldV}
    {oldVisit : SourceNativeTemporalVisitAt oldWorld.toLedgerRoot}
    {U7 : U7ProducerCalculus M14SourceGeneratedLossAllocationWorld.OldN}
    {oldTheory : TheoryState M14SourceGeneratedLossAllocationWorld.OldN}
    {support : M14SourceGeneratedLossAllocationWorld.OldN.Support}
    {obstruction :
      M14SourceGeneratedLossAllocationWorld.OldN.ObstructionAt support}
    {failure : ActualExpressibilityFailure oldTheory obstruction}

local notation "RootedFailure" => RootedActualExpressibilityFailureAt
  oldWorld oldVisit U7 failure

abbrev OldN (rooted : RootedFailure) :=
  M14SourceGeneratedContributionMergeWorld.TargetN rooted

abbrev CapacityCutSupport (rooted : RootedFailure) :=
  (OldN rooted).Support × Bool

abbrev CapacityCutResponsibility (rooted : RootedFailure) :=
  (OldN rooted).Responsibility

abbrev CapacityCutClaim (rooted : RootedFailure) :=
  (OldN rooted).Claim

/-- The capacity action starts at the actual two-row merge target. -/
def contributionCapacityCutSourceSupport (rooted : RootedFailure) :
    (OldN rooted).Support :=
  contributionMergeTargetSupport rooted

def contributionCapacityCutInitialSupport (rooted : RootedFailure) :
    CapacityCutSupport rooted :=
  (contributionCapacityCutSourceSupport rooted, false)

def contributionCapacityCutTargetSupport (rooted : RootedFailure) :
    CapacityCutSupport rooted :=
  (contributionCapacityCutSourceSupport rooted, true)

/-- Exact residual generated only at the actual capacity-cut target.  The
constructor carries no information; its support index supplies all source
identity. -/
inductive SourceGeneratedContributionCapacityResidualAt
    (rooted : RootedFailure) : CapacityCutSupport rooted → Type
  | exhausted : SourceGeneratedContributionCapacityResidualAt rooted
      (contributionCapacityCutTargetSupport rooted)

/-- At cut phase `false` every existing merge-world row is retained.  At
cut phase `true`, only the unique actual merge target is replaced by the
two equality-restricted zero-budget rows; all other total-world faces are
conservative representation support and are never emitted. -/
def contributionCapacityCutOpenAt (rooted : RootedFailure) :
    CapacityCutSupport rooted → CapacityCutResponsibility rooted → Type
  | (oldSupport, false), responsibility =>
      (OldN rooted).OpenAt oldSupport responsibility
  | (((.inl oldSupport, lossPhase), mergePhase), true), responsibility =>
      (OldN rooted).OpenAt
        ((.inl oldSupport, lossPhase), mergePhase) responsibility
  | (((.inr direction, false), mergePhase), true), responsibility =>
      (OldN rooted).OpenAt
        ((.inr direction, false), mergePhase) responsibility
  | (((.inr direction, true), false), true), responsibility =>
      (OldN rooted).OpenAt
        ((.inr direction, true), false) responsibility
  | (oldSupport@((.inr _, true), true), true), responsibility =>
      PLift (oldSupport = contributionCapacityCutSourceSupport rooted ∧
          responsibility = contributionResponsibility rooted) ⊕
        PLift (oldSupport = contributionCapacityCutSourceSupport rooted ∧
          responsibility = contributionObstructionResponsibility rooted)

def contributionCapacityCutOpenClaimAt (rooted : RootedFailure) :
    {indexedSupport : CapacityCutSupport rooted} →
    {responsibility : CapacityCutResponsibility rooted} →
    contributionCapacityCutOpenAt rooted indexedSupport responsibility →
      CapacityCutClaim rooted
  | (_oldSupport, false), _responsibility, isOpen =>
      (OldN rooted).openClaimAt isOpen
  | (((.inl _oldSupport, _lossPhase), _mergePhase), true),
      _responsibility, isOpen =>
      (OldN rooted).openClaimAt isOpen
  | (((.inr _direction, false), _mergePhase), true),
      _responsibility, isOpen =>
      (OldN rooted).openClaimAt isOpen
  | (((.inr _direction, true), false), true),
      _responsibility, isOpen =>
      (OldN rooted).openClaimAt isOpen
  | (((.inr _direction, true), true), true), _responsibility, .inl _ =>
      contributionClaim rooted
  | (((.inr _direction, true), true), true), _responsibility, .inr _ =>
      contributionObstructionClaim rooted

def contributionCapacityCutOpenProgressBudgetAt
    (rooted : RootedFailure) :
    {indexedSupport : CapacityCutSupport rooted} →
    {responsibility : CapacityCutResponsibility rooted} →
    contributionCapacityCutOpenAt rooted indexedSupport responsibility → Nat
  | (_oldSupport, false), _responsibility, isOpen =>
      (OldN rooted).openProgressBudgetAt isOpen
  | (((.inl _oldSupport, _lossPhase), _mergePhase), true),
      _responsibility, isOpen =>
      (OldN rooted).openProgressBudgetAt isOpen
  | (((.inr _direction, false), _mergePhase), true),
      _responsibility, isOpen =>
      (OldN rooted).openProgressBudgetAt isOpen
  | (((.inr _direction, true), false), true),
      _responsibility, isOpen =>
      (OldN rooted).openProgressBudgetAt isOpen
  | (((.inr _direction, true), true), true), _responsibility, .inl _ => 0
  | (((.inr _direction, true), true), true), _responsibility, .inr _ => 0

def contributionCapacityCutWorld
    (rooted : RootedFailure) : WorldRelationNetwork where
  Support := CapacityCutSupport rooted
  Anchor := (OldN rooted).Anchor
  Incidence := (OldN rooted).Incidence
  Lineage := (OldN rooted).Lineage
  Responsibility := CapacityCutResponsibility rooted
  Claim := CapacityCutClaim rooted
  anchorAt := fun indexedSupport =>
    (OldN rooted).anchorAt indexedSupport.1
  incidenceAt := fun indexedSupport =>
    (OldN rooted).incidenceAt indexedSupport.1
  lineageAt := fun indexedSupport =>
    (OldN rooted).lineageAt indexedSupport.1
  OpenAt := contributionCapacityCutOpenAt rooted
  openClaimAt := contributionCapacityCutOpenClaimAt rooted
  openProgressBudgetAt := contributionCapacityCutOpenProgressBudgetAt rooted
  HoldsAt := fun indexedSupport claim =>
    (OldN rooted).HoldsAt indexedSupport.1 claim
  ObstructionAt := fun indexedSupport =>
    (OldN rooted).ObstructionAt indexedSupport.1 ⊕
      SourceGeneratedContributionCapacityResidualAt rooted indexedSupport
  obstructionClaim := fun indexedObstruction => match indexedObstruction with
    | .inl oldObstruction => (OldN rooted).obstructionClaim oldObstruction
    | .inr _ => contributionObstructionClaim rooted
  SemanticChangeAt := fun indexedSupport sourceClaim targetClaim =>
    (OldN rooted).SemanticChangeAt indexedSupport.1 sourceClaim targetClaim
  DispositionAt := fun indexedSupport kind =>
    (OldN rooted).DispositionAt indexedSupport.1 kind

abbrev CutN (rooted : RootedFailure) :=
  contributionCapacityCutWorld rooted

/-! ## Conservative source ingress -/

def contributionCapacityCutTranslation (rooted : RootedFailure) :
    TypedSemanticWorldNetworkTranslationAt (OldN rooted) (CutN rooted) where
  support :=
    { forward := fun oldSupport => (oldSupport, false)
      backward := Prod.fst
      backward_forward := fun _ => rfl }
  anchor :=
    { forward := id
      backward := id
      backward_forward := fun _ => rfl }
  incidence :=
    { forward := id
      backward := id
      backward_forward := fun _ => rfl }
  lineage :=
    { forward := id
      backward := id
      backward_forward := fun _ => rfl }
  responsibility :=
    { forward := id
      backward := id
      backward_forward := fun _ => rfl }
  claim :=
    { forward := id
      backward := id
      backward_forward := fun _ => rfl }
  anchor_commutes := fun _ => rfl
  incidence_commutes := fun _ => rfl
  lineage_commutes := fun _ => rfl
  oldOpenLedger := fun _oldSupport =>
    { forward := fun oldEntry => ⟨oldEntry.1, oldEntry.2⟩
      backward := fun targetEntry => ⟨targetEntry.1, targetEntry.2⟩
      backward_forward := fun _ => rfl }
  oldOpenClaim_commutes := fun _ _ => rfl
  oldOpenProgressBudget_commutes := fun _ _ => rfl
  oldHoldsSurvives := fun _ _ proof => proof
  oldDispositionSurvives := fun _ _ proof => proof

def contributionCapacityCutInitialLedger (rooted : RootedFailure) :
    CompleteLiveLedgerAt (CutN rooted) :=
  ⟨contributionCapacityCutInitialSupport rooted⟩

def contributionCapacityCutTargetLedger (rooted : RootedFailure) :
    CompleteLiveLedgerAt (CutN rooted) :=
  ⟨contributionCapacityCutTargetSupport rooted⟩

def contributionCapacityCutInitialEntry
    (rooted : RootedFailure)
    (entry : (contributionMergeTargetLedger rooted).Entry) :
    (contributionCapacityCutInitialLedger rooted).Entry :=
  ⟨entry.1, entry.2⟩

def contributionCapacityCutTargetContribution
    (rooted : RootedFailure) :
    (contributionCapacityCutTargetLedger rooted).Entry :=
  ⟨contributionResponsibility rooted,
    .inl (PLift.up ⟨rfl, rfl⟩)⟩

def contributionCapacityCutTargetObstruction
    (rooted : RootedFailure) :
    (contributionCapacityCutTargetLedger rooted).Entry :=
  ⟨contributionObstructionResponsibility rooted,
    .inr (PLift.up ⟨rfl, rfl⟩)⟩

theorem contributionCapacityCut_initialLedger_noFresh
    (rooted : RootedFailure)
    (targetEntry : (contributionCapacityCutInitialLedger rooted).Entry) :
    Nonempty (Sigma fun oldEntry :
      (contributionMergeTargetLedger rooted).Entry =>
      PLift (contributionCapacityCutInitialEntry rooted oldEntry =
        targetEntry)) := by
  rcases targetEntry with ⟨responsibility, isOpen⟩
  exact ⟨⟨⟨responsibility, isOpen⟩, PLift.up rfl⟩⟩

theorem contributionCapacityCutTargetEntry_cases
    (rooted : RootedFailure)
    (entry : (contributionCapacityCutTargetLedger rooted).Entry) :
    entry = contributionCapacityCutTargetContribution rooted ∨
      entry = contributionCapacityCutTargetObstruction rooted := by
  rcases entry with ⟨responsibility, isOpen⟩
  rcases isOpen with contribution | obstruction
  · rcases contribution.down with ⟨support_eq, responsibility_eq⟩
    cases support_eq
    cases responsibility_eq
    exact .inl (by congr)
  · rcases obstruction.down with ⟨support_eq, responsibility_eq⟩
    cases support_eq
    cases responsibility_eq
    exact .inr (by congr)

theorem contributionCapacityCutTargetEntries_distinct
    (rooted : RootedFailure) :
    contributionCapacityCutTargetContribution rooted ≠
      contributionCapacityCutTargetObstruction rooted := by
  intro equality
  have responsibility_eq := congrArg Sigma.fst equality
  exact nomatch responsibility_eq

@[simp] theorem contributionCapacityCut_initialContribution_budget
    (rooted : RootedFailure) :
    (contributionCapacityCutInitialEntry rooted
      (mergedContributionEntry rooted)).progressBudget = 1 :=
  rfl

@[simp] theorem contributionCapacityCut_targetContribution_budget
    (rooted : RootedFailure) :
    (contributionCapacityCutTargetContribution rooted).progressBudget = 0 :=
  rfl

@[simp] theorem contributionCapacityCut_targetObstruction_budget
    (rooted : RootedFailure) :
    (contributionCapacityCutTargetObstruction rooted).progressBudget = 0 :=
  rfl

/-! ## Total representation inhabitant -/

def contributionCapacityCutDefaultEntryAt
    (rooted : RootedFailure) :
    (indexedSupport : (CutN rooted).Support) →
      OpenResponsibilityAt (CutN rooted) indexedSupport
  | (oldSupport, false) =>
      contributionMergeDefaultEntryAt rooted oldSupport
  | (((.inl oldSupport, lossPhase), mergePhase), true) =>
      contributionMergeDefaultEntryAt rooted
        ((.inl oldSupport, lossPhase), mergePhase)
  | (((.inr direction, false), mergePhase), true) =>
      contributionMergeDefaultEntryAt rooted
        ((.inr direction, false), mergePhase)
  | (((.inr direction, true), false), true) =>
      contributionMergeDefaultEntryAt rooted
        ((.inr direction, true), false)
  | (((.inr direction, true), true), true) => by
      cases direction
      exact contributionCapacityCutTargetContribution rooted

@[simp] theorem contributionCapacityCutDefaultEntryAt_target_exact
    (rooted : RootedFailure) :
    contributionCapacityCutDefaultEntryAt rooted
        (contributionCapacityCutTargetSupport rooted) =
      contributionCapacityCutTargetContribution rooted :=
  rfl

/-! ## Source-generated narrow operational theory -/

abbrev ContributionCapacityOperationalExpressionAt
    (rooted : RootedFailure) (_indexedSupport : (CutN rooted).Support) :=
  { claim : (CutN rooted).Claim //
    claim ≠ contributionObstructionClaim rooted }

def contributionCapacityOperationalTheory
    (rooted : RootedFailure) : TheoryState (CutN rooted) where
  inventory :=
    { Version := PUnit
      version := PUnit.unit
      Law := PEmpty
      RealizationAt := fun {support} indexedObstruction =>
        match indexedObstruction with
        | .inl oldObstruction =>
            (CutN rooted).HoldsAt support
              ((CutN rooted).obstructionClaim (.inl oldObstruction))
        | .inr _ => PEmpty
      RealizationWithoutAt := fun law => nomatch law }
  ExpressionAt := ContributionCapacityOperationalExpressionAt rooted
  denotes := Subtype.val
  TheoremAt := fun {support} expression =>
    (CutN rooted).HoldsAt support expression.1
  theoremPresentation := fun _ => ConstructivePresentation.refl _

def contributionCapacityOperationalTheory_rootSemantic
    (rooted : RootedFailure) :
    ConservativeTheoryTranslation
      (contributionCapacityOperationalTheory rooted)
      (TheoryState.rootSemantic (CutN rooted)) where
  compile := fun expression => expression.1
  commuting := fun _expression => rfl

def contributionCapacityResidual
    (rooted : RootedFailure) :
    (CutN rooted).ObstructionAt
      (contributionCapacityCutTargetSupport rooted) :=
  .inr .exhausted

@[simp] theorem contributionCapacityResidual_claim_exact
    (rooted : RootedFailure) :
    (CutN rooted).obstructionClaim
        (contributionCapacityResidual rooted) =
      contributionObstructionClaim rooted :=
  rfl

def contributionCapacityOperationalFailure
    (rooted : RootedFailure) :
    ActualExpressibilityFailure
      (contributionCapacityOperationalTheory rooted)
      (contributionCapacityResidual rooted) where
  notExpressible := by
    constructor
    rintro ⟨expression, denotes_eq⟩
    change ContributionCapacityOperationalExpressionAt rooted
      (contributionCapacityCutTargetSupport rooted) at expression
    exact expression.2 denotes_eq
  noLawfulRealization := by
    constructor
    intro realization
    exact nomatch realization

end
end M14SourceGeneratedContributionCapacityCutWorld
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityCutWorld.contributionCapacityCutTranslation
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityCutWorld.contributionCapacityCutTargetEntry_cases
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityCutWorld.contributionCapacityOperationalTheory_rootSemantic
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityCutWorld.contributionCapacityOperationalFailure
