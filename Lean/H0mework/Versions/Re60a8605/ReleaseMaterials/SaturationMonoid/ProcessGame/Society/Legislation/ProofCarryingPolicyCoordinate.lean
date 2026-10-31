import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Legislation.ProofCarryingLegislation

/-!
# Proof-carrying legislation with an exact policy coordinate

The existing proof-carrying legislation seal owns renewal, lifecycle,
residual, observer-kernel, inquiry branch, whole-ledger, and generated-next
authority.  A domain policy may join it only when another source-installed
renewal coordinate belongs to the same root and temporal visit and its row and
successor commute with the base PCL coordinate.

This module adds no policy content, branch selector, court, root, ledger,
registry, repair, effectiveness verdict, revision target, or completed
future.  It is the generic multi-coordinate splice later consumed by UBI,
election, money, relation, or AI domain faces.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Legislation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Renewal Settlement Observer
open ConstructiveRoot.RootInquiryCompletion

universe u

/-! ## Base PCL coordinate -/

variable {LocalSource LocalState Seed : Type u}
variable {occurrenceOf : LocalSource → RootedAccountedUnfolding LocalState}
variable {game : SaturationMonoid.ProcessGame occurrenceOf}
variable {SeedAt : LocalSource → LocalState → Seed → Prop}

variable {N : WorldRelationNetwork.{u}}
variable {RootV : ConstructiveRoot.Vocabulary.{u}}
variable {root : SourceNativeLivingRootClosure N RootV}

variable {W : ResponsibilityLifecycle.Vocabulary.{u}}
variable {P : NativeResponsibilityProcess W}
variable {Occurrence Visible AuthorityResidual : Type u}
variable {observer : AuthorityObserver Occurrence Visible AuthorityResidual}
variable {LocalConsumerAt LocalLifecycleAt DispositionAt :
  SourceSeed occurrenceOf Seed SeedAt game.source → Type u}

variable {recognition :
  SourceNativeProofCarryingRenewalRecognitionAt root P observer
    LocalConsumerAt LocalLifecycleAt DispositionAt}
variable {visit : SourceNativeTemporalVisitAt
  root.toAuthoritativeRoot.toLedgerRoot}
variable {installed : SourceInstalledRenewalAt recognition visit}

variable {process : SourceNativeInquiryEngineProcess.{u}}
variable {runtime : SourceNativeInquiryRuntime process}
variable {depth : Nat}
variable {splice :
  SourceInstalledRenewalRuntimeSpliceAt installed runtime depth}
variable {legislation :
  ProofCarryingLegislationAt installed runtime depth splice}

/-! ## Secondary policy coordinate -/

variable {PolicySource PolicyState PolicySeed : Type u}
variable {policyOccurrenceOf :
  PolicySource → RootedAccountedUnfolding PolicyState}
variable {policyGame : SaturationMonoid.ProcessGame policyOccurrenceOf}
variable {PolicySeedAt :
  PolicySource → PolicyState → PolicySeed → Prop}
variable {PolicyConsumerAt PolicyDispositionAt :
  SourceSeed policyOccurrenceOf PolicySeed PolicySeedAt policyGame.source →
    Type u}
variable {policyRecognition : SourceNativeRenewalRecognitionAt root policyGame
  PolicySeed PolicySeedAt PolicyConsumerAt PolicyDispositionAt}
variable {policyInstalled :
  SourceInstalledRenewalAt policyRecognition visit}

/-- Exact root-row coordination between the pre-emitter PCL renewal and one
additional policy renewal.  Shared root and visit are type indices; only the
source entry, generated row, and successor equations remain to prove. -/
structure SourceInstalledPolicyCoordinateAt
    (installed : SourceInstalledRenewalAt recognition visit)
    (policyInstalled : SourceInstalledRenewalAt policyRecognition visit) :
    Prop where
  sourceEntry_eq :
    installed.payload.sourceEntry = policyInstalled.payload.sourceEntry
  selectedRow_heq :
    HEq installed.payload.selectedRow policyInstalled.payload.selectedRow
  successor_heq :
    HEq installed.payload.successor policyInstalled.payload.successor

variable {coordinate :
  SourceInstalledPolicyCoordinateAt installed policyInstalled}

/-- Zero-choice legislation extension.  The empty private constructor keeps
all authority in the existing PCL, policy installation, and exact coordinate
indices. -/
structure ProofCarryingPolicyLegislationAt
    (legislation :
      ProofCarryingLegislationAt installed runtime depth splice)
    (policyInstalled : SourceInstalledRenewalAt policyRecognition visit)
    (_coordinate :
      SourceInstalledPolicyCoordinateAt installed policyInstalled) :
    Type (u + 14) where
  private mk ::

/-- Sole generic producer.  It accepts no policy meaning or outcome. -/
def sourceGeneratedProofCarryingPolicyLegislation
    (legislation :
      ProofCarryingLegislationAt installed runtime depth splice)
    (policyInstalled : SourceInstalledRenewalAt policyRecognition visit)
    (coordinate :
      SourceInstalledPolicyCoordinateAt installed policyInstalled) :
    ProofCarryingPolicyLegislationAt legislation policyInstalled coordinate :=
  ⟨⟩

namespace ProofCarryingPolicyLegislationAt

variable (policyLegislation :
  ProofCarryingPolicyLegislationAt legislation policyInstalled coordinate)

/-- Independent base PCL consumer. -/
def baseConsumer : ProofCarryingLegislationConsumerAt legislation := by
  cases policyLegislation
  exact legislation.independentConsumer

/-- Exact source seed selected by the policy coordinate. -/
def policySeed :
    SourceSeed policyOccurrenceOf PolicySeed PolicySeedAt policyGame.source := by
  cases policyLegislation
  exact policyInstalled.payload.sourceSeed

/-- Pre-emitter policy consumer and disposition. -/
def policyConsumer : PolicyConsumerAt policyLegislation.policySeed := by
  cases policyLegislation
  exact policyInstalled.payload.consumer

def policyDisposition : PolicyDispositionAt policyLegislation.policySeed := by
  cases policyLegislation
  exact policyInstalled.payload.disposition

/-- Independent operational consumer and exact whole-ledger write-back of
the policy coordinate. -/
def policyRootConsumer :
    RenewalResponsibilityConsumerAt policyInstalled.operationalAuthority := by
  cases policyLegislation
  exact policyInstalled.rootResponsibilityConsumer

def policyWholeLedgerWriteBack :
    SourceNativeLedgerEvolutionAt
      root.toAuthoritativeRoot.toLedgerRoot.source.source
      (root.toAuthoritativeRoot.toLedgerRoot
        |>.generatedAtTemporalVisit visit).occurrence := by
  cases policyLegislation
  exact (root.toAuthoritativeRoot.toLedgerRoot
    |>.generatedAtTemporalVisit visit).wholeLedgerWriteBack

theorem policyRootAnswerAndNext_factorizes
    (policyLegislation :
      ProofCarryingPolicyLegislationAt legislation policyInstalled coordinate) :
    policyInstalled.RootAnswerAndNextFactorizes := by
  cases policyLegislation
  exact policyInstalled.rootAnswerAndNext_factorizes

theorem sourceEntry_eq_base
    (policyLegislation :
      ProofCarryingPolicyLegislationAt legislation policyInstalled coordinate) :
    policyInstalled.payload.sourceEntry = installed.payload.sourceEntry := by
  cases policyLegislation
  exact coordinate.sourceEntry_eq.symm

theorem selectedRow_heq_base
    (policyLegislation :
      ProofCarryingPolicyLegislationAt legislation policyInstalled coordinate) :
    HEq policyInstalled.payload.selectedRow installed.payload.selectedRow := by
  cases policyLegislation
  exact coordinate.selectedRow_heq.symm

theorem successor_heq_base
    (policyLegislation :
      ProofCarryingPolicyLegislationAt legislation policyInstalled coordinate) :
    HEq policyInstalled.payload.successor installed.payload.successor := by
  cases policyLegislation
  exact coordinate.successor_heq.symm

/-- The secondary policy cannot choose a different inquiry branch or next;
both remain readouts of the base PCL's exact runtime tick. -/
def branchKind
    (policyLegislation :
      ProofCarryingPolicyLegislationAt legislation policyInstalled coordinate) :
    Revision.SourceGeneratedInstitutionalRevisionKind := by
  cases policyLegislation
  exact legislation.revisionKind

def generatedNext
    (policyLegislation :
      ProofCarryingPolicyLegislationAt legislation policyInstalled coordinate) :
    AnyAuthoritativeRootCurrent.{u} := by
  cases policyLegislation
  exact legislation.generatedNext

def revolutionaryConsumption
    (policyLegislation :
      ProofCarryingPolicyLegislationAt legislation policyInstalled coordinate) := by
  cases policyLegislation
  exact legislation.revolutionaryConsumption?

end ProofCarryingPolicyLegislationAt

/-! ## Independent consumer mouth -/

structure ProofCarryingPolicyLegislationConsumerAt
    (policyLegislation :
      ProofCarryingPolicyLegislationAt legislation policyInstalled coordinate) :
    Type (u + 14) where
  private mk ::
  baseConsumer : ProofCarryingLegislationConsumerAt legislation
  policySeed :
    SourceSeed policyOccurrenceOf PolicySeed PolicySeedAt policyGame.source
  policySeed_eq : policySeed = policyInstalled.payload.sourceSeed
  policyConsumer : PolicyConsumerAt policySeed
  policyDisposition : PolicyDispositionAt policySeed
  policyRootConsumer :
    RenewalResponsibilityConsumerAt policyInstalled.operationalAuthority
  sourceEntry_eq :
    policyInstalled.payload.sourceEntry = installed.payload.sourceEntry
  selectedRow_heq :
    HEq policyInstalled.payload.selectedRow installed.payload.selectedRow
  successor_heq :
    HEq policyInstalled.payload.successor installed.payload.successor
  policyWholeLedgerWriteBack :
    SourceNativeLedgerEvolutionAt
      root.toAuthoritativeRoot.toLedgerRoot.source.source
      (root.toAuthoritativeRoot.toLedgerRoot
        |>.generatedAtTemporalVisit visit).occurrence
  policyRootFactorization : policyInstalled.RootAnswerAndNextFactorizes
  branchKind : Revision.SourceGeneratedInstitutionalRevisionKind
  generatedNext : AnyAuthoritativeRootCurrent.{u}
  generatedNext_eq : generatedNext = legislation.generatedNext
  revolutionaryConsumption :
    Option (Sigma fun revolution :
      Revision.SourceGeneratedRevolutionaryTickAt runtime depth =>
        ProofCarryingRevolutionaryConsumptionAt legislation revolution)

/-- Direct consumer generated only from the exact legislation extension. -/
def ProofCarryingPolicyLegislationAt.independentConsumer
    (policyLegislation :
      ProofCarryingPolicyLegislationAt legislation policyInstalled coordinate) :
    ProofCarryingPolicyLegislationConsumerAt policyLegislation where
  baseConsumer := policyLegislation.baseConsumer
  policySeed := policyLegislation.policySeed
  policySeed_eq := rfl
  policyConsumer := policyLegislation.policyConsumer
  policyDisposition := policyLegislation.policyDisposition
  policyRootConsumer := policyLegislation.policyRootConsumer
  sourceEntry_eq := policyLegislation.sourceEntry_eq_base
  selectedRow_heq := policyLegislation.selectedRow_heq_base
  successor_heq := policyLegislation.successor_heq_base
  policyWholeLedgerWriteBack := policyLegislation.policyWholeLedgerWriteBack
  policyRootFactorization :=
    policyLegislation.policyRootAnswerAndNext_factorizes
  branchKind := policyLegislation.branchKind
  generatedNext := policyLegislation.generatedNext
  generatedNext_eq := rfl
  revolutionaryConsumption := policyLegislation.revolutionaryConsumption

end Legislation
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.Legislation.sourceGeneratedProofCarryingPolicyLegislation
#print axioms SaturationMonoid.ProcessGame.Society.Legislation.ProofCarryingPolicyLegislationAt.independentConsumer
