import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Compiler.SourceGeneratedContributionCapacityCutRestructuring

/-!
# M14 source-generated contribution-capacity root

This root installs the capacity cut as the sole successor of the already
generated contribution-merge occurrence.  Its law surface is the narrower
operational theory: the first whole-ledger write spends the contribution
budget `1 -> 0`, preserves the obstruction row `0 -> 0`, and thereby exposes
the exact source-generated capacity residual to U7.

The root inventory contains only the whole-ledger lifecycle readout, the
inquiry token, and the exact failure token at the generated target.  It does
not install a revision, settlement, completed future, new bearer, or second
authority compiler.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityCutRoot

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open ObstructionGeneratedMinimalCoface
open M14SourceGeneratedLossAllocationMaterial
open M14SourceGeneratedLossAllocationWorld
open M14SourceGeneratedContributionMergeWorld
open M14SourceGeneratedContributionCapacityCutWorld
open M14SourceGeneratedContributionCapacityCutCompiler
open M14SourceGeneratedContributionCapacityCutLifecycle
open M14SourceGeneratedContributionCapacityCutRestructuring

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

/-! ## Operational U7 theory-audit surface -/

def contributionCapacityInquiryEntryAt
    (rooted : RootedFailure) :
    (current : (TargetV rooted).Current) →
      OpenResponsibilityAt (CutN rooted)
        (contributionCapacityCutSupportAt rooted current)
  | 0 => initialObstruction rooted
  | _ + 1 => contributionCapacityCutTargetObstruction rooted

@[simp] theorem contributionCapacityInquiryEntryAt_zero
    (rooted : RootedFailure) :
    contributionCapacityInquiryEntryAt rooted 0 = initialObstruction rooted :=
  rfl

@[simp] theorem contributionCapacityInquiryEntryAt_succ
    (rooted : RootedFailure) (current : Nat) :
    contributionCapacityInquiryEntryAt rooted (current + 1) =
      contributionCapacityCutTargetObstruction rooted :=
  rfl

def contributionCapacityU7
    (rooted : RootedFailure) : U7ProducerCalculus (CutN rooted) where
  DemandAt := fun _ => Unit
  generateDemand := fun _ => ()

def contributionCapacityDemandEntryAt
    (rooted : RootedFailure) :
    {indexedSupport : (CutN rooted).Support} →
      (CutN rooted).ObstructionAt indexedSupport →
        OpenResponsibilityAt (CutN rooted) indexedSupport
  | _indexedSupport, .inl _oldObstruction =>
      contributionCapacityCutDefaultEntryAt rooted _indexedSupport
  | _, .inr .exhausted =>
      contributionCapacityCutTargetObstruction rooted

def contributionCapacityU7Source
    (rooted : RootedFailure) :
    U7ActualSuccessorSource (CutN rooted) (contributionCapacityU7 rooted) where
  EventAt := SourceGeneratedU7DemandAt (contributionCapacityU7 rooted)
  emit := fun obstruction => .canonical obstruction
  demandGeneratedAt := fun event => event
  demandEntryAt := fun {_support} {obstruction} {_demand} _ =>
    contributionCapacityDemandEntryAt rooted obstruction

def contributionCapacityLawExtensionDispositionAt
    (rooted : RootedFailure)
    (indexedSupport : (CutN rooted).Support) :
    (CutN rooted).DispositionAt indexedSupport .lawSurfaceExtension := by
  rcases indexedSupport with ⟨oldSupport, cutPhase⟩
  rcases oldSupport with ⟨worldSupport, mergePhase⟩
  rcases worldSupport with ⟨cofaceSupport, lossPhase⟩
  cases cofaceSupport with
  | inl oldSupport => exact ()
  | inr direction =>
      cases direction
      exact GeneratedMinimalCofaceAt.CofaceTargetDispositionAt.ofTarget ()

/-- Every capacity residual first reaches the theory-audit gate.  The exact
target residual below then proves both old expression and realization fibres
empty, so only that occurrence opens U8. -/
def contributionCapacityCalculus
    (rooted : RootedFailure) :
    U7ObstructionEvolutionCalculus
      (CutN rooted) (contributionCapacityU7 rooted) where
  source := contributionCapacityU7Source rooted
  compile := by
    intro indexedSupport indexedObstruction demand event
    exact
      { disposition := .requiresTheoryAudit
          (contributionCapacityLawExtensionDispositionAt rooted indexedSupport)
        demandEntryDisposition := PUnit.unit }

def contributionCapacityU7Event
    (rooted : RootedFailure) :=
  (contributionCapacityCalculus rooted).source.emit
    (contributionCapacityResidual rooted)

def contributionCapacityU7Gate
    (rooted : RootedFailure) :
    SourceNativeU7TheoryAuditAt (contributionCapacityCalculus rooted)
      (contributionCapacityU7Event rooted) :=
  PUnit.unit

def contributionCapacityInquiryAuditAt
    (rooted : RootedFailure) :
    (current : (TargetV rooted).Current) →
      SourceNativeInquiryFrontAuditAt
        (contributionCapacityU7 rooted) (contributionCapacityCalculus rooted)
        (contributionCapacityOperationalTheory rooted)
        (contributionCapacityCutSupportAt rooted current)
  | 0 => .answered
  | _ + 1 =>
      .obstructed (contributionCapacityResidual rooted)
        (.requiresU8 (contributionCapacityU7Gate rooted)
          (contributionCapacityOperationalFailure rooted))

/-! ## Three exact root projections -/

def ContributionCapacityRootPayloadAt
    (rooted : RootedFailure)
    {current : (TargetV rooted).Current}
    (occurrence :
      (contributionCapacityCutSource rooted).toRootSource.actual.OccurrenceAt
        current) : Type :=
  SourceNativeLedgerEvolutionAt (contributionCapacityCutSource rooted)
      occurrence ×
    ((entry : OpenResponsibilityAt (CutN rooted)
      ((contributionCapacityCutSource rooted).toRootSource.account.supportOf
        occurrence)) →
      AdmittedObligation (ContributionCapacityCutLifecycleV rooted))

inductive ContributionCapacityProjection
  | ledgerLifecycle
  | inquiry
  | failure

def contributionCapacityProjectionLaw
    (rooted : RootedFailure) :
    SourceNativeProjectionLaw
      (contributionCapacityCutRestructuringSource rooted).toLedgerSource where
  Projection := ContributionCapacityProjection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {current} occurrence _ =>
    match projection with
    | .ledgerLifecycle => ContributionCapacityRootPayloadAt rooted occurrence
    | .inquiry => SourceNativeInquiryCompilationTokenAt
        (contributionCapacityInquiryEntryAt rooted current) ()
          (ULift.up.{1, 0} occurrence)
          (contributionCapacityInquiryAuditAt rooted current) PUnit
    | .failure => match current with
      | 0 => PUnit
      | _ + 1 => SourceNativeRootExpressibilityFailureTokenAt
          (contributionCapacityOperationalFailure rooted)
          (contributionCapacityCalculus rooted)
          (contributionCapacityU7Event rooted)
  project := fun projection {current} occurrence _ => by
    cases projection with
    | ledgerLifecycle =>
        exact
          ⟨(contributionCapacityCutLedgerCompiler rooted).compile occurrence,
            fun entry => contributionCapacityCutObligationAt rooted
              occurrence.2.materialWitness entry⟩
    | inquiry => exact .canonical PUnit.unit
    | failure =>
        cases current with
        | zero => exact PUnit.unit
        | succ current => exact .canonical

/-! ## Complete authority and living root -/

def contributionCapacityAuthoritySource
    (rooted : RootedFailure) :
    SourceNativeAuthoritySource (CutN rooted) (TargetV rooted) where
  restructuringSource := contributionCapacityCutRestructuringSource rooted
  eventInventoryAdmission :=
    .reflOfNoFaithfulTerminal
      (contributionCapacityCutRestructuringSource rooted)
      (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := contributionCapacityOperationalTheory rooted
  projectionLaw := contributionCapacityProjectionLaw rooted

def contributionCapacityAuthoritativeRoot
    (rooted : RootedFailure) :
    SourceNativeAuthoritativeRootClosure (CutN rooted) (TargetV rooted) where
  source := contributionCapacityAuthoritySource rooted
  emitted := contributionCapacityCutEmitted rooted
  compiler_commutes := contributionCapacityCutCompiler_commutes rooted

def contributionCapacityLivingRoot
    (rooted : RootedFailure) :
    SourceNativeLivingRootClosure (CutN rooted) (TargetV rooted) :=
  (contributionCapacityAuthoritativeRoot rooted).toLivingWithoutFaithfulTerminal
    (fun _ => ⟨fun terminal => nomatch terminal⟩)

@[simp] theorem contributionCapacityRoot_lawSurface_exact
    (rooted : RootedFailure) :
    (contributionCapacityLivingRoot rooted).source.base.lawSurface =
      contributionCapacityOperationalTheory rooted :=
  rfl

@[simp] theorem contributionCapacityRoot_emitted_exact
    (rooted : RootedFailure)
    (current : (TargetV rooted).Current) :
    (contributionCapacityLivingRoot rooted).emitted current =
      contributionCapacityCutEmitted rooted current :=
  rfl

/-! ## Initial occurrence and first actual capacity write -/

abbrev ContributionCapacityRootVisit
    (rooted : RootedFailure) :=
  SourceNativeTemporalVisitAt
    (contributionCapacityLivingRoot rooted).toAuthoritativeRoot.toLedgerRoot

abbrev contributionCapacityRootInitialVisit
    (rooted : RootedFailure) : ContributionCapacityRootVisit rooted :=
  .finite
    (contributionCapacityLivingRoot rooted).toAuthoritativeRoot.toRoot.initialVisit

def contributionCapacityRootInitialGenerated
    (rooted : RootedFailure) :
    SourceNativeTemporalVisitGeneratedEvolutionAt
      (contributionCapacityLivingRoot rooted).toAuthoritativeRoot.toLedgerRoot
      (contributionCapacityRootInitialVisit rooted) :=
  (contributionCapacityLivingRoot rooted).toAuthoritativeRoot.toLedgerRoot
    |>.generatedAtTemporalVisit (contributionCapacityRootInitialVisit rooted)

def contributionCapacityRootInitialContributionRow
    (rooted : RootedFailure) :
    (contributionCapacityRootInitialGenerated rooted).GeneratedEntryRowAt
      (initialContribution rooted) :=
  ((contributionCapacityRootInitialGenerated rooted).canonicalGeneratedEntryRow?
    (initialContribution rooted)).get (by rfl)

def contributionCapacityRootInitialObstructionRow
    (rooted : RootedFailure) :
    (contributionCapacityRootInitialGenerated rooted).GeneratedEntryRowAt
      (initialObstruction rooted) :=
  ((contributionCapacityRootInitialGenerated rooted).canonicalGeneratedEntryRow?
    (initialObstruction rooted)).get (by rfl)

def contributionCapacityRootFirstSuccessor
    (rooted : RootedFailure) :
    SourceNativeLedgerGeneratedSuccessorAt
      (contributionCapacityRootInitialGenerated rooted).occurrence
      (contributionCapacityRootInitialGenerated rooted).wholeLedgerWriteBack :=
  contributionCapacityCutFirstSuccessor rooted

@[simp] theorem contributionCapacityRoot_firstTargetCurrent_exact
    (rooted : RootedFailure) :
    (contributionCapacityRootFirstSuccessor rooted).targetCurrent = 1 :=
  rfl

@[simp] theorem contributionCapacityRoot_firstTargetOccurrence_exact
    (rooted : RootedFailure) :
    (contributionCapacityRootFirstSuccessor rooted).targetOccurrence =
      contributionCapacityCutEmitted rooted 1 :=
  rfl

@[simp] theorem contributionCapacityRoot_contribution_destination_exact
    (rooted : RootedFailure) :
    ((contributionCapacityRootFirstSuccessor rooted).ledgerEvolution.destination
      (initialContribution rooted)).1 =
        contributionCapacityCutTargetContribution rooted :=
  contributionCapacityFirst_destination_contribution rooted
    (contributionCapacityCutEmitted rooted 0)

@[simp] theorem contributionCapacityRoot_obstruction_destination_exact
    (rooted : RootedFailure) :
    ((contributionCapacityRootFirstSuccessor rooted).ledgerEvolution.destination
      (initialObstruction rooted)).1 =
        contributionCapacityCutTargetObstruction rooted :=
  contributionCapacityFirst_destination_obstruction rooted
    (contributionCapacityCutEmitted rooted 0)

def contributionCapacityRootTargetVisit
    (rooted : RootedFailure) : ContributionCapacityRootVisit rooted :=
  (contributionCapacityRootInitialVisit rooted).next
    (contributionCapacityRootFirstSuccessor rooted).next_eq

def contributionCapacityRootInitialObstructionAuthority
    (rooted : RootedFailure) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt
      (contributionCapacityLivingRoot rooted)
      (contributionCapacityRootInitialVisit rooted)
      (initialObstruction rooted) :=
  SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitialRow
    (contributionCapacityLivingRoot rooted) (initialObstruction rooted)
    (contributionCapacityRootInitialObstructionRow rooted)

def contributionCapacityRootTargetObstructionAuthority
    (rooted : RootedFailure) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt
      (contributionCapacityLivingRoot rooted)
      (contributionCapacityRootTargetVisit rooted)
      (contributionCapacityCutTargetObstruction rooted) :=
  (contributionCapacityRootInitialObstructionAuthority rooted).next
    (contributionCapacityRootFirstSuccessor rooted).next_eq

end
end M14SourceGeneratedContributionCapacityCutRoot
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityCutRoot.contributionCapacityCalculus
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityCutRoot.contributionCapacityLivingRoot
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityCutRoot.contributionCapacityRootTargetObstructionAuthority
