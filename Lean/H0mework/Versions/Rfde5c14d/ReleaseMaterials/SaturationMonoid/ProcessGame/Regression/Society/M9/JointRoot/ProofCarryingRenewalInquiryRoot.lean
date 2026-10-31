import H0mework.Versions.R2.Checks.Runtime.U8Completion
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Legislation.ProofCarryingRenewalRestriction
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Theory.Adoption.SourceInstalledCausalTheoryAdoption
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Lifecycle.Universal.FixedFixtureLaw
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M8.Relationship.RelationshipMaintenanceRenewalRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M6.GoNaturalAuthorityReconstructionRegression
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.UBIProofCarryingRootRestriction
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Recognition.WitnessPublication
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Mandate.SourceMandateRenewal
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Maintenance.SourceEssentialServiceRestoration
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Route.SourceRouteOutageRestoration
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Clearing.SourceCommonClearingRenewal
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Clearing.Backstop.SourceClearingBackstopRenewal

/-!
# Proof-carrying renewal, UBI, witness, mandate, service, route, and clearing

The existing U8 inquiry authority source is successively uplifted before its
emitter is installed with proof-carrying renewal, UBI, recognition-witness,
mandate-power, and essential-service maintenance coordinates.  Old inquiry
and failure coordinates survive only through
`.inherited`; the first renewal carries relationship/lifecycle/residual/kernel
authority, the second UBI source and repair disposition, and the third the
root-independent source witness plus honest publication law.  The fourth
installs exact source-generated election renewal without importing the M8
sibling root; the fifth installs the health-service restoration action
without expanding the UBI capture-repair disposition.  The sixth installs
route-outage restoration as its own action-bearing coordinate rather than a
contingency branch inside the UBI disposition.  The seventh installs the
existing exhaustive exchange fold as source-owned symmetric common clearing,
without a second settlement run or ledger.  The eighth installs the exact
source-generated residual-consumer activation for the existing partial
settlement, keeping ordinary clearing and residual-backstop authority distinct.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M9ProofCarryingRenewalInquiryRoot

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open ConstructiveRoot.RootInquiryU8CompletionRegression
open Lifecycle Universal Renewal Legislation
open Theory Effect Adoption
open Lifecycle.Universal.FixedAdapter
open M3FiniteExchangeFixture M3SettlementDispositionRegression
open M8RelationshipMaintenanceRenewalRegression
open M6GoNaturalAuthorityReconstructionRegression
open M14UBIProofCarryingRootRestriction
open M14RecognitionWitnessPublication
open M14SourceMandateRenewal
open M14SourceEssentialServiceRestoration
open M14SourceRouteOutageRestoration
open M14SourceCommonClearingRenewal
open M14SourceGeneratedClearingBackstopActivation
open M14SourceClearingBackstopRenewal

abbrev N := RootInquiryU8CompletionRegression.N
abbrev V := RootInquiryU8CompletionRegression.V

abbrev LocalGame := Lifecycle.actualEventGame
abbrev LocalSeed := Lifecycle.Universal.FixedAdapter.targetFace.Seed
abbrev LocalSeedAt := Lifecycle.Universal.FixedAdapter.targetFace.SeedAt
abbrev LocalDispositionAt := RelationshipDispositionAt

/-- Exact M1 lifecycle compilation carried at every local renewal seed. -/
abbrev LocalLifecycleAt
    (_seed : SourceSeed Lifecycle.actualEventOccurrenceOf
      LocalSeed LocalSeedAt LocalGame.source) :=
  SourceOwnedActorLifecycleLaw.ActualLifecycleCompilation
    Lifecycle.Universal.FixedAdapter.law

/-- Causally adopted theory feedback is compiled from the pre-uplift law
surface, so it can enter the renewal payload before `jointRoot` exists. -/
def theoryFeedbackCompiler : SourceOwnedTheoryFeedbackCompilerAt
    RootInquiryU8CompletionRegression.oldTheory
      LocalGame LocalSeed LocalSeedAt where
  Classification := Bool
  PolicyDecision := Bool
  classificationReadout :=
    { read := fun seed => match seed.1 with
        | .t0 => true
        | _ => false }
  policyReadout :=
    { read := fun seed => match seed.1 with
        | .t0 => true
        | _ => false }
  EffectAt := LocalLifecycleAt
  actualEffectAt := fun _ =>
    Lifecycle.Universal.FixedAdapter.law.wholeCompilation
  EffectConsumerAt := fun _ effect =>
    PLift (effect = Lifecycle.Universal.FixedAdapter.law.wholeCompilation)
  consumeEffect := fun _ => ⟨rfl⟩

/-- The M9 relationship consumer is preserved inside the M13 pre-emitter
composite; causal adoption does not replace its earlier authority. -/
abbrev LocalConsumerAt := CausalTheoryAdoptionConsumerAt
  theoryFeedbackCompiler RelationshipConsumerAt

abbrev ResidualProcess := M3FiniteExchangeFixture.P
abbrev RenewalObserver := goAuthorityObserver 1

abbrev RenewalConsumerAt :=
  ProofCarryingRenewalConsumerAt ResidualProcess RenewalObserver
    LocalConsumerAt LocalLifecycleAt

/-- Existing maintained M3 residual; no obligation or bearer is allocated by
the renewal law. -/
def existingResidual : ExistingResidualBearerAt ResidualProcess where
  sourceState := M3SettlementDispositionRegression.exchangeState.current
  settlement := settlementOf .a .maintain
  liveResidual := maintainOpen .a

/-- Complete exact-seed restriction installed in the renewal consumer fibre. -/
def proofCarryingRestriction :
    ProofCarryingRenewalRestrictionAt ResidualProcess RenewalObserver
      LocalConsumerAt LocalLifecycleAt relationshipRenewalSeed where
  localConsumer := CausalTheoryAdoptionConsumerAt.generate
    theoryFeedbackCompiler relationshipConsumer
  localLifecycle := Lifecycle.Universal.FixedAdapter.law.wholeCompilation
  existingResidual := existingResidual
  observerVertical := goAuthorityChangingVerticalAutomorphism 1

/-- The renewal compiler is total on the literal one-occurrence U8 root.
Every payload field is generated before a later temporal visit can inspect
the inquiry branch. -/
def renewalLaw : SourceNativeRenewalProjectionLaw
    RootInquiryU8CompletionRegression.root.toAuthoritativeRoot.toLedgerRoot.source
    LocalGame LocalSeed LocalSeedAt RenewalConsumerAt LocalDispositionAt where
  ActiveAt := fun {_current} _occurrence => PUnit
  InactiveAt := fun {_current} _occurrence => PEmpty
  classify := fun {_current} _occurrence => .inl PUnit.unit
  compile := by
    intro current occurrence _active
    cases current
    rcases occurrence with ⟨support, event⟩
    cases support with
    | false => exact nomatch event
    | true =>
        cases event
        let source :=
          RootInquiryU8CompletionRegression.root.toAuthoritativeRoot.toLedgerRoot.source
        let exactOccurrence := RootInquiryU8CompletionRegression.root.emitted ()
        let exactEntry := RootInquiryU8CompletionRegression.entry
        let exactRow := RootInquiryU8CompletionRegression.entryRow.sourceRow
        let exactSuccessor :=
          (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated?
            (source.ledgerCompiler.compile exactOccurrence)).get (by rfl)
        exact RootRestrictedRenewalPayloadAt.generate
          relationshipRenewalSeed proofCarryingRestriction
          relationshipDisposition exactEntry exactRow exactSuccessor
  sourceSeed_reflects_rootOccurrence := by
    intro leftCurrent rightCurrent leftOccurrence rightOccurrence
      _leftActive _rightActive _seedEq
    cases leftCurrent
    cases rightCurrent
    rcases leftOccurrence with ⟨leftSupport, leftEvent⟩
    rcases rightOccurrence with ⟨rightSupport, rightEvent⟩
    cases leftSupport with
    | false => exact nomatch leftEvent
    | true =>
        cases rightSupport with
        | false => exact nomatch rightEvent
        | true => cases leftEvent; cases rightEvent; rfl

/-- First pre-emitter uplift: the existing proof-carrying renewal coordinate.
The final joint source below inherits this coordinate unchanged. -/
def proofCarryingAuthoritySource : SourceNativeAuthoritySource N V :=
  withRenewalProjection
    RootInquiryU8CompletionRegression.root.toAuthoritativeRoot.source renewalLaw

/-- Second pre-emitter coordinate: an exact UBI source program indexed by the
recurrent occurrence-capacity seed.  It contains no exit verdict, matching,
service slot, capacity, or completed future. -/
def ubiLaw : SourceNativeRenewalProjectionLaw
    proofCarryingAuthoritySource.restructuringSource.toLedgerSource
    M14UBIProofCarryingRootRestriction.LocalGame
    M14UBIProofCarryingRootRestriction.LocalSeed
    M14UBIProofCarryingRootRestriction.LocalSeedAt
    M14UBIProofCarryingRootRestriction.UBIConsumerAt
    M14UBIProofCarryingRootRestriction.UBIDispositionAt where
  ActiveAt := fun {_current} _occurrence => PUnit
  InactiveAt := fun {_current} _occurrence => PEmpty
  classify := fun {_current} _occurrence => .inl PUnit.unit
  compile := by
    intro current occurrence _active
    cases current
    rcases occurrence with ⟨support, event⟩
    cases support with
    | false => exact nomatch event
    | true =>
        cases event
        let source :=
          proofCarryingAuthoritySource.restructuringSource.toLedgerSource
        let exactOccurrence :=
          RootInquiryU8CompletionRegression.root.emitted ()
        let exactSuccessor :=
          (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated?
            (source.ledgerCompiler.compile exactOccurrence)).get (by rfl)
        exact RootRestrictedRenewalPayloadAt.generate
          M10OccurrenceCapacityProcessFixture.focalSeed
          sourceGeneratedUBIRootRestriction sourceGeneratedUBIDisposition
          RootInquiryU8CompletionRegression.entry
          RootInquiryU8CompletionRegression.entryRow.sourceRow
          exactSuccessor
  sourceSeed_reflects_rootOccurrence := by
    intro leftCurrent rightCurrent leftOccurrence rightOccurrence
      _leftActive _rightActive _seedEq
    cases leftCurrent
    cases rightCurrent
    rcases leftOccurrence with ⟨leftSupport, leftEvent⟩
    rcases rightOccurrence with ⟨rightSupport, rightEvent⟩
    cases leftSupport with
    | false => exact nomatch leftEvent
    | true =>
        cases rightSupport with
        | false => exact nomatch rightEvent
        | true => cases leftEvent; cases rightEvent; rfl

/-- Intermediate pre-emitter inventory carrying PCL and UBI. -/
def ubiAuthoritySource : SourceNativeAuthoritySource N V :=
  withRenewalProjection proofCarryingAuthoritySource ubiLaw

/-- Third pre-emitter coordinate: publication of the root-independent
structural-exploitation witness on the exact left standing of the existing
PCL authority kernel.  The disposition carries the honest total publication
law, but no refined observer, decoder, reconstruction, branch, or next. -/
def recognitionWitnessLaw : SourceNativeRenewalProjectionLaw
    ubiAuthoritySource.restructuringSource.toLedgerSource
    LocalGame LocalSeed LocalSeedAt RecognitionWitnessConsumerAt
      RecognitionWitnessDispositionAt where
  ActiveAt := fun {_current} _occurrence => PUnit
  InactiveAt := fun {_current} _occurrence => PEmpty
  classify := fun {_current} _occurrence => .inl PUnit.unit
  compile := by
    intro current occurrence _active
    cases current
    rcases occurrence with ⟨support, event⟩
    cases support with
    | false => exact nomatch event
    | true =>
        cases event
        let source :=
          ubiAuthoritySource.restructuringSource.toLedgerSource
        let exactOccurrence := RootInquiryU8CompletionRegression.root.emitted ()
        let exactSuccessor :=
          (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated?
            (source.ledgerCompiler.compile exactOccurrence)).get (by rfl)
        exact RootRestrictedRenewalPayloadAt.generate
          relationshipRenewalSeed recognitionWitnessConsumer
          recognitionWitnessDisposition RootInquiryU8CompletionRegression.entry
          RootInquiryU8CompletionRegression.entryRow.sourceRow exactSuccessor
  sourceSeed_reflects_rootOccurrence := by
    intro leftCurrent rightCurrent leftOccurrence rightOccurrence
      _leftActive _rightActive _seedEq
    cases leftCurrent
    cases rightCurrent
    rcases leftOccurrence with ⟨leftSupport, leftEvent⟩
    rcases rightOccurrence with ⟨rightSupport, rightEvent⟩
    cases leftSupport with
    | false => exact nomatch leftEvent
    | true =>
        cases rightSupport with
        | false => exact nomatch rightEvent
        | true => cases leftEvent; cases rightEvent; rfl

/-- Intermediate inventory carrying PCL, UBI, and recognition publication. -/
def recognitionAuthoritySource : SourceNativeAuthoritySource N V :=
  withRenewalProjection ubiAuthoritySource recognitionWitnessLaw

/-- Root-owned shell for the fourth pre-emitter coordinate.  The shell only
supplies this literal root's existing entry, row, and successor; the election
seed, consumer, and disposition remain fixed by `sourceMandateRenewalFace`. -/
def mandateRootShell : SourceMandateRenewalRootShellAt
    recognitionAuthoritySource.restructuringSource.toLedgerSource where
  ActiveAt := fun {_current} _occurrence => PUnit
  InactiveAt := fun {_current} _occurrence => PEmpty
  classify := fun {_current} _occurrence => .inl PUnit.unit
  sourceEntry := by
    intro current occurrence _active
    cases current
    rcases occurrence with ⟨support, event⟩
    cases support with
    | false => exact nomatch event
    | true => cases event; exact RootInquiryU8CompletionRegression.entry
  selectedRow := by
    intro current occurrence _active
    cases current
    rcases occurrence with ⟨support, event⟩
    cases support with
    | false => exact nomatch event
    | true =>
        cases event
        exact RootInquiryU8CompletionRegression.entryRow.sourceRow
  successor := by
    intro current occurrence _active
    cases current
    rcases occurrence with ⟨support, event⟩
    cases support with
    | false => exact nomatch event
    | true =>
        cases event
        let source :=
          recognitionAuthoritySource.restructuringSource.toLedgerSource
        exact (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated?
          (source.ledgerCompiler.compile
            (RootInquiryU8CompletionRegression.root.emitted ()))).get (by rfl)
  activeOccurrences_eq := by
    intro leftCurrent rightCurrent leftOccurrence rightOccurrence
      _leftActive _rightActive
    cases leftCurrent
    cases rightCurrent
    rcases leftOccurrence with ⟨leftSupport, leftEvent⟩
    rcases rightOccurrence with ⟨rightSupport, rightEvent⟩
    cases leftSupport with
    | false => exact nomatch leftEvent
    | true =>
        cases rightSupport with
        | false => exact nomatch rightEvent
        | true => cases leftEvent; cases rightEvent; rfl

/-- Fourth pre-emitter producer: exact mandate-power renewal. -/
def mandateLaw : SourceMandateRenewalLawAt
    recognitionAuthoritySource.restructuringSource.toLedgerSource :=
  sourceMandateRenewalLaw mandateRootShell

/-- Intermediate inventory through exact mandate-power renewal. -/
def mandateAuthoritySource : SourceNativeAuthoritySource N V :=
  withSourceMandateRenewal recognitionAuthoritySource mandateRootShell

/-- The fifth renewal coordinate reuses the exact same root-owned shell.  The
shell types coincide definitionally because every renewal uplift preserves
the one restructuring source and ledger compiler. -/
def essentialServiceRestorationRootShell : SourceNativeRenewalRootShellAt
    mandateAuthoritySource.restructuringSource.toLedgerSource :=
  mandateRootShell

/-- Fifth pre-emitter law: exact health-service restoration. -/
def essentialServiceRestorationLaw : SourceEssentialServiceRestorationLawAt
    mandateAuthoritySource.restructuringSource.toLedgerSource :=
  sourceEssentialServiceRestorationLaw
    essentialServiceRestorationRootShell

/-- Intermediate inventory through exact essential-service restoration. -/
def essentialServiceRestorationAuthoritySource :
    SourceNativeAuthoritySource N V :=
  withRenewalProjection mandateAuthoritySource
    essentialServiceRestorationLaw

/-- The sixth renewal coordinate reuses the same root-owned shell. -/
def routeOutageRestorationRootShell : SourceNativeRenewalRootShellAt
    essentialServiceRestorationAuthoritySource.restructuringSource.toLedgerSource :=
  essentialServiceRestorationRootShell

/-- Sixth pre-emitter law: exact route-outage restoration. -/
def routeOutageRestorationLaw : SourceRouteOutageRestorationLawAt
    essentialServiceRestorationAuthoritySource.restructuringSource.toLedgerSource :=
  sourceRouteOutageRestorationLaw routeOutageRestorationRootShell

/-- Intermediate inventory through exact route-outage restoration. -/
def routeOutageRestorationAuthoritySource : SourceNativeAuthoritySource N V :=
  withRenewalProjection essentialServiceRestorationAuthoritySource
    routeOutageRestorationLaw

/-- The seventh renewal coordinate reuses the same root-owned shell. -/
def commonClearingRootShell : SourceNativeRenewalRootShellAt
    routeOutageRestorationAuthoritySource.restructuringSource.toLedgerSource :=
  routeOutageRestorationRootShell

/-- Seventh pre-emitter law: source-owned symmetric common clearing. -/
def commonClearingLaw : SourceCommonClearingRenewalLawAt
    routeOutageRestorationAuthoritySource.restructuringSource.toLedgerSource :=
  sourceCommonClearingRenewalLaw commonClearingRootShell

/-- Intermediate inventory through source-owned symmetric common clearing. -/
def commonClearingAuthoritySource : SourceNativeAuthoritySource N V :=
  withRenewalProjection routeOutageRestorationAuthoritySource
    commonClearingLaw

/-- The eighth renewal coordinate reuses the same root-owned shell. -/
def clearingBackstopRootShell : SourceNativeRenewalRootShellAt
    commonClearingAuthoritySource.restructuringSource.toLedgerSource :=
  commonClearingRootShell

/-- Eighth pre-emitter law: exact source-owned clearing backstop. -/
def clearingBackstopLaw : SourceClearingBackstopRenewalLawAt
    commonClearingAuthoritySource.restructuringSource.toLedgerSource :=
  sourceClearingBackstopRenewalLaw clearingBackstopRootShell

/-- The one final source inventory used by M9, M13, M∞, and M14.  All eight
renewal coordinates are installed before this root emits. -/
def jointAuthoritySource : SourceNativeAuthoritySource N V :=
  withRenewalProjection commonClearingAuthoritySource clearingBackstopLaw

/-- Literal expanded root.  It is not related to the old root by an external
HEq splice: all downstream indices mention this value directly. -/
def jointRoot : SourceNativeLivingRootClosure N V where
  source :=
    { base := jointAuthoritySource
      terminalHandoff := jointAuthoritySource.emptyFaithfulTerminalHandoff
        (fun _ => ⟨fun terminal => nomatch terminal⟩) }
  emitted := RootInquiryU8CompletionRegression.root.emitted
  compiler_commutes := fun _ => rfl

def jointVisit : SourceNativeTemporalVisitAt
    jointRoot.toAuthoritativeRoot.toLedgerRoot :=
  .finite jointRoot.toAuthoritativeRoot.toRoot.initialVisit

/-- Old U8 inquiry coordinate in the expanded inventory. -/
def jointInquiryProjection :
    jointRoot.toAuthoritativeRoot.source.projectionLaw.Projection :=
  .inherited
    (.inherited
      (.inherited
        (.inherited (.inherited (.inherited (.inherited (.inherited .inquiry)))))))

/-- Old failure coordinate in the expanded inventory. -/
def jointFailureProjection :
    jointRoot.toAuthoritativeRoot.source.projectionLaw.Projection :=
  .inherited
    (.inherited
      (.inherited
        (.inherited (.inherited (.inherited (.inherited (.inherited .failure)))))))

/-- Exact final-root coordinate of the proof-carrying renewal. -/
def jointProofCarryingProjection :
    jointRoot.toAuthoritativeRoot.source.projectionLaw.Projection :=
  .inherited
    (.inherited
      (.inherited (.inherited (.inherited (.inherited (.inherited .renewal))))))

/-- Exact final-root coordinate of the UBI source program. -/
def jointUBIProjection :
    jointRoot.toAuthoritativeRoot.source.projectionLaw.Projection :=
  .inherited
    (.inherited (.inherited (.inherited (.inherited (.inherited .renewal)))))

/-- Exact final-root coordinate of recognition-witness publication. -/
def jointRecognitionWitnessProjection :
    jointRoot.toAuthoritativeRoot.source.projectionLaw.Projection :=
  .inherited (.inherited (.inherited (.inherited (.inherited .renewal))))

/-- Exact final-root coordinate of mandate-power renewal. -/
def jointMandateProjection :
    jointRoot.toAuthoritativeRoot.source.projectionLaw.Projection :=
  .inherited (.inherited (.inherited (.inherited .renewal)))

/-- Exact final-root coordinate of essential-service restoration. -/
def jointEssentialServiceRestorationProjection :
    jointRoot.toAuthoritativeRoot.source.projectionLaw.Projection :=
  .inherited (.inherited (.inherited .renewal))

/-- Exact final-root coordinate of route-outage restoration. -/
def jointRouteOutageRestorationProjection :
    jointRoot.toAuthoritativeRoot.source.projectionLaw.Projection :=
  .inherited (.inherited .renewal)

/-- Exact final-root coordinate of symmetric common clearing. -/
def jointCommonClearingProjection :
    jointRoot.toAuthoritativeRoot.source.projectionLaw.Projection :=
  .inherited .renewal

/-- Exact final-root coordinate of the source-owned clearing backstop. -/
def jointClearingBackstopProjection :
    jointRoot.toAuthoritativeRoot.source.projectionLaw.Projection :=
  .renewal

theorem ubi_projection_ne_proofCarrying_projection :
    jointUBIProjection ≠ jointProofCarryingProjection := by
  intro equality
  cases equality

theorem ubi_projection_ne_inquiry_projection :
    jointUBIProjection ≠ jointInquiryProjection := by
  intro equality
  cases equality

theorem proofCarrying_projection_ne_inquiry_projection :
    jointProofCarryingProjection ≠ jointInquiryProjection := by
  intro equality
  cases equality

theorem recognitionWitness_projection_ne_ubi_projection :
    jointRecognitionWitnessProjection ≠ jointUBIProjection := by
  intro equality
  cases equality

theorem recognitionWitness_projection_ne_proofCarrying_projection :
    jointRecognitionWitnessProjection ≠ jointProofCarryingProjection := by
  intro equality
  cases equality

theorem mandate_projection_ne_recognitionWitness_projection :
    jointMandateProjection ≠ jointRecognitionWitnessProjection := by
  intro equality
  cases equality

theorem mandate_projection_ne_ubi_projection :
    jointMandateProjection ≠ jointUBIProjection := by
  intro equality
  cases equality

theorem mandate_projection_ne_proofCarrying_projection :
    jointMandateProjection ≠ jointProofCarryingProjection := by
  intro equality
  cases equality

theorem mandate_projection_ne_inquiry_projection :
    jointMandateProjection ≠ jointInquiryProjection := by
  intro equality
  cases equality

theorem mandate_projection_ne_failure_projection :
    jointMandateProjection ≠ jointFailureProjection := by
  intro equality
  cases equality

theorem essentialService_projection_ne_mandate_projection :
    jointEssentialServiceRestorationProjection ≠ jointMandateProjection := by
  intro equality
  cases equality

theorem essentialService_projection_ne_recognitionWitness_projection :
    jointEssentialServiceRestorationProjection ≠
      jointRecognitionWitnessProjection := by
  intro equality
  cases equality

theorem essentialService_projection_ne_ubi_projection :
    jointEssentialServiceRestorationProjection ≠ jointUBIProjection := by
  intro equality
  cases equality

theorem essentialService_projection_ne_proofCarrying_projection :
    jointEssentialServiceRestorationProjection ≠
      jointProofCarryingProjection := by
  intro equality
  cases equality

theorem essentialService_projection_ne_inquiry_projection :
    jointEssentialServiceRestorationProjection ≠ jointInquiryProjection := by
  intro equality
  cases equality

theorem essentialService_projection_ne_failure_projection :
    jointEssentialServiceRestorationProjection ≠ jointFailureProjection := by
  intro equality
  cases equality

theorem essentialService_projection_distinct_from_existing_coordinates :
    jointEssentialServiceRestorationProjection ≠ jointMandateProjection ∧
      jointEssentialServiceRestorationProjection ≠
        jointRecognitionWitnessProjection ∧
      jointEssentialServiceRestorationProjection ≠ jointUBIProjection ∧
      jointEssentialServiceRestorationProjection ≠
        jointProofCarryingProjection ∧
      jointEssentialServiceRestorationProjection ≠ jointInquiryProjection ∧
      jointEssentialServiceRestorationProjection ≠ jointFailureProjection :=
  ⟨essentialService_projection_ne_mandate_projection,
    essentialService_projection_ne_recognitionWitness_projection,
    essentialService_projection_ne_ubi_projection,
    essentialService_projection_ne_proofCarrying_projection,
    essentialService_projection_ne_inquiry_projection,
    essentialService_projection_ne_failure_projection⟩

theorem routeOutage_projection_ne_essentialService_projection :
    jointRouteOutageRestorationProjection ≠
      jointEssentialServiceRestorationProjection := by
  intro equality
  cases equality

theorem routeOutage_projection_ne_mandate_projection :
    jointRouteOutageRestorationProjection ≠ jointMandateProjection := by
  intro equality
  cases equality

theorem routeOutage_projection_ne_recognitionWitness_projection :
    jointRouteOutageRestorationProjection ≠
      jointRecognitionWitnessProjection := by
  intro equality
  cases equality

theorem routeOutage_projection_ne_ubi_projection :
    jointRouteOutageRestorationProjection ≠ jointUBIProjection := by
  intro equality
  cases equality

theorem routeOutage_projection_ne_proofCarrying_projection :
    jointRouteOutageRestorationProjection ≠
      jointProofCarryingProjection := by
  intro equality
  cases equality

theorem routeOutage_projection_ne_inquiry_projection :
    jointRouteOutageRestorationProjection ≠ jointInquiryProjection := by
  intro equality
  cases equality

theorem routeOutage_projection_ne_failure_projection :
    jointRouteOutageRestorationProjection ≠ jointFailureProjection := by
  intro equality
  cases equality

theorem routeOutage_projection_distinct_from_existing_coordinates :
    jointRouteOutageRestorationProjection ≠
        jointEssentialServiceRestorationProjection ∧
      jointRouteOutageRestorationProjection ≠ jointMandateProjection ∧
      jointRouteOutageRestorationProjection ≠
        jointRecognitionWitnessProjection ∧
      jointRouteOutageRestorationProjection ≠ jointUBIProjection ∧
      jointRouteOutageRestorationProjection ≠
        jointProofCarryingProjection ∧
      jointRouteOutageRestorationProjection ≠ jointInquiryProjection ∧
      jointRouteOutageRestorationProjection ≠ jointFailureProjection :=
  ⟨routeOutage_projection_ne_essentialService_projection,
    routeOutage_projection_ne_mandate_projection,
    routeOutage_projection_ne_recognitionWitness_projection,
    routeOutage_projection_ne_ubi_projection,
    routeOutage_projection_ne_proofCarrying_projection,
    routeOutage_projection_ne_inquiry_projection,
    routeOutage_projection_ne_failure_projection⟩

theorem commonClearing_projection_ne_routeOutage_projection :
    jointCommonClearingProjection ≠ jointRouteOutageRestorationProjection := by
  intro equality
  cases equality

theorem commonClearing_projection_ne_essentialService_projection :
    jointCommonClearingProjection ≠
      jointEssentialServiceRestorationProjection := by
  intro equality
  cases equality

theorem commonClearing_projection_ne_mandate_projection :
    jointCommonClearingProjection ≠ jointMandateProjection := by
  intro equality
  cases equality

theorem commonClearing_projection_ne_recognitionWitness_projection :
    jointCommonClearingProjection ≠
      jointRecognitionWitnessProjection := by
  intro equality
  cases equality

theorem commonClearing_projection_ne_ubi_projection :
    jointCommonClearingProjection ≠ jointUBIProjection := by
  intro equality
  cases equality

theorem commonClearing_projection_ne_proofCarrying_projection :
    jointCommonClearingProjection ≠ jointProofCarryingProjection := by
  intro equality
  cases equality

theorem commonClearing_projection_ne_inquiry_projection :
    jointCommonClearingProjection ≠ jointInquiryProjection := by
  intro equality
  cases equality

theorem commonClearing_projection_ne_failure_projection :
    jointCommonClearingProjection ≠ jointFailureProjection := by
  intro equality
  cases equality

theorem commonClearing_projection_distinct_from_existing_coordinates :
    jointCommonClearingProjection ≠ jointRouteOutageRestorationProjection ∧
      jointCommonClearingProjection ≠
        jointEssentialServiceRestorationProjection ∧
      jointCommonClearingProjection ≠ jointMandateProjection ∧
      jointCommonClearingProjection ≠
        jointRecognitionWitnessProjection ∧
      jointCommonClearingProjection ≠ jointUBIProjection ∧
      jointCommonClearingProjection ≠ jointProofCarryingProjection ∧
      jointCommonClearingProjection ≠ jointInquiryProjection ∧
      jointCommonClearingProjection ≠ jointFailureProjection :=
  ⟨commonClearing_projection_ne_routeOutage_projection,
    commonClearing_projection_ne_essentialService_projection,
    commonClearing_projection_ne_mandate_projection,
    commonClearing_projection_ne_recognitionWitness_projection,
    commonClearing_projection_ne_ubi_projection,
    commonClearing_projection_ne_proofCarrying_projection,
    commonClearing_projection_ne_inquiry_projection,
    commonClearing_projection_ne_failure_projection⟩

theorem clearingBackstop_projection_ne_commonClearing_projection :
    jointClearingBackstopProjection ≠ jointCommonClearingProjection := by
  intro equality
  cases equality

theorem clearingBackstop_projection_ne_routeOutage_projection :
    jointClearingBackstopProjection ≠
      jointRouteOutageRestorationProjection := by
  intro equality
  cases equality

theorem clearingBackstop_projection_ne_essentialService_projection :
    jointClearingBackstopProjection ≠
      jointEssentialServiceRestorationProjection := by
  intro equality
  cases equality

theorem clearingBackstop_projection_ne_mandate_projection :
    jointClearingBackstopProjection ≠ jointMandateProjection := by
  intro equality
  cases equality

theorem clearingBackstop_projection_ne_recognitionWitness_projection :
    jointClearingBackstopProjection ≠
      jointRecognitionWitnessProjection := by
  intro equality
  cases equality

theorem clearingBackstop_projection_ne_ubi_projection :
    jointClearingBackstopProjection ≠ jointUBIProjection := by
  intro equality
  cases equality

theorem clearingBackstop_projection_ne_proofCarrying_projection :
    jointClearingBackstopProjection ≠ jointProofCarryingProjection := by
  intro equality
  cases equality

theorem clearingBackstop_projection_ne_inquiry_projection :
    jointClearingBackstopProjection ≠ jointInquiryProjection := by
  intro equality
  cases equality

theorem clearingBackstop_projection_ne_failure_projection :
    jointClearingBackstopProjection ≠ jointFailureProjection := by
  intro equality
  cases equality

theorem clearingBackstop_projection_distinct_from_existing_coordinates :
    jointClearingBackstopProjection ≠ jointCommonClearingProjection ∧
      jointClearingBackstopProjection ≠
        jointRouteOutageRestorationProjection ∧
      jointClearingBackstopProjection ≠
        jointEssentialServiceRestorationProjection ∧
      jointClearingBackstopProjection ≠ jointMandateProjection ∧
      jointClearingBackstopProjection ≠
        jointRecognitionWitnessProjection ∧
      jointClearingBackstopProjection ≠ jointUBIProjection ∧
      jointClearingBackstopProjection ≠ jointProofCarryingProjection ∧
      jointClearingBackstopProjection ≠ jointInquiryProjection ∧
      jointClearingBackstopProjection ≠ jointFailureProjection :=
  ⟨clearingBackstop_projection_ne_commonClearing_projection,
    clearingBackstop_projection_ne_routeOutage_projection,
    clearingBackstop_projection_ne_essentialService_projection,
    clearingBackstop_projection_ne_mandate_projection,
    clearingBackstop_projection_ne_recognitionWitness_projection,
    clearingBackstop_projection_ne_ubi_projection,
    clearingBackstop_projection_ne_proofCarrying_projection,
    clearingBackstop_projection_ne_inquiry_projection,
    clearingBackstop_projection_ne_failure_projection⟩

@[simp] theorem joint_restructuringSource_is_original :
    jointAuthoritySource.restructuringSource =
      RootInquiryU8CompletionRegression.root.toAuthoritativeRoot.source.restructuringSource :=
  rfl

/-- The previous eight-coordinate inventory survives the clearing uplift
through the faithful inherited branch into the intermediate source. -/
def preBackstopInventoryInheritedByCommonClearing :
    SourceNativeProjectionLaw.InstallationAt
      routeOutageRestorationAuthoritySource.projectionLaw
      commonClearingAuthoritySource.projectionLaw :=
  inheritedByRenewal routeOutageRestorationAuthoritySource commonClearingLaw

/-- The nine-coordinate inventory, including common clearing, survives the
final backstop uplift only through the inherited branch. -/
def commonClearingInventoryInheritedByBackstop :
    SourceNativeProjectionLaw.InstallationAt
      commonClearingAuthoritySource.projectionLaw
      jointRoot.toAuthoritativeRoot.source.projectionLaw :=
  inheritedByRenewal commonClearingAuthoritySource clearingBackstopLaw

def oldInventoryInheritedByCommonClearing :
    SourceNativeProjectionLaw.InstallationAt
      routeOutageRestorationAuthoritySource.projectionLaw
      jointRoot.toAuthoritativeRoot.source.projectionLaw :=
  preBackstopInventoryInheritedByCommonClearing.trans
    commonClearingInventoryInheritedByBackstop

def renewalInstallation : SourceNativeProjectionLaw.InstallationAt
    renewalLaw.toProjectionLaw
    jointRoot.toAuthoritativeRoot.source.projectionLaw :=
  (((renewalComponent
        RootInquiryU8CompletionRegression.root.toAuthoritativeRoot.source
          renewalLaw).trans
        ((inheritedByRenewal proofCarryingAuthoritySource ubiLaw).trans
          ((inheritedByRenewal ubiAuthoritySource recognitionWitnessLaw).trans
            ((inheritedByRenewal recognitionAuthoritySource mandateLaw).trans
              (inheritedByRenewal mandateAuthoritySource
                essentialServiceRestorationLaw))))).trans
      (inheritedByRenewal essentialServiceRestorationAuthoritySource
        routeOutageRestorationLaw)).trans
    oldInventoryInheritedByCommonClearing

def ubiInstallation : SourceNativeProjectionLaw.InstallationAt
    ubiLaw.toProjectionLaw
    jointRoot.toAuthoritativeRoot.source.projectionLaw :=
  (((renewalComponent proofCarryingAuthoritySource ubiLaw).trans
        ((inheritedByRenewal ubiAuthoritySource recognitionWitnessLaw).trans
          ((inheritedByRenewal recognitionAuthoritySource mandateLaw).trans
            (inheritedByRenewal mandateAuthoritySource
              essentialServiceRestorationLaw)))).trans
      (inheritedByRenewal essentialServiceRestorationAuthoritySource
        routeOutageRestorationLaw)).trans
    oldInventoryInheritedByCommonClearing

def recognitionWitnessInstallation :
    SourceNativeProjectionLaw.InstallationAt
      recognitionWitnessLaw.toProjectionLaw
      jointRoot.toAuthoritativeRoot.source.projectionLaw :=
  (((renewalComponent ubiAuthoritySource recognitionWitnessLaw).trans
        ((inheritedByRenewal recognitionAuthoritySource mandateLaw).trans
          (inheritedByRenewal mandateAuthoritySource
            essentialServiceRestorationLaw))).trans
      (inheritedByRenewal essentialServiceRestorationAuthoritySource
        routeOutageRestorationLaw)).trans
    oldInventoryInheritedByCommonClearing

def mandateInstallation : SourceNativeProjectionLaw.InstallationAt
    mandateLaw.toProjectionLaw
    jointRoot.toAuthoritativeRoot.source.projectionLaw :=
  (((sourceMandateRenewalComponent recognitionAuthoritySource
        mandateRootShell).trans
          (inheritedByRenewal mandateAuthoritySource
            essentialServiceRestorationLaw)).trans
      (inheritedByRenewal essentialServiceRestorationAuthoritySource
        routeOutageRestorationLaw)).trans
    oldInventoryInheritedByCommonClearing

def essentialServiceRestorationInstallation :
    SourceNativeProjectionLaw.InstallationAt
      essentialServiceRestorationLaw.toProjectionLaw
      jointRoot.toAuthoritativeRoot.source.projectionLaw :=
  ((renewalComponent mandateAuthoritySource
      essentialServiceRestorationLaw).trans
      (inheritedByRenewal essentialServiceRestorationAuthoritySource
        routeOutageRestorationLaw)).trans
    oldInventoryInheritedByCommonClearing

def routeOutageRestorationInstallation :
    SourceNativeProjectionLaw.InstallationAt
      routeOutageRestorationLaw.toProjectionLaw
      jointRoot.toAuthoritativeRoot.source.projectionLaw :=
  (renewalComponent essentialServiceRestorationAuthoritySource
    routeOutageRestorationLaw).trans oldInventoryInheritedByCommonClearing

def commonClearingInstallation :
    SourceNativeProjectionLaw.InstallationAt
      commonClearingLaw.toProjectionLaw
      jointRoot.toAuthoritativeRoot.source.projectionLaw :=
  (renewalComponent routeOutageRestorationAuthoritySource
    commonClearingLaw).trans commonClearingInventoryInheritedByBackstop

def clearingBackstopInstallation :
    SourceNativeProjectionLaw.InstallationAt
      clearingBackstopLaw.toProjectionLaw
      jointRoot.toAuthoritativeRoot.source.projectionLaw :=
  renewalComponent commonClearingAuthoritySource clearingBackstopLaw

def jointRecognition : SourceNativeProofCarryingRenewalRecognitionAt
    jointRoot ResidualProcess RenewalObserver LocalConsumerAt
      LocalLifecycleAt LocalDispositionAt where
  law := renewalLaw
  installation := renewalInstallation

def ubiRecognition : SourceNativeRenewalRecognitionAt jointRoot
    M14UBIProofCarryingRootRestriction.LocalGame
    M14UBIProofCarryingRootRestriction.LocalSeed
    M14UBIProofCarryingRootRestriction.LocalSeedAt
    M14UBIProofCarryingRootRestriction.UBIConsumerAt
    M14UBIProofCarryingRootRestriction.UBIDispositionAt where
  law := ubiLaw
  installation := ubiInstallation

def recognitionWitnessRecognition : SourceNativeRenewalRecognitionAt jointRoot
    LocalGame LocalSeed LocalSeedAt RecognitionWitnessConsumerAt
      RecognitionWitnessDispositionAt where
  law := recognitionWitnessLaw
  installation := recognitionWitnessInstallation

def mandateRecognition : SourceNativeRenewalRecognitionAt jointRoot
    SourceMandateGame SourceMandateSeed SourceMandateSeedAt
      SourceMandateConsumerAt SourceMandateDispositionAt where
  law := mandateLaw
  installation := mandateInstallation

def essentialServiceRestorationRecognition :
    SourceNativeRenewalRecognitionAt jointRoot
      M14SourceEssentialServiceRestoration.LocalGame
      M14SourceEssentialServiceRestoration.LocalSeed
      M14SourceEssentialServiceRestoration.LocalSeedAt
      EssentialServiceMaintenanceConsumerAt
      EssentialServiceRestorationDispositionAt where
  law := essentialServiceRestorationLaw
  installation := essentialServiceRestorationInstallation

def routeOutageRestorationRecognition :
    SourceNativeRenewalRecognitionAt jointRoot
      M14SourceRouteOutageRestoration.LocalGame
      M14SourceRouteOutageRestoration.LocalSeed
      M14SourceRouteOutageRestoration.LocalSeedAt
      RouteOutageConsumerAt RouteRestorationDispositionAt where
  law := routeOutageRestorationLaw
  installation := routeOutageRestorationInstallation

def commonClearingRecognition :
    SourceNativeRenewalRecognitionAt jointRoot
      M14SourceCommonClearingRenewal.LocalGame
      M14SourceCommonClearingRenewal.LocalSeed
      M14SourceCommonClearingRenewal.LocalSeedAt
      CommonClearingConsumerAt CommonClearingDispositionAt where
  law := commonClearingLaw
  installation := commonClearingInstallation

def clearingBackstopRecognition :
    SourceNativeRenewalRecognitionAt jointRoot
      M14SourceClearingBackstopRenewal.LocalGame
      M14SourceClearingBackstopRenewal.LocalSeed
      M14SourceClearingBackstopRenewal.LocalSeedAt
      ClearingBackstopConsumerAt ClearingBackstopDispositionAt where
  law := clearingBackstopLaw
  installation := clearingBackstopInstallation

/-- Final-root recognition of the pre-uplift theory feedback compiler. -/
def causalTheoryRecognition : SourceNativeCausalTheoryAdoptionRecognitionAt
    jointRoot RootInquiryU8CompletionRegression.oldTheory
      ResidualProcess RenewalObserver theoryFeedbackCompiler
      RelationshipConsumerAt LocalLifecycleAt LocalDispositionAt where
  proofCarrying := jointRecognition
  lawSurface_eq := rfl

def installedRenewal : SourceInstalledRenewalAt jointRecognition jointVisit :=
  SourceInstalledRenewalAt.generate PUnit.unit rfl

def installedUBI : SourceInstalledRenewalAt ubiRecognition jointVisit :=
  SourceInstalledRenewalAt.generate PUnit.unit rfl

def installedRecognitionWitness :
    SourceInstalledRenewalAt recognitionWitnessRecognition jointVisit :=
  SourceInstalledRenewalAt.generate PUnit.unit rfl

def installedMandate : SourceInstalledRenewalAt mandateRecognition jointVisit :=
  SourceInstalledRenewalAt.generate PUnit.unit rfl

def installedEssentialServiceRestoration :
    SourceInstalledRenewalAt essentialServiceRestorationRecognition jointVisit :=
  SourceInstalledRenewalAt.generate PUnit.unit rfl

def installedRouteOutageRestoration :
    SourceInstalledRenewalAt routeOutageRestorationRecognition jointVisit :=
  SourceInstalledRenewalAt.generate PUnit.unit rfl

def installedCommonClearing :
    SourceInstalledRenewalAt commonClearingRecognition jointVisit :=
  SourceInstalledRenewalAt.generate PUnit.unit rfl

def installedClearingBackstop :
    SourceInstalledRenewalAt clearingBackstopRecognition jointVisit :=
  SourceInstalledRenewalAt.generate PUnit.unit rfl

@[simp] theorem installed_sourceEntry_eq :
    installedRenewal.payload.sourceEntry =
      RootInquiryU8CompletionRegression.entry :=
  rfl

@[simp] theorem installed_seed_eq :
    installedRenewal.payload.sourceSeed = relationshipRenewalSeed :=
  rfl

@[simp] theorem installedUBI_seed_eq :
    installedUBI.payload.sourceSeed =
      M10OccurrenceCapacityProcessFixture.focalSeed :=
  rfl

@[simp] theorem installedUBI_consumer_eq :
    installedUBI.payload.consumer = sourceGeneratedUBIRootRestriction :=
  rfl

@[simp] theorem installedUBI_disposition_eq :
    installedUBI.payload.disposition = sourceGeneratedUBIDisposition :=
  rfl

@[simp] theorem installedRecognitionWitness_seed_eq :
    installedRecognitionWitness.payload.sourceSeed = relationshipRenewalSeed :=
  rfl

@[simp] theorem installedRecognitionWitness_consumer_eq :
    installedRecognitionWitness.payload.consumer = recognitionWitnessConsumer :=
  rfl

@[simp] theorem installedRecognitionWitness_disposition_eq :
    installedRecognitionWitness.payload.disposition =
      recognitionWitnessDisposition :=
  rfl

@[simp] theorem installedMandate_seed_eq :
    installedMandate.payload.sourceSeed = sourceMandateSeed :=
  rfl

@[simp] theorem installedMandate_consumer_eq :
    installedMandate.payload.consumer = sourceMandateConsumer :=
  rfl

@[simp] theorem installedMandate_disposition_eq :
    installedMandate.payload.disposition = sourceMandateDisposition :=
  rfl

@[simp] theorem installedEssentialServiceRestoration_seed_eq :
    installedEssentialServiceRestoration.payload.sourceSeed =
      M10OccurrenceCapacityProcessFixture.focalSeed :=
  rfl

@[simp] theorem installedEssentialServiceRestoration_consumer_eq :
    installedEssentialServiceRestoration.payload.consumer =
      sourceEssentialServiceMaintenanceRestriction :=
  rfl

@[simp] theorem installedEssentialServiceRestoration_disposition_eq :
    installedEssentialServiceRestoration.payload.disposition =
      sourceGeneratedHealthServiceRestoration :=
  rfl

@[simp] theorem installedRouteOutageRestoration_seed_eq :
    installedRouteOutageRestoration.payload.sourceSeed =
      M10OccurrenceCapacityProcessFixture.focalSeed :=
  rfl

@[simp] theorem installedRouteOutageRestoration_consumer_eq :
    installedRouteOutageRestoration.payload.consumer =
      sourceRouteOutageRestriction :=
  rfl

@[simp] theorem installedRouteOutageRestoration_disposition_eq :
    installedRouteOutageRestoration.payload.disposition =
      sourceGeneratedRouteRestoration :=
  rfl

@[simp] theorem installedCommonClearing_seed_eq :
    installedCommonClearing.payload.sourceSeed = commonClearingSeed :=
  rfl

@[simp] theorem installedCommonClearing_consumer_eq :
    installedCommonClearing.payload.consumer =
      sourceCommonClearingRestriction :=
  rfl

@[simp] theorem installedCommonClearing_disposition_eq :
    installedCommonClearing.payload.disposition =
      sourceGeneratedCommonClearingDisposition :=
  rfl

@[simp] theorem installedClearingBackstop_seed_eq :
    installedClearingBackstop.payload.sourceSeed =
      sourceGeneratedClearingBackstopExactSeed :=
  rfl

@[simp] theorem installedClearingBackstop_consumer_eq :
    installedClearingBackstop.payload.consumer =
      sourceClearingBackstopRestriction :=
  rfl

@[simp] theorem installedClearingBackstop_disposition_eq :
    installedClearingBackstop.payload.disposition =
      sourceGeneratedClearingBackstopDisposition :=
  rfl

@[simp] theorem installed_coordinates_share_sourceEntry :
    installedRenewal.payload.sourceEntry = installedUBI.payload.sourceEntry :=
  rfl

theorem installed_coordinates_share_selectedRow :
    HEq installedRenewal.payload.selectedRow installedUBI.payload.selectedRow :=
  HEq.rfl

theorem installed_coordinates_share_successor :
    HEq installedRenewal.payload.successor installedUBI.payload.successor :=
  HEq.rfl

@[simp] theorem recognitionWitness_shares_sourceEntry :
    installedRecognitionWitness.payload.sourceEntry =
      installedRenewal.payload.sourceEntry :=
  rfl

theorem recognitionWitness_shares_selectedRow :
    HEq installedRecognitionWitness.payload.selectedRow
      installedRenewal.payload.selectedRow :=
  HEq.rfl

theorem recognitionWitness_shares_successor :
    HEq installedRecognitionWitness.payload.successor
      installedRenewal.payload.successor :=
  HEq.rfl

@[simp] theorem mandate_shares_sourceEntry :
    installedMandate.payload.sourceEntry =
      installedRenewal.payload.sourceEntry :=
  rfl

theorem mandate_shares_selectedRow :
    HEq installedMandate.payload.selectedRow
      installedRenewal.payload.selectedRow :=
  HEq.rfl

theorem mandate_shares_successor :
    HEq installedMandate.payload.successor
      installedRenewal.payload.successor :=
  HEq.rfl

@[simp] theorem essentialService_shares_sourceEntry :
    installedEssentialServiceRestoration.payload.sourceEntry =
      installedRenewal.payload.sourceEntry :=
  rfl

theorem essentialService_shares_selectedRow :
    HEq installedEssentialServiceRestoration.payload.selectedRow
      installedRenewal.payload.selectedRow :=
  HEq.rfl

theorem essentialService_shares_successor :
    HEq installedEssentialServiceRestoration.payload.successor
      installedRenewal.payload.successor :=
  HEq.rfl

@[simp] theorem routeOutage_shares_sourceEntry :
    installedRouteOutageRestoration.payload.sourceEntry =
      installedRenewal.payload.sourceEntry :=
  rfl

theorem routeOutage_shares_selectedRow :
    HEq installedRouteOutageRestoration.payload.selectedRow
      installedRenewal.payload.selectedRow :=
  HEq.rfl

theorem routeOutage_shares_successor :
    HEq installedRouteOutageRestoration.payload.successor
      installedRenewal.payload.successor :=
  HEq.rfl

@[simp] theorem routeOutage_shares_ubi_sourceEntry :
    installedRouteOutageRestoration.payload.sourceEntry =
      installedUBI.payload.sourceEntry :=
  rfl

theorem routeOutage_shares_ubi_selectedRow :
    HEq installedRouteOutageRestoration.payload.selectedRow
      installedUBI.payload.selectedRow :=
  HEq.rfl

theorem routeOutage_shares_ubi_successor :
    HEq installedRouteOutageRestoration.payload.successor
      installedUBI.payload.successor :=
  HEq.rfl

@[simp] theorem commonClearing_shares_sourceEntry :
    installedCommonClearing.payload.sourceEntry =
      installedRenewal.payload.sourceEntry :=
  rfl

theorem commonClearing_shares_selectedRow :
    HEq installedCommonClearing.payload.selectedRow
      installedRenewal.payload.selectedRow :=
  HEq.rfl

theorem commonClearing_shares_successor :
    HEq installedCommonClearing.payload.successor
      installedRenewal.payload.successor :=
  HEq.rfl

@[simp] theorem commonClearing_shares_mandate_sourceEntry :
    installedCommonClearing.payload.sourceEntry =
      installedMandate.payload.sourceEntry :=
  rfl

theorem commonClearing_shares_mandate_selectedRow :
    HEq installedCommonClearing.payload.selectedRow
      installedMandate.payload.selectedRow :=
  HEq.rfl

theorem commonClearing_shares_mandate_successor :
    HEq installedCommonClearing.payload.successor
      installedMandate.payload.successor :=
  HEq.rfl

@[simp] theorem clearingBackstop_shares_sourceEntry :
    installedClearingBackstop.payload.sourceEntry =
      installedRenewal.payload.sourceEntry :=
  rfl

theorem clearingBackstop_shares_selectedRow :
    HEq installedClearingBackstop.payload.selectedRow
      installedRenewal.payload.selectedRow :=
  HEq.rfl

theorem clearingBackstop_shares_successor :
    HEq installedClearingBackstop.payload.successor
      installedRenewal.payload.successor :=
  HEq.rfl

@[simp] theorem clearingBackstop_shares_commonClearing_sourceEntry :
    installedClearingBackstop.payload.sourceEntry =
      installedCommonClearing.payload.sourceEntry :=
  rfl

theorem clearingBackstop_shares_commonClearing_selectedRow :
    HEq installedClearingBackstop.payload.selectedRow
      installedCommonClearing.payload.selectedRow :=
  HEq.rfl

theorem clearingBackstop_shares_commonClearing_successor :
    HEq installedClearingBackstop.payload.successor
      installedCommonClearing.payload.successor :=
  HEq.rfl

theorem ubi_root_factorization : installedUBI.RootAnswerAndNextFactorizes :=
  installedUBI.rootAnswerAndNext_factorizes

theorem recognitionWitness_root_factorization :
    installedRecognitionWitness.RootAnswerAndNextFactorizes :=
  installedRecognitionWitness.rootAnswerAndNext_factorizes

theorem mandate_root_factorization :
    installedMandate.RootAnswerAndNextFactorizes :=
  installedMandate.rootAnswerAndNext_factorizes

theorem essentialServiceRestoration_root_factorization :
    installedEssentialServiceRestoration.RootAnswerAndNextFactorizes :=
  installedEssentialServiceRestoration.rootAnswerAndNext_factorizes

theorem routeOutageRestoration_root_factorization :
    installedRouteOutageRestoration.RootAnswerAndNextFactorizes :=
  installedRouteOutageRestoration.rootAnswerAndNext_factorizes

theorem commonClearing_root_factorization :
    installedCommonClearing.RootAnswerAndNextFactorizes :=
  installedCommonClearing.rootAnswerAndNext_factorizes

theorem clearingBackstop_root_factorization :
    installedClearingBackstop.RootAnswerAndNextFactorizes :=
  installedClearingBackstop.rootAnswerAndNext_factorizes

@[simp] theorem jointRoot_emitted_is_original :
    jointRoot.emitted = RootInquiryU8CompletionRegression.root.emitted :=
  rfl

theorem renewal_and_inquiry_share_occurrence :
    jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
        jointVisit =
      jointRoot.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
        jointVisit :=
  rfl

end
end M9ProofCarryingRenewalInquiryRoot
end Society
end ProcessGame
end SaturationMonoid
