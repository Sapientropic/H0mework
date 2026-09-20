import H0mework.Physics.GravityTail.FixedRootNativeWrite
import H0mework.Physics.Dirac.DiracMatterSpatialEnergyBalance
import H0mework.Physics.Revision.InquirySource

/-!
# Fixed gravity-tail canonical living answer-next root
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace PhysicsCore
namespace StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailLivingRoot

open ResponsibilityLifecycle
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ProofFreeRicherAnholonomicSource
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGlobalOperator
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailRootNativeWrite
open StageNineDiracDualFormNativeCartanECSynchronizedGravityTailJointPathOperator
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField

noncomputable section

private abbrev Source : SmoothUnifiedSource := positiveSmoothUnifiedSource

theorem rootEntry_subsingleton
    (support : N.Support) : Subsingleton (OpenResponsibilityAt N support) :=
  ⟨fun left right =>
    (rootLedgerEntry_unique support left).trans
      (rootLedgerEntry_unique support right).symm⟩

private def restructuringLaw : SourceNativeLedgerRestructuringLaw rootSource :=
  identityOnlyWorldLedgerRestructuringLaw rootSource Source <| by
    intro support responsibility
    constructor
    rintro ⟨left⟩ ⟨right⟩
    rfl

def restructuringCertification
    {current : V.Current}
    (occurrence : rootSource.toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerRestructuringCertificationAt restructuringLaw
      (rootLedgerCompiler.compile occurrence) := by
  rcases occurrence with ⟨support, event⟩
  change RootNativeEventAt current support at event
  cases event.support_eq
  rcases current with ⟨state⟩
  cases state <;>
    exact ExactLedgerRestructuringCertificationAt.ofInjective
      (fun left right _ => (rootEntry_subsingleton _).elim left right)
      (fun left right _ => (rootEntry_subsingleton _).elim left right)

private def restructuringCompiler :
    SourceNativeRestructuringLedgerCompiler rootSource where
  ledgerCompiler := rootLedgerCompiler
  restructuringLaw := restructuringLaw
  certifyRestructuring := restructuringCertification

private def restructuringSource : SourceNativeRestructuringLedgerSource N V where
  source := rootSource
  compiler := restructuringCompiler

/-- The authoritative faces exposed by the fixed Stage Nine root.

The residual is not an adjacent diagnostic field: it is compiled at the same
current and occurrence as the whole-ledger evolution.  The complete physical
configuration is retained before any pointwise restriction; the matter face
does not install a completed trajectory. -/
inductive RootProjectionCoordinate
  | source
  | configuration
  | ledger
  | residual
  | inquiryCompilation
  | inquiryConsumer
  | cartanAction
  | matter
      (time : ℝ)
      (space :
        StageNineDiracMatterSpatialEnergyBalance.DiracMatterSpatialCoordinates)

/-- Pointwise matter restriction of one physical root current. -/
def rootMatterFaceAt
    (current : RootCurrent)
    (time : ℝ)
    (space :
      StageNineDiracMatterSpatialEnergyBalance.DiracMatterSpatialCoordinates) :
    MatterCoordinateCarrier :=
  matterCoordinateEquiv
    ((current.configuration).matter
      (StageNineDiracMatterSpatialEnergyBalance.diracMatterSpacetimeCoordinatePoint
        time space))

/-- Whole-ledger and gravity/assembly residual faces of one actual root
occurrence. -/
private def projectionLaw :
    SourceNativeProjectionLaw restructuringSource.toLedgerSource where
  Projection := RootProjectionCoordinate
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {current} occurrence _ =>
    match projection with
    | .source => SmoothUnifiedSource
    | .configuration => StageNineHolonomicConfiguration
    | .ledger => SourceNativeLedgerEvolutionAt rootSource occurrence
    | .residual => RootResidualPayload
    | .inquiryCompilation =>
        Stage9C.Revision.InquirySource.ConfigurationTokenAt occurrence
    | .inquiryConsumer =>
        RootInquiryCompletion.SourceNativeInquiryAnswerConsumerTokenAt PUnit.unit
          (ULift.up.{1, 0} occurrence) (rootLedgerEntry current) current.configuration
    | .cartanAction =>
        Stage9C.Revision.InquirySource.ConfigurationTokenAt occurrence
    | .matter _ _ => MatterCoordinateCarrier
  project := fun projection {current} occurrence _ =>
    match projection with
    | .source => N.anchorAt current
    | .configuration => current.configuration
    | .ledger => rootLedgerCompiler.compile occurrence
    | .residual => rootResidualAt current
    | .inquiryCompilation => Stage9C.Revision.InquirySource.configurationToken occurrence
    | .inquiryConsumer => Stage9C.Revision.InquirySource.configurationConsumerToken occurrence
    | .cartanAction => Stage9C.Revision.InquirySource.cartanActionToken occurrence
    | .matter time space => rootMatterFaceAt current time space

private def authoritySource : SourceNativeAuthoritySource N V where
  restructuringSource := restructuringSource
  eventInventoryAdmission :=
    .reflOfNoFaithfulTerminal restructuringSource
      (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := .rootSemantic N
  projectionLaw := projectionLaw

def authoritativeRoot : SourceNativeAuthoritativeRootClosure N V where
  source := authoritySource
  emitted := rootEmitted
  compiler_commutes := by
    intro current
    rcases current with ⟨state⟩
    cases state <;> rfl

/-- The complete Stage-Eight source and continuous-contact enrichment are one
dependent face of every fixed-root occurrence. -/
@[simp] theorem source_projection_eq
    (current : V.Current) :
    authoritativeRoot.projectionOutcomeAt .source current =
      .inl ⟨PUnit.unit, N.anchorAt current⟩ :=
  rfl

/-- The complete physical current is a dependent face of the same emitted
occurrence as its ledger, residual and pointwise matter restrictions. -/
@[simp] theorem configuration_projection_eq
    (current : V.Current) :
    authoritativeRoot.projectionOutcomeAt .configuration current =
      .inl ⟨PUnit.unit, current.configuration⟩ :=
  rfl

/-- The field residual is a literal dependent face of the same emitted root
occurrence.  No separate Physics carrier or authority receipt is involved. -/
@[simp] theorem residual_projection_eq
    (current : V.Current) :
    authoritativeRoot.projectionOutcomeAt .residual current =
      .inl ⟨PUnit.unit, rootResidualAt current⟩ :=
  rfl

/-- The pointwise matter field is read from the same emitted occurrence as
the ledger and residual. -/
@[simp] theorem matter_projection_eq
    (current : V.Current)
    (time : ℝ)
    (space :
      StageNineDiracMatterSpatialEnergyBalance.DiracMatterSpatialCoordinates) :
    authoritativeRoot.projectionOutcomeAt (.matter time space) current =
      .inl ⟨PUnit.unit, rootMatterFaceAt current time space⟩ :=
  rfl

def livingRoot : SourceNativeLivingRootClosure N V :=
  authoritativeRoot.toLivingWithoutFaithfulTerminal <| fun _ =>
    ⟨fun terminal => nomatch terminal⟩

def livingInitialVisit : SourceNativeTemporalVisitAt
    livingRoot.toAuthoritativeRoot.toLedgerRoot :=
  .finite livingRoot.toAuthoritativeRoot.toRoot.initialVisit

/-- The canonical temporal successor inside the fixed physical root. -/
def livingRootNextVisit
    (visit : SourceNativeTemporalVisitAt
      livingRoot.toAuthoritativeRoot.toLedgerRoot) :
    SourceNativeTemporalVisitAt
      livingRoot.toAuthoritativeRoot.toLedgerRoot :=
  visit.next (next := Next visit.current) <| by
    rcases visit with ⟨current, history⟩
    rcases current with ⟨state⟩
    cases state <;> rfl

@[simp] theorem livingRootNextVisit_current_eq
    (visit : SourceNativeTemporalVisitAt
      livingRoot.toAuthoritativeRoot.toLedgerRoot) :
    (livingRootNextVisit visit).current = Next visit.current :=
  rfl

/-- Physics does not choose a sibling root after observing the action.  The
source compiler's next package is exactly the successor visit of this same
authoritative root. -/
theorem livingRoot_generated_next_eq
    (visit : SourceNativeTemporalVisitAt
      livingRoot.toAuthoritativeRoot.toLedgerRoot) :
    livingRoot.generatedNextCurrentAt visit =
      { V := V
        root := authoritativeRoot
        visit := livingRootNextVisit visit } := by
  rcases visit with ⟨current, history⟩
  rcases current with ⟨state⟩
  cases state <;> rfl

/-- One temporal occurrence exposes the current residual, performs the exact
whole-ledger write-back, and generates the target residual in the same root.
No adjacent Physics authority or post-hoc effect projection is involved. -/
theorem livingRoot_residual_answer_and_next
    (visit : SourceNativeTemporalVisitAt
      livingRoot.toAuthoritativeRoot.toLedgerRoot) :
    livingRoot.generatedNextCurrentAt visit =
        { V := V
          root := authoritativeRoot
          visit := livingRootNextVisit visit } ∧
      authoritativeRoot.projectionOutcomeAt .residual visit.current =
        .inl ⟨PUnit.unit, rootResidualAt visit.current⟩ ∧
      HEq
        (livingRoot.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
          visit).wholeLedgerWriteBack
        (rootLedgerCompiler.compile (rootEmitted visit.current)) ∧
      authoritativeRoot.projectionOutcomeAt .residual
          (livingRootNextVisit visit).current =
        .inl ⟨PUnit.unit, rootResidualAt (Next visit.current)⟩ := by
  rcases visit with ⟨current, history⟩
  rcases current with ⟨state⟩
  cases state <;> exact ⟨rfl, rfl, HEq.rfl, rfl⟩

@[simp] theorem livingRoot_initial_next_eq_quadraticCoface :
    (livingRoot.generatedNextCurrentAt livingInitialVisit).visit.current =
      quadraticCofaceCurrent :=
  by
    unfold SourceNativeLivingRootClosure.generatedNextCurrentAt
    rfl

@[simp] theorem livingRoot_initial_next_keeps_same_vocabulary :
    (livingRoot.generatedNextCurrentAt livingInitialVisit).V = V :=
  rfl

end
end StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailLivingRoot
end PhysicsCore
end SaturationMonoid
