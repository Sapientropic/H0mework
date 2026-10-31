import Mathlib.Combinatorics.Quiver.Path
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.Economy.Attractor.PeriodicViabilityRenewalReceipt

/-!
# M14 actual economic-viability action graph

The two existing death-repair receipts generate the entry arrows from their
respective source configurations to the common viable target.  The existing
periodic viability-renewal receipt generates the forward arrow to the next
viable configuration in this same Quiver.  No second graph, state registry,
target, path list, or coverage table is supplied to a producer.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ActualEconomicViabilityPath

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Renewal UBI Capacity Space CrossingCost
open M9ProofCarryingRenewalInquiryRoot
open M14UBIExitCapacityFixture
open M14UBIPeriodicRootHistory
open M14ActionableFuturePortfolio
open M14GeneratedEconomicDisposition
open M14PortfolioCaptureDeath
open M14PeriodicEssentialServiceRestoration
open M14PeriodicDeathRepairNormalization
open M14PeriodicNormalizedViableDisposition
open M14EconomicViability
open M14AdjacentEconomicViabilityBoundary
open M14PeriodicViabilityRenewalReceipt

/-! ## Existing state axes, not a new state registry -/

abbrev EconomicConfiguration :=
  Sigma fun depth : Nat => EssentialPortfolioSourceAt depth × CaptureCompiler

def maintenanceConfigurationAt (depth : Nat) : EconomicConfiguration :=
  ⟨depth, stablePortfolioSourceAt depth, noCapture⟩

def captureConfigurationAt (depth : Nat) : EconomicConfiguration :=
  ⟨depth, fullPortfolioSourceAt depth, fullCapture⟩

def repairedConfigurationAt (depth : Nat) : EconomicConfiguration :=
  ⟨depth + 1, fullPortfolioSourceAt (depth + 1), noCapture⟩

theorem maintenance_capture_configurations_distinct (depth : Nat) :
    maintenanceConfigurationAt depth ≠ captureConfigurationAt depth := by
  intro equality
  have sourceCompilerEquality :
      (stablePortfolioSourceAt depth, noCapture) =
        (fullPortfolioSourceAt depth, fullCapture) :=
    eq_of_heq (Sigma.mk.inj_iff.mp equality).2
  exact full_stable_sources_distinct depth
    (congrArg Prod.fst sourceCompilerEquality).symm

theorem maintenance_repaired_configurations_distinct (depth : Nat) :
    maintenanceConfigurationAt depth ≠ repairedConfigurationAt depth := by
  intro equality
  have depthEquality := congrArg Sigma.fst equality
  change depth = depth + 1 at depthEquality
  omega

theorem capture_repaired_configurations_distinct (depth : Nat) :
    captureConfigurationAt depth ≠ repairedConfigurationAt depth := by
  intro equality
  have depthEquality := congrArg Sigma.fst equality
  change depth = depth + 1 at depthEquality
  omega

theorem adjacent_repaired_configurations_distinct (depth : Nat) :
    repairedConfigurationAt depth ≠ repairedConfigurationAt (depth + 1) := by
  intro equality
  have depthEquality := congrArg Sigma.fst equality
  change depth + 1 = (depth + 1) + 1 at depthEquality
  omega

def EconomicConfiguration.Viable
    (configuration : EconomicConfiguration) : Type 18 :=
  EconomicViabilityAt configuration.1 configuration.2.1 configuration.2.2

abbrev ActualDeathRepairActionAt (depth : Nat) :=
  SourceGeneratedProofCarryingEssentialServiceRestorationAt depth ⊕
    ActualCaptureRepairAt depth

abbrev AdjacentBoundaryAt (depth : Nat) :=
  PeriodicViabilityBoundaryAt depth

abbrev PeriodicViabilityRenewalReceiptAt (depth : Nat) :=
  SourceGeneratedPeriodicViabilityRenewalAt depth
    (sourceGeneratedPeriodicEconomicViabilityAt depth)
    (sourceGeneratedAdjacentEconomicViabilityBoundaryAt (depth + 1))
    (sourceGeneratedPeriodicEconomicViabilityAt (depth + 1))

abbrev ActualEconomicEvolutionActionAt (depth : Nat) :=
  ActualDeathRepairActionAt depth ⊕ PeriodicViabilityRenewalReceiptAt depth

/-! ## Receipt-indexed native arrows -/

structure SourceGeneratedEconomicActionEdgeAt
    (depth : Nat)
    (boundary : AdjacentBoundaryAt depth)
    (action : ActualEconomicEvolutionActionAt depth)
    (source target : EconomicConfiguration) : Type 18 where
  private mk ::
  boundaryExact : boundary =
    sourceGeneratedAdjacentEconomicViabilityBoundaryAt depth
  actionExact :
    match action with
    | .inl (.inl service) =>
        service = boundary.entry.normalization.service
    | .inl (.inr capture) =>
        capture = boundary.entry.normalization.captureDeath.ordinaryRepair
    | .inr renewal =>
        renewal = sourceGeneratedPeriodicViabilityRenewalAt depth
  sourceExact : source =
    match action with
    | .inl (.inl _) => maintenanceConfigurationAt depth
    | .inl (.inr _) => captureConfigurationAt depth
    | .inr _ => repairedConfigurationAt depth
  targetExact : target =
    match action with
    | .inl _ => repairedConfigurationAt depth
    | .inr _ => repairedConfigurationAt (depth + 1)
  actionNextExact :
    match action with
    | .inl (.inl service) => service.applied.generatedNext =
        boundary.entry.normalization.normalForm.generatedNext
    | .inl (.inr capture) => capture.renewal.generatedNext =
        boundary.entry.normalization.normalForm.generatedNext
    | .inr renewal =>
        renewal.transition.entry.normalization.normalForm.generatedNext =
          jointRoot.generatedNextCurrentAt (temporalVisitAt (depth + 1))

abbrev SourceGeneratedEconomicActionEdge
    (source target : EconomicConfiguration) :=
  Sigma fun depth : Nat =>
      Sigma fun boundary : AdjacentBoundaryAt depth =>
      Sigma fun action : ActualEconomicEvolutionActionAt depth =>
        SourceGeneratedEconomicActionEdgeAt depth boundary action source target

instance economicActionQuiver : Quiver EconomicConfiguration where
  Hom := SourceGeneratedEconomicActionEdge

def maintenanceActionEdgeAt (depth : Nat) :
    maintenanceConfigurationAt depth ⟶ repairedConfigurationAt depth := by
  let boundary := sourceGeneratedAdjacentEconomicViabilityBoundaryAt depth
  let service := boundary.entry.normalization.service
  let action : ActualEconomicEvolutionActionAt depth := .inl (.inl service)
  let edge : SourceGeneratedEconomicActionEdgeAt depth boundary action
      (maintenanceConfigurationAt depth) (repairedConfigurationAt depth) :=
    { boundaryExact := rfl
      actionExact := rfl
      sourceExact := rfl
      targetExact := rfl
      actionNextExact := boundary.entry.normalization.normalForm.nextIsService.symm }
  exact ⟨depth, boundary, action, edge⟩

def captureActionEdgeAt (depth : Nat) :
    captureConfigurationAt depth ⟶ repairedConfigurationAt depth := by
  let boundary := sourceGeneratedAdjacentEconomicViabilityBoundaryAt depth
  let capture := boundary.entry.normalization.captureDeath.ordinaryRepair
  let action : ActualEconomicEvolutionActionAt depth := .inl (.inr capture)
  let edge : SourceGeneratedEconomicActionEdgeAt depth boundary action
      (captureConfigurationAt depth) (repairedConfigurationAt depth) :=
    { boundaryExact := rfl
      actionExact := rfl
      sourceExact := rfl
      targetExact := rfl
      actionNextExact := boundary.entry.normalization.normalForm.nextIsCapture.symm }
  exact ⟨depth, boundary, action, edge⟩

/-- The already viable target at `depth` performs the next whole-root
renewal inside the same economic-action quiver. -/
def viabilityRenewalActionEdgeAt (depth : Nat) :
    repairedConfigurationAt depth ⟶ repairedConfigurationAt (depth + 1) := by
  let boundary := sourceGeneratedAdjacentEconomicViabilityBoundaryAt depth
  let renewal := sourceGeneratedPeriodicViabilityRenewalAt depth
  let action : ActualEconomicEvolutionActionAt depth := .inr renewal
  let edge : SourceGeneratedEconomicActionEdgeAt depth boundary action
      (repairedConfigurationAt depth) (repairedConfigurationAt (depth + 1)) :=
    { boundaryExact := rfl
      actionExact := rfl
      sourceExact := rfl
      targetExact := rfl
      actionNextExact := renewal.generatedNextExact }
  exact ⟨depth, boundary, action, edge⟩

/-! ## Exact-source negatives -/

instance serviceAction_captureSourceEdge_isEmpty
    (depth : Nat)
    (boundary : AdjacentBoundaryAt depth)
    (service : SourceGeneratedProofCarryingEssentialServiceRestorationAt depth)
    (target : EconomicConfiguration) :
    IsEmpty (SourceGeneratedEconomicActionEdgeAt depth boundary
      (.inl (.inl service))
      (captureConfigurationAt depth) target) :=
  ⟨fun edge =>
    maintenance_capture_configurations_distinct depth edge.sourceExact.symm⟩

instance captureAction_maintenanceSourceEdge_isEmpty
    (depth : Nat)
    (boundary : AdjacentBoundaryAt depth)
    (capture : ActualCaptureRepairAt depth)
    (target : EconomicConfiguration) :
    IsEmpty (SourceGeneratedEconomicActionEdgeAt depth boundary
      (.inl (.inr capture))
      (maintenanceConfigurationAt depth) target) :=
  ⟨fun edge =>
    maintenance_capture_configurations_distinct depth edge.sourceExact⟩

theorem service_receipt_cannot_index_capture_source
    (depth : Nat)
    (boundary : AdjacentBoundaryAt depth)
    (service : SourceGeneratedProofCarryingEssentialServiceRestorationAt depth)
    (target : EconomicConfiguration) :
    IsEmpty (SourceGeneratedEconomicActionEdgeAt depth boundary
      (.inl (.inl service))
      (captureConfigurationAt depth) target) :=
  serviceAction_captureSourceEdge_isEmpty depth boundary service target

theorem capture_repair_cannot_index_maintenance_source
    (depth : Nat)
    (boundary : AdjacentBoundaryAt depth)
    (capture : ActualCaptureRepairAt depth)
    (target : EconomicConfiguration) :
    IsEmpty (SourceGeneratedEconomicActionEdgeAt depth boundary
      (.inl (.inr capture))
      (maintenanceConfigurationAt depth) target) :=
  captureAction_maintenanceSourceEdge_isEmpty depth boundary capture target

instance serviceAction_repairedSourceEdge_isEmpty
    (depth : Nat)
    (boundary : AdjacentBoundaryAt depth)
    (service : SourceGeneratedProofCarryingEssentialServiceRestorationAt depth)
    (target : EconomicConfiguration) :
    IsEmpty (SourceGeneratedEconomicActionEdgeAt depth boundary
      (.inl (.inl service)) (repairedConfigurationAt depth) target) :=
  ⟨fun edge =>
    maintenance_repaired_configurations_distinct depth edge.sourceExact.symm⟩

instance captureAction_repairedSourceEdge_isEmpty
    (depth : Nat)
    (boundary : AdjacentBoundaryAt depth)
    (capture : ActualCaptureRepairAt depth)
    (target : EconomicConfiguration) :
    IsEmpty (SourceGeneratedEconomicActionEdgeAt depth boundary
      (.inl (.inr capture)) (repairedConfigurationAt depth) target) :=
  ⟨fun edge =>
    capture_repaired_configurations_distinct depth edge.sourceExact.symm⟩

theorem death_repair_actions_cannot_start_from_viable_source
    (depth : Nat)
    (boundary : AdjacentBoundaryAt depth)
    (service : SourceGeneratedProofCarryingEssentialServiceRestorationAt depth)
    (capture : ActualCaptureRepairAt depth)
    (target : EconomicConfiguration) :
    IsEmpty (SourceGeneratedEconomicActionEdgeAt depth boundary
        (.inl (.inl service)) (repairedConfigurationAt depth) target) ∧
      IsEmpty (SourceGeneratedEconomicActionEdgeAt depth boundary
        (.inl (.inr capture)) (repairedConfigurationAt depth) target) :=
  ⟨serviceAction_repairedSourceEdge_isEmpty depth boundary service target,
    captureAction_repairedSourceEdge_isEmpty depth boundary capture target⟩

instance viabilityRenewalAction_maintenanceSourceEdge_isEmpty
    (depth : Nat)
    (boundary : AdjacentBoundaryAt depth)
    (renewal : PeriodicViabilityRenewalReceiptAt depth)
    (target : EconomicConfiguration) :
    IsEmpty (SourceGeneratedEconomicActionEdgeAt depth boundary (.inr renewal)
      (maintenanceConfigurationAt depth) target) :=
  ⟨fun edge =>
    maintenance_repaired_configurations_distinct depth edge.sourceExact⟩

instance viabilityRenewalAction_captureSourceEdge_isEmpty
    (depth : Nat)
    (boundary : AdjacentBoundaryAt depth)
    (renewal : PeriodicViabilityRenewalReceiptAt depth)
    (target : EconomicConfiguration) :
    IsEmpty (SourceGeneratedEconomicActionEdgeAt depth boundary (.inr renewal)
      (captureConfigurationAt depth) target) :=
  ⟨fun edge =>
    capture_repaired_configurations_distinct depth edge.sourceExact⟩

theorem viability_renewal_cannot_index_maintenance_source
    (depth : Nat)
    (boundary : AdjacentBoundaryAt depth)
    (renewal : PeriodicViabilityRenewalReceiptAt depth)
    (target : EconomicConfiguration) :
    IsEmpty (SourceGeneratedEconomicActionEdgeAt depth boundary (.inr renewal)
      (maintenanceConfigurationAt depth) target) :=
  viabilityRenewalAction_maintenanceSourceEdge_isEmpty
    depth boundary renewal target

theorem viability_renewal_cannot_index_capture_source
    (depth : Nat)
    (boundary : AdjacentBoundaryAt depth)
    (renewal : PeriodicViabilityRenewalReceiptAt depth)
    (target : EconomicConfiguration) :
    IsEmpty (SourceGeneratedEconomicActionEdgeAt depth boundary (.inr renewal)
      (captureConfigurationAt depth) target) :=
  viabilityRenewalAction_captureSourceEdge_isEmpty
    depth boundary renewal target

instance viabilityRenewalAction_sameTargetEdge_isEmpty
    (depth : Nat)
    (boundary : AdjacentBoundaryAt depth)
    (renewal : PeriodicViabilityRenewalReceiptAt depth)
    (source : EconomicConfiguration) :
    IsEmpty (SourceGeneratedEconomicActionEdgeAt depth boundary (.inr renewal)
      source (repairedConfigurationAt depth)) :=
  ⟨fun edge =>
    adjacent_repaired_configurations_distinct depth edge.targetExact⟩

theorem viability_renewal_cannot_stay_at_same_viable_target
    (depth : Nat)
    (boundary : AdjacentBoundaryAt depth)
    (renewal : PeriodicViabilityRenewalReceiptAt depth)
    (source : EconomicConfiguration) :
    IsEmpty (SourceGeneratedEconomicActionEdgeAt depth boundary (.inr renewal)
      source (repairedConfigurationAt depth)) :=
  viabilityRenewalAction_sameTargetEdge_isEmpty
    depth boundary renewal source

def maintenanceActualActionAt (depth : Nat) : ActualDeathRepairActionAt depth :=
  .inl (sourceGeneratedAdjacentEconomicViabilityBoundaryAt depth
    |>.entry.normalization.service)

def captureActualActionAt (depth : Nat) : ActualDeathRepairActionAt depth :=
  .inr (sourceGeneratedAdjacentEconomicViabilityBoundaryAt depth
    |>.entry.normalization.captureDeath.ordinaryRepair)

theorem maintenance_capture_actions_distinct (depth : Nat) :
    maintenanceActualActionAt depth ≠ captureActualActionAt depth := by
  intro equality
  cases equality

def maintenanceEconomicEvolutionActionAt (depth : Nat) :
    ActualEconomicEvolutionActionAt depth :=
  .inl (maintenanceActualActionAt depth)

def captureEconomicEvolutionActionAt (depth : Nat) :
    ActualEconomicEvolutionActionAt depth :=
  .inl (captureActualActionAt depth)

def viabilityRenewalActualActionAt (depth : Nat) :
    ActualEconomicEvolutionActionAt depth :=
  .inr (sourceGeneratedPeriodicViabilityRenewalAt depth)

@[simp] theorem maintenanceActionEdge_action (depth : Nat) :
    (maintenanceActionEdgeAt depth).2.2.1 =
      maintenanceEconomicEvolutionActionAt depth :=
  rfl

@[simp] theorem captureActionEdge_action (depth : Nat) :
    (captureActionEdgeAt depth).2.2.1 =
      captureEconomicEvolutionActionAt depth :=
  rfl

@[simp] theorem viabilityRenewalActionEdge_action (depth : Nat) :
    (viabilityRenewalActionEdgeAt depth).2.2.1 =
      viabilityRenewalActualActionAt depth :=
  rfl

theorem three_economic_evolution_actions_pairwise_distinct (depth : Nat) :
    maintenanceEconomicEvolutionActionAt depth ≠
        captureEconomicEvolutionActionAt depth ∧
      maintenanceEconomicEvolutionActionAt depth ≠
        viabilityRenewalActualActionAt depth ∧
      captureEconomicEvolutionActionAt depth ≠
        viabilityRenewalActualActionAt depth := by
  constructor
  · exact fun equality =>
      maintenance_capture_actions_distinct depth (Sum.inl.inj equality)
  constructor <;> intro equality <;> cases equality

theorem three_actual_edge_actions_pairwise_distinct (depth : Nat) :
    (maintenanceActionEdgeAt depth).2.2.1 ≠
        (captureActionEdgeAt depth).2.2.1 ∧
      (maintenanceActionEdgeAt depth).2.2.1 ≠
        (viabilityRenewalActionEdgeAt depth).2.2.1 ∧
      (captureActionEdgeAt depth).2.2.1 ≠
        (viabilityRenewalActionEdgeAt depth).2.2.1 := by
  change maintenanceEconomicEvolutionActionAt depth ≠
      captureEconomicEvolutionActionAt depth ∧
    maintenanceEconomicEvolutionActionAt depth ≠
      viabilityRenewalActualActionAt depth ∧
    captureEconomicEvolutionActionAt depth ≠
      viabilityRenewalActualActionAt depth
  exact three_economic_evolution_actions_pairwise_distinct depth

end
end M14ActualEconomicViabilityPath
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ActualEconomicViabilityPath.maintenanceActionEdgeAt
#print axioms SaturationMonoid.ProcessGame.Society.M14ActualEconomicViabilityPath.captureActionEdgeAt
#print axioms SaturationMonoid.ProcessGame.Society.M14ActualEconomicViabilityPath.service_receipt_cannot_index_capture_source
#print axioms SaturationMonoid.ProcessGame.Society.M14ActualEconomicViabilityPath.capture_repair_cannot_index_maintenance_source
#print axioms SaturationMonoid.ProcessGame.Society.M14ActualEconomicViabilityPath.viabilityRenewalActionEdgeAt
#print axioms SaturationMonoid.ProcessGame.Society.M14ActualEconomicViabilityPath.death_repair_actions_cannot_start_from_viable_source
#print axioms SaturationMonoid.ProcessGame.Society.M14ActualEconomicViabilityPath.viability_renewal_cannot_index_maintenance_source
#print axioms SaturationMonoid.ProcessGame.Society.M14ActualEconomicViabilityPath.viability_renewal_cannot_stay_at_same_viable_target
#print axioms SaturationMonoid.ProcessGame.Society.M14ActualEconomicViabilityPath.three_economic_evolution_actions_pairwise_distinct
#print axioms SaturationMonoid.ProcessGame.Society.M14ActualEconomicViabilityPath.three_actual_edge_actions_pairwise_distinct
