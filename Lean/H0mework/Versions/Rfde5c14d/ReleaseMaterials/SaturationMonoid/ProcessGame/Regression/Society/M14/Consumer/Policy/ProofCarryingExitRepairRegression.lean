import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Policy.TenureCaptureRouteRepairNoGoRegression

/-!
# M14 source-aware proof-carrying exit repair

The repair no-go has one positive exit: retain the exact causal origin.
Pattern matching that origin generates the canonical repair without reading
the visible capacity.  Existing geometry then proves its outcome capacity is
exactly one and that no other repair is effective for the same cause.

The proof-carrying interface indexes the repair rather than storing a policy
table.  It is a counterfactual geometry certificate, not an actual law update,
legislative first write, or self-U8 execution.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingExitRepairRegression

noncomputable section

open UBI Capacity Policy
open M14UBIPeriodicRootHistory
open M14TenureCaptureRouteRepairNoGoRegression

/-- Sole repair selector with causal authority.  The exact origin first
generates its failure kind; the repair is then compiled by the UBI
restriction already installed at this temporal visit.  No visible capacity
readout participates. -/
def canonicalRepairAt {depth : Nat}
    (origin : RepairFailureOriginAt depth) : ExactExitRepair :=
  (periodicUBISourceAt depth).installed.payload.consumer.repairAt
    origin.failureKind

theorem canonical_repair_outcome_eq_one
    {depth : Nat} (origin : RepairFailureOriginAt depth) :
    repairOutcomeCapacityAt depth origin (canonicalRepairAt origin) = 1 := by
  cases origin with
  | tenureCapture _ => exact remove_capture_repairs_tenure_at depth
  | routeBottleneck _ => exact restore_route_repairs_bottleneck_at depth

theorem canonical_repair_is_effective
    {depth : Nat} (origin : RepairFailureOriginAt depth) :
    EffectiveRepairAt depth origin (canonicalRepairAt origin) := by
  unfold EffectiveRepairAt
  rw [canonical_repair_outcome_eq_one]
  omega

theorem effective_repair_iff_eq_canonical
    {depth : Nat} (origin : RepairFailureOriginAt depth)
    (repair : ExactExitRepair) :
    EffectiveRepairAt depth origin repair ↔
      repair = canonicalRepairAt origin := by
  cases origin with
  | tenureCapture _ => exact tenure_effective_repair_iff depth repair
  | routeBottleneck _ => exact route_effective_repair_iff depth repair

/-- A repair proof is indexed by the exact cause and candidate repair.  The
constructor is private and accepts no capacity/effectiveness proof. -/
structure SourceGeneratedProofCarryingExitRepairAt
    {depth : Nat} (origin : RepairFailureOriginAt depth)
    (repair : ExactExitRepair) : Prop where
  private mk ::
  repair_eq : repair = canonicalRepairAt origin
  outcome_eq_one : repairOutcomeCapacityAt depth origin repair = 1
  uniqueEffective : ∀ candidate : ExactExitRepair,
    EffectiveRepairAt depth origin candidate → candidate = repair

namespace SourceGeneratedProofCarryingExitRepairAt

theorem generate {depth : Nat} (origin : RepairFailureOriginAt depth) :
    SourceGeneratedProofCarryingExitRepairAt origin
      (canonicalRepairAt origin) where
  repair_eq := rfl
  outcome_eq_one := canonical_repair_outcome_eq_one origin
  uniqueEffective := by
    intro candidate effective
    exact (effective_repair_iff_eq_canonical origin candidate).1 effective

theorem effective
    {depth : Nat} {origin : RepairFailureOriginAt depth}
    {repair : ExactExitRepair}
    (proof : SourceGeneratedProofCarryingExitRepairAt origin repair) :
    EffectiveRepairAt depth origin repair := by
  unfold EffectiveRepairAt
  rw [proof.outcome_eq_one]
  omega

theorem candidate_eq_canonical
    {depth : Nat} {origin : RepairFailureOriginAt depth}
    {repair : ExactExitRepair}
    (proof : SourceGeneratedProofCarryingExitRepairAt origin repair) :
    repair = canonicalRepairAt origin :=
  proof.repair_eq

end SourceGeneratedProofCarryingExitRepairAt

theorem exact_causes_generate_different_repairs (depth : Nat) :
    canonicalRepairAt (tenureCaptureOriginAt depth) ≠
      canonicalRepairAt (routeBottleneckOriginAt depth) := by
  intro equality
  cases equality

theorem same_capacity_but_different_canonical_repairs (depth : Nat) :
    failureCapacityReadoutAt depth (tenureCaptureOriginAt depth) =
        failureCapacityReadoutAt depth (routeBottleneckOriginAt depth) ∧
      canonicalRepairAt (tenureCaptureOriginAt depth) ≠
        canonicalRepairAt (routeBottleneckOriginAt depth) :=
  ⟨failure_readouts_equal depth, exact_causes_generate_different_repairs depth⟩

/-- Forgetting the cause destroys even reconstruction of the canonical
proof-carrying repair, not only arbitrary effectiveness selection. -/
theorem no_capacity_only_canonical_repair_reconstruction (depth : Nat) :
    ¬ ∃ reconstruct : Nat → ExactExitRepair,
      ∀ origin : RepairFailureOriginAt depth,
        reconstruct (failureCapacityReadoutAt depth origin) =
          canonicalRepairAt origin := by
  rintro ⟨reconstruct, exact⟩
  have tenureExact := exact (tenureCaptureOriginAt depth)
  have routeExact := exact (routeBottleneckOriginAt depth)
  have repairsEqual :
      canonicalRepairAt (tenureCaptureOriginAt depth) =
        canonicalRepairAt (routeBottleneckOriginAt depth) := by
    calc
      _ = reconstruct
          (failureCapacityReadoutAt depth (tenureCaptureOriginAt depth)) :=
        tenureExact.symm
      _ = reconstruct
          (failureCapacityReadoutAt depth (routeBottleneckOriginAt depth)) :=
        congrArg reconstruct (failure_readouts_equal depth)
      _ = _ := routeExact
  exact exact_causes_generate_different_repairs depth repairsEqual

structure ProofCarryingExitRepairCertificate : Prop where
  everyDepthEveryCause : ∀ (depth : Nat)
    (origin : RepairFailureOriginAt depth),
    SourceGeneratedProofCarryingExitRepairAt origin (canonicalRepairAt origin)
  everyCanonicalOutcomeExact : ∀ (depth : Nat)
    (origin : RepairFailureOriginAt depth),
    repairOutcomeCapacityAt depth origin (canonicalRepairAt origin) = 1
  everyEffectiveRepairUnique : ∀ (depth : Nat)
    (origin : RepairFailureOriginAt depth) (candidate : ExactExitRepair),
    EffectiveRepairAt depth origin candidate ↔
      candidate = canonicalRepairAt origin
  sameReadoutDifferentRepairs : ∀ depth : Nat,
    failureCapacityReadoutAt depth (tenureCaptureOriginAt depth) =
        failureCapacityReadoutAt depth (routeBottleneckOriginAt depth) ∧
      canonicalRepairAt (tenureCaptureOriginAt depth) ≠
        canonicalRepairAt (routeBottleneckOriginAt depth)
  noCapacityOnlyReconstruction : ∀ depth : Nat,
    ¬ ∃ reconstruct : Nat → ExactExitRepair,
      ∀ origin : RepairFailureOriginAt depth,
        reconstruct (failureCapacityReadoutAt depth origin) =
          canonicalRepairAt origin

theorem proofCarryingExitRepairDirectConsumer :
    ProofCarryingExitRepairCertificate where
  everyDepthEveryCause := fun _depth origin =>
    SourceGeneratedProofCarryingExitRepairAt.generate origin
  everyCanonicalOutcomeExact := fun _depth origin =>
    canonical_repair_outcome_eq_one origin
  everyEffectiveRepairUnique := fun _depth origin candidate =>
    effective_repair_iff_eq_canonical origin candidate
  sameReadoutDifferentRepairs := same_capacity_but_different_canonical_repairs
  noCapacityOnlyReconstruction :=
    no_capacity_only_canonical_repair_reconstruction

end
end M14ProofCarryingExitRepairRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingExitRepairRegression.SourceGeneratedProofCarryingExitRepairAt.generate
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingExitRepairRegression.no_capacity_only_canonical_repair_reconstruction
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingExitRepairRegression.proofCarryingExitRepairDirectConsumer
