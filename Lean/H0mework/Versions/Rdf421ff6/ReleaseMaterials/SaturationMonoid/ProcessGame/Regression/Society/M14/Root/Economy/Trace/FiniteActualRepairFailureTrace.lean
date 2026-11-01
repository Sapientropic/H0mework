import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.Economy.Occurrence.ActualRepairFailureOccurrence

/-!
# M14 finite paired actual repair-failure trace

Every generated temporal depth now emits two actual failure faces: tenure
capture in the UBI coordinate and route outage in the independent route
coordinate.  They share one exact root occurrence while retaining distinct
failure kinds, projections, and repairs.

The dependent failure trace is duplicate-free.  Bare root projection is
intentionally non-faithful at each depth; branchwise root traces remain
duplicate-free, and stamping the root occurrence with the existing failure
kind restores duplicate-freedom for the full paired trace.  The requested
finite horizon is not stored as a schedule or completed future.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14FiniteActualRepairFailureTrace

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Renewal UBI Policy
open M9ProofCarryingRenewalInquiryRoot
open M14UBIPeriodicRootHistory
open M14TenureCaptureRouteRepairNoGoRegression
open M14ActualRepairFailureOccurrence

/-! ## Full actual support -/

def actualRepairSupportAt (depth : Nat) :
    Set (RepairFailureOriginAt depth) :=
  {origin | Nonempty (ActualRepairFailureAt depth origin)}

theorem actualRepairFailure_nonempty
    (depth : Nat) (origin : RepairFailureOriginAt depth) :
    Nonempty (ActualRepairFailureAt depth origin) :=
  every_origin_has_actualRepairFailure depth origin

theorem actualRepairSupport_eq_univ (depth : Nat) :
    actualRepairSupportAt depth = Set.univ := by
  ext origin
  change Nonempty (ActualRepairFailureAt depth origin) ↔ True
  exact ⟨fun _ => trivial, fun _ => actualRepairFailure_nonempty depth origin⟩

/-! ## Dependent actual occurrences -/

abbrev AnyActualRepairFailure :=
  Sigma fun depth : Nat =>
    Sigma fun origin : RepairFailureOriginAt depth =>
      ActualRepairFailureAt depth origin

namespace AnyActualRepairFailure

def depth (occurrence : AnyActualRepairFailure) : Nat := occurrence.1

def origin (occurrence : AnyActualRepairFailure) :
    RepairFailureOriginAt occurrence.depth := occurrence.2.1

def actual (occurrence : AnyActualRepairFailure) :
    ActualRepairFailureAt occurrence.depth occurrence.origin := occurrence.2.2

def failureKind (occurrence : AnyActualRepairFailure) :
    ExactExitFailureKind := occurrence.origin.failureKind

abbrev AnyExactRootOccurrence := ExactTemporalCausalRootEvent
  jointRoot.toAuthoritativeRoot.toLedgerRoot

def erasedRootOccurrence (occurrence : AnyActualRepairFailure) :
    AnyExactRootOccurrence :=
  ⟨temporalVisitAt occurrence.depth, occurrence.actual.rootOccurrence⟩

abbrev StampedRootOccurrence :=
  ExactExitFailureKind × AnyExactRootOccurrence

def stampedRootOccurrence (occurrence : AnyActualRepairFailure) :
    StampedRootOccurrence :=
  (occurrence.failureKind, occurrence.erasedRootOccurrence)

end AnyActualRepairFailure

def tenureRepairFailureOccurrenceAt (depth : Nat) :
    AnyActualRepairFailure :=
  ⟨depth, tenureCaptureOriginAt depth,
    sourceGeneratedActualTenureRepairFailureAt depth⟩

def routeRepairFailureOccurrenceAt (depth : Nat) :
    AnyActualRepairFailure :=
  ⟨depth, routeBottleneckOriginAt depth,
    sourceGeneratedActualRouteRepairFailureAt depth⟩

@[simp] theorem tenureRepairFailureOccurrenceAt_depth (depth : Nat) :
    (tenureRepairFailureOccurrenceAt depth).depth = depth := rfl

@[simp] theorem routeRepairFailureOccurrenceAt_depth (depth : Nat) :
    (routeRepairFailureOccurrenceAt depth).depth = depth := rfl

@[simp] theorem tenureRepairFailureOccurrenceAt_failureKind (depth : Nat) :
    (tenureRepairFailureOccurrenceAt depth).failureKind =
      ExactExitFailureKind.tenureCapture := rfl

@[simp] theorem routeRepairFailureOccurrenceAt_failureKind (depth : Nat) :
    (routeRepairFailureOccurrenceAt depth).failureKind =
      ExactExitFailureKind.routeBottleneck := rfl

theorem tenureRepairFailureOccurrenceAt_injective :
    Function.Injective tenureRepairFailureOccurrenceAt := by
  intro left right equality
  exact congrArg Sigma.fst equality

theorem routeRepairFailureOccurrenceAt_injective :
    Function.Injective routeRepairFailureOccurrenceAt := by
  intro left right equality
  exact congrArg Sigma.fst equality

/-! ## Requested paired finite prefix -/

def finiteActualTenureRepairFailureTrace (horizon : Nat) :
    List AnyActualRepairFailure :=
  (List.range horizon).map tenureRepairFailureOccurrenceAt

def finiteActualRouteRepairFailureTrace (horizon : Nat) :
    List AnyActualRepairFailure :=
  (List.range horizon).map routeRepairFailureOccurrenceAt

/-- Sole paired-trace producer. -/
def sourceGeneratedFiniteActualRepairFailureTrace (horizon : Nat) :
    List AnyActualRepairFailure :=
  finiteActualTenureRepairFailureTrace horizon ++
    finiteActualRouteRepairFailureTrace horizon

@[simp] theorem finiteActualRepairFailureTrace_length (horizon : Nat) :
    (sourceGeneratedFiniteActualRepairFailureTrace horizon).length =
      2 * horizon := by
  simp [sourceGeneratedFiniteActualRepairFailureTrace,
    finiteActualTenureRepairFailureTrace,
    finiteActualRouteRepairFailureTrace, Nat.two_mul]

theorem mem_finiteActualTenureRepairFailureTrace_iff
    {horizon : Nat} {occurrence : AnyActualRepairFailure} :
    occurrence ∈ finiteActualTenureRepairFailureTrace horizon ↔
      ∃ depth : Nat, depth < horizon ∧
        occurrence = tenureRepairFailureOccurrenceAt depth := by
  constructor
  · intro membership
    rcases List.mem_map.mp membership with ⟨depth, depthMem, equality⟩
    exact ⟨depth, List.mem_range.mp depthMem, equality.symm⟩
  · rintro ⟨depth, depthLt, rfl⟩
    exact List.mem_map.mpr ⟨depth, List.mem_range.mpr depthLt, rfl⟩

theorem mem_finiteActualRouteRepairFailureTrace_iff
    {horizon : Nat} {occurrence : AnyActualRepairFailure} :
    occurrence ∈ finiteActualRouteRepairFailureTrace horizon ↔
      ∃ depth : Nat, depth < horizon ∧
        occurrence = routeRepairFailureOccurrenceAt depth := by
  constructor
  · intro membership
    rcases List.mem_map.mp membership with ⟨depth, depthMem, equality⟩
    exact ⟨depth, List.mem_range.mp depthMem, equality.symm⟩
  · rintro ⟨depth, depthLt, rfl⟩
    exact List.mem_map.mpr ⟨depth, List.mem_range.mpr depthLt, rfl⟩

theorem mem_pairedTrace_iff
    {horizon : Nat} {occurrence : AnyActualRepairFailure} :
    occurrence ∈ sourceGeneratedFiniteActualRepairFailureTrace horizon ↔
      ∃ depth < horizon,
        occurrence = tenureRepairFailureOccurrenceAt depth ∨
        occurrence = routeRepairFailureOccurrenceAt depth := by
  constructor
  · intro membership
    rcases List.mem_append.mp membership with tenureMem | routeMem
    · rcases mem_finiteActualTenureRepairFailureTrace_iff.mp tenureMem with
        ⟨depth, depthLt, equality⟩
      exact ⟨depth, depthLt, Or.inl equality⟩
    · rcases mem_finiteActualRouteRepairFailureTrace_iff.mp routeMem with
        ⟨depth, depthLt, equality⟩
      exact ⟨depth, depthLt, Or.inr equality⟩
  · rintro ⟨depth, depthLt, equality | equality⟩
    · rw [equality]
      exact List.mem_append_left _
        (mem_finiteActualTenureRepairFailureTrace_iff.mpr
          ⟨depth, depthLt, rfl⟩)
    · rw [equality]
      exact List.mem_append_right _
        (mem_finiteActualRouteRepairFailureTrace_iff.mpr
          ⟨depth, depthLt, rfl⟩)

theorem tenureOccurrence_mem_pairedTrace_iff
    {horizon depth : Nat} :
    tenureRepairFailureOccurrenceAt depth ∈
        sourceGeneratedFiniteActualRepairFailureTrace horizon ↔
      depth < horizon := by
  constructor
  · intro membership
    rcases List.mem_append.mp membership with tenureMem | routeMem
    · rcases mem_finiteActualTenureRepairFailureTrace_iff.mp tenureMem with
        ⟨index, indexLt, equality⟩
      have depthEquality :=
        congrArg AnyActualRepairFailure.depth equality
      have depthEquality' : depth = index := by
        simpa using depthEquality
      rw [depthEquality']
      exact indexLt
    · rcases mem_finiteActualRouteRepairFailureTrace_iff.mp routeMem with
        ⟨index, _indexLt, equality⟩
      have kindEquality := congrArg AnyActualRepairFailure.failureKind equality
      cases kindEquality
  · intro depthLt
    exact List.mem_append_left _
      (mem_finiteActualTenureRepairFailureTrace_iff.mpr
        ⟨depth, depthLt, rfl⟩)

theorem routeOccurrence_mem_pairedTrace_iff
    {horizon depth : Nat} :
    routeRepairFailureOccurrenceAt depth ∈
        sourceGeneratedFiniteActualRepairFailureTrace horizon ↔
      depth < horizon := by
  constructor
  · intro membership
    rcases List.mem_append.mp membership with tenureMem | routeMem
    · rcases mem_finiteActualTenureRepairFailureTrace_iff.mp tenureMem with
        ⟨index, _indexLt, equality⟩
      have kindEquality := congrArg AnyActualRepairFailure.failureKind equality
      cases kindEquality
    · rcases mem_finiteActualRouteRepairFailureTrace_iff.mp routeMem with
        ⟨index, indexLt, equality⟩
      have depthEquality :=
        congrArg AnyActualRepairFailure.depth equality
      have depthEquality' : depth = index := by
        simpa using depthEquality
      rw [depthEquality']
      exact indexLt
  · intro depthLt
    exact List.mem_append_right _
      (mem_finiteActualRouteRepairFailureTrace_iff.mpr
        ⟨depth, depthLt, rfl⟩)

theorem finiteActualTenureRepairFailureTrace_nodup (horizon : Nat) :
    (finiteActualTenureRepairFailureTrace horizon).Nodup :=
  List.nodup_range.map tenureRepairFailureOccurrenceAt_injective

theorem finiteActualRouteRepairFailureTrace_nodup (horizon : Nat) :
    (finiteActualRouteRepairFailureTrace horizon).Nodup :=
  List.nodup_range.map routeRepairFailureOccurrenceAt_injective

theorem tenure_route_failure_traces_disjoint (horizon : Nat) :
    List.Disjoint (finiteActualTenureRepairFailureTrace horizon)
      (finiteActualRouteRepairFailureTrace horizon) := by
  rw [List.disjoint_left]
  intro occurrence tenureMem routeMem
  rcases mem_finiteActualTenureRepairFailureTrace_iff.mp tenureMem with
    ⟨tenureDepth, _tenureLt, tenureEq⟩
  rcases mem_finiteActualRouteRepairFailureTrace_iff.mp routeMem with
    ⟨routeDepth, _routeLt, routeEq⟩
  have equality : tenureRepairFailureOccurrenceAt tenureDepth =
      routeRepairFailureOccurrenceAt routeDepth :=
    tenureEq.symm.trans routeEq
  have kindEquality := congrArg AnyActualRepairFailure.failureKind equality
  cases kindEquality

theorem finiteActualRepairFailureTrace_nodup (horizon : Nat) :
    (sourceGeneratedFiniteActualRepairFailureTrace horizon).Nodup :=
  (finiteActualTenureRepairFailureTrace_nodup horizon).append
    (finiteActualRouteRepairFailureTrace_nodup horizon)
    (tenure_route_failure_traces_disjoint horizon)

/-! ## Bare and stamped root readouts -/

theorem sameDepth_tenure_route_rootOccurrence_equal (depth : Nat) :
    (tenureRepairFailureOccurrenceAt depth).erasedRootOccurrence =
      (routeRepairFailureOccurrenceAt depth).erasedRootOccurrence := by
  apply Sigma.ext
  · rfl
  · exact heq_of_eq
      (canonical_actual_pair_shared_root_distinct_authority depth).1

def tenureRepairFailureRootOccurrenceAt (depth : Nat) :
    AnyActualRepairFailure.AnyExactRootOccurrence :=
  (tenureRepairFailureOccurrenceAt depth).erasedRootOccurrence

def routeRepairFailureRootOccurrenceAt (depth : Nat) :
    AnyActualRepairFailure.AnyExactRootOccurrence :=
  (routeRepairFailureOccurrenceAt depth).erasedRootOccurrence

theorem tenureRepairFailureRootOccurrenceAt_injective :
    Function.Injective tenureRepairFailureRootOccurrenceAt := by
  intro left right equality
  exact temporalVisitAt_injective (congrArg Sigma.fst equality)

theorem routeRepairFailureRootOccurrenceAt_injective :
    Function.Injective routeRepairFailureRootOccurrenceAt := by
  intro left right equality
  exact temporalVisitAt_injective (congrArg Sigma.fst equality)

def finiteActualTenureRepairFailureRootTrace (horizon : Nat) :=
  (finiteActualTenureRepairFailureTrace horizon).map
    AnyActualRepairFailure.erasedRootOccurrence

def finiteActualRouteRepairFailureRootTrace (horizon : Nat) :=
  (finiteActualRouteRepairFailureTrace horizon).map
    AnyActualRepairFailure.erasedRootOccurrence

theorem finiteActualTenureRepairFailureRootTrace_nodup (horizon : Nat) :
    (finiteActualTenureRepairFailureRootTrace horizon).Nodup := by
  unfold finiteActualTenureRepairFailureRootTrace
    finiteActualTenureRepairFailureTrace
  rw [List.map_map]
  exact List.nodup_range.map tenureRepairFailureRootOccurrenceAt_injective

theorem finiteActualRouteRepairFailureRootTrace_nodup (horizon : Nat) :
    (finiteActualRouteRepairFailureRootTrace horizon).Nodup := by
  unfold finiteActualRouteRepairFailureRootTrace
    finiteActualRouteRepairFailureTrace
  rw [List.map_map]
  exact List.nodup_range.map routeRepairFailureRootOccurrenceAt_injective

/-- The full bare-root readout necessarily repeats each positive-depth
pair's common root.  Authority stamping is therefore required, not cosmetic. -/
def finiteActualRepairFailureBareRootTrace (horizon : Nat) :
    List AnyActualRepairFailure.AnyExactRootOccurrence :=
  (sourceGeneratedFiniteActualRepairFailureTrace horizon).map
    AnyActualRepairFailure.erasedRootOccurrence

theorem finiteActualRepairFailureBareRootTrace_not_nodup
    {horizon : Nat} (positive : 0 < horizon) :
    ¬ (finiteActualRepairFailureBareRootTrace horizon).Nodup := by
  intro nodup
  have appendedNodup :
      (finiteActualTenureRepairFailureRootTrace horizon ++
        finiteActualRouteRepairFailureRootTrace horizon).Nodup := by
    simpa [finiteActualRepairFailureBareRootTrace,
      sourceGeneratedFiniteActualRepairFailureTrace,
      finiteActualTenureRepairFailureRootTrace,
      finiteActualRouteRepairFailureRootTrace, List.map_append] using nodup
  have disjoint := appendedNodup.disjoint
  have tenureMem : tenureRepairFailureRootOccurrenceAt 0 ∈
      finiteActualTenureRepairFailureRootTrace horizon := by
    unfold finiteActualTenureRepairFailureRootTrace
      finiteActualTenureRepairFailureTrace
    rw [List.map_map]
    change tenureRepairFailureRootOccurrenceAt 0 ∈
      (List.range horizon).map tenureRepairFailureRootOccurrenceAt
    exact List.mem_map.mpr
      ⟨0, List.mem_range.mpr positive, rfl⟩
  have routeOwnMem : routeRepairFailureRootOccurrenceAt 0 ∈
      finiteActualRouteRepairFailureRootTrace horizon := by
    unfold finiteActualRouteRepairFailureRootTrace
      finiteActualRouteRepairFailureTrace
    rw [List.map_map]
    change routeRepairFailureRootOccurrenceAt 0 ∈
      (List.range horizon).map routeRepairFailureRootOccurrenceAt
    exact List.mem_map.mpr
      ⟨0, List.mem_range.mpr positive, rfl⟩
  have sameRoot : tenureRepairFailureRootOccurrenceAt 0 =
      routeRepairFailureRootOccurrenceAt 0 :=
    sameDepth_tenure_route_rootOccurrence_equal 0
  have routeMem : tenureRepairFailureRootOccurrenceAt 0 ∈
      finiteActualRouteRepairFailureRootTrace horizon := by
    rw [sameRoot]
    exact routeOwnMem
  exact (List.disjoint_left.mp disjoint) tenureMem routeMem

def tenureStampedRootOccurrenceAt (depth : Nat) :
    AnyActualRepairFailure.StampedRootOccurrence :=
  (tenureRepairFailureOccurrenceAt depth).stampedRootOccurrence

def routeStampedRootOccurrenceAt (depth : Nat) :
    AnyActualRepairFailure.StampedRootOccurrence :=
  (routeRepairFailureOccurrenceAt depth).stampedRootOccurrence

theorem tenureStampedRootOccurrenceAt_injective :
    Function.Injective tenureStampedRootOccurrenceAt := by
  intro left right equality
  exact temporalVisitAt_injective
    (congrArg (fun stamped => stamped.2.1) equality)

theorem routeStampedRootOccurrenceAt_injective :
    Function.Injective routeStampedRootOccurrenceAt := by
  intro left right equality
  exact temporalVisitAt_injective
    (congrArg (fun stamped => stamped.2.1) equality)

def finiteActualRepairFailureStampedRootTrace (horizon : Nat) :
    List AnyActualRepairFailure.StampedRootOccurrence :=
  (sourceGeneratedFiniteActualRepairFailureTrace horizon).map
    AnyActualRepairFailure.stampedRootOccurrence

theorem finiteActualRepairFailureStampedRootTrace_nodup (horizon : Nat) :
    (finiteActualRepairFailureStampedRootTrace horizon).Nodup := by
  have tenureNodup :
      ((List.range horizon).map tenureStampedRootOccurrenceAt).Nodup :=
    List.nodup_range.map tenureStampedRootOccurrenceAt_injective
  have routeNodup :
      ((List.range horizon).map routeStampedRootOccurrenceAt).Nodup :=
    List.nodup_range.map routeStampedRootOccurrenceAt_injective
  have disjoint : List.Disjoint
      ((List.range horizon).map tenureStampedRootOccurrenceAt)
      ((List.range horizon).map routeStampedRootOccurrenceAt) := by
    rw [List.disjoint_left]
    intro stamped tenureMem routeMem
    rcases List.mem_map.mp tenureMem with
      ⟨tenureDepth, _tenureMem, tenureEq⟩
    rcases List.mem_map.mp routeMem with
      ⟨routeDepth, _routeMem, routeEq⟩
    have kindEquality := congrArg Prod.fst (tenureEq.trans routeEq.symm)
    cases kindEquality
  unfold finiteActualRepairFailureStampedRootTrace
    sourceGeneratedFiniteActualRepairFailureTrace
    finiteActualTenureRepairFailureTrace
    finiteActualRouteRepairFailureTrace
  rw [List.map_append, List.map_map, List.map_map]
  exact tenureNodup.append routeNodup disjoint

/-! ## Pointwise exact provenance -/

theorem finiteActualRepairFailureTrace_member_exact
    {horizon : Nat} {occurrence : AnyActualRepairFailure}
    (membership : occurrence ∈
      sourceGeneratedFiniteActualRepairFailureTrace horizon) :
    occurrence.depth < horizon ∧
      (occurrence.failureKind = ExactExitFailureKind.tenureCapture ∨
        occurrence.failureKind = ExactExitFailureKind.routeBottleneck) ∧
      occurrence.actual.rootOccurrence =
        jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
          (temporalVisitAt occurrence.depth) ∧
      ActualRepairFailureAt.SourceConsumerExactAt occurrence.origin
        occurrence.actual ∧
      ActualRepairFailureAt.InstalledActionExactAt occurrence.origin
        occurrence.actual ∧
      ActualRepairFailureAt.SelectedWriteCommutesAt occurrence.origin
        occurrence.actual ∧
      ActualRepairFailureAt.RootFactorizesAt occurrence.origin
        occurrence.actual ∧
      ActualRepairFailureAt.ComponentOutcomeExactAt occurrence.origin
        occurrence.actual ∧
      HEq occurrence.actual.wholeLedgerWriteBack
        (jointRoot.toAuthoritativeRoot.toLedgerRoot
          |>.generatedAtTemporalVisit
            (temporalVisitAt occurrence.depth)).wholeLedgerWriteBack ∧
      occurrence.actual.generatedNext =
        jointRoot.generatedNextCurrentAt
          (temporalVisitAt occurrence.depth) := by
  rcases List.mem_append.mp membership with tenureMem | routeMem
  · rcases mem_finiteActualTenureRepairFailureTrace_iff.mp tenureMem with
      ⟨depth, depthLt, rfl⟩
    exact
      ⟨depthLt, Or.inl rfl,
        actualRepairFailure_rootOccurrence_exact _,
        ActualRepairFailureAt.sourceConsumerExact _,
        ActualRepairFailureAt.installedActionExact _,
        ActualRepairFailureAt.selectedWriteCommutes _,
        ActualRepairFailureAt.rootFactorizes _,
        ActualRepairFailureAt.componentOutcomeExact _,
        actualRepairFailure_wholeLedger_exact _,
        actualRepairFailure_generatedNext_exact _⟩
  · rcases mem_finiteActualRouteRepairFailureTrace_iff.mp routeMem with
      ⟨depth, depthLt, rfl⟩
    exact
      ⟨depthLt, Or.inr rfl,
        actualRepairFailure_rootOccurrence_exact _,
        ActualRepairFailureAt.sourceConsumerExact _,
        ActualRepairFailureAt.installedActionExact _,
        ActualRepairFailureAt.selectedWriteCommutes _,
        ActualRepairFailureAt.rootFactorizes _,
        ActualRepairFailureAt.componentOutcomeExact _,
        actualRepairFailure_wholeLedger_exact _,
        actualRepairFailure_generatedNext_exact _⟩

theorem finiteActualRepairFailureTrace_mouth_has_no_schedule_or_measure
    (horizon : Nat) : True := by
  let trace := sourceGeneratedFiniteActualRepairFailureTrace horizon
  fail_if_success exact trace.completedFuture
  fail_if_success exact trace.schedule
  fail_if_success exact trace.occurrenceRegistry
  fail_if_success exact trace.coverage
  fail_if_success exact trace.measure
  fail_if_success exact trace.weights
  fail_if_success exact trace.probability
  fail_if_success exact trace.terminal
  trivial

end
end M14FiniteActualRepairFailureTrace
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14FiniteActualRepairFailureTrace.actualRepairSupport_eq_univ
#print axioms SaturationMonoid.ProcessGame.Society.M14FiniteActualRepairFailureTrace.mem_pairedTrace_iff
#print axioms SaturationMonoid.ProcessGame.Society.M14FiniteActualRepairFailureTrace.finiteActualRepairFailureTrace_nodup
#print axioms SaturationMonoid.ProcessGame.Society.M14FiniteActualRepairFailureTrace.sameDepth_tenure_route_rootOccurrence_equal
#print axioms SaturationMonoid.ProcessGame.Society.M14FiniteActualRepairFailureTrace.finiteActualRepairFailureBareRootTrace_not_nodup
#print axioms SaturationMonoid.ProcessGame.Society.M14FiniteActualRepairFailureTrace.finiteActualRepairFailureStampedRootTrace_nodup
#print axioms SaturationMonoid.ProcessGame.Society.M14FiniteActualRepairFailureTrace.finiteActualRepairFailureTrace_member_exact
