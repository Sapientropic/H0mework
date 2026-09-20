import H0mework.Realization.Relations.FintypeDerivation
import H0mework.Arithmetic.SourceAdmission.CanonicalPreP950RawCoordinates

/-!
# Pre-realization Borromean source core

This file freezes the source-side interface *before* endpoint realization,
P950 holonomy payloads, Boolean atomicity checks, tensor irreducibility, prime
readout, or Goldbach/RAAPD atom pairs enter the dependency graph.

The separation is deliberate:

* the legacy `ConcreteBorromeanReturnFreePositiveCoreGeometry` is a
  realization-carrying diagnostic mouth;
* the core below contains only source dynamics, raw SU(7)-shaped coordinates,
  a two-ring phase cochain, and sigma-interval data;
* a current-shell certificate is pointwise in `k`, and carries raw energy
  `k + 2`; it is not a bounded all-shell family;
* endpoint-realization consumers must cross an explicit stage capability.

The raw branch/incidence/cell types come from the dependency-light canonical
pre-P950 coordinate module.  Importing the later historical SU(7) branching
cell would also import the long physical/holonomy proposition chain; importing
the historical phase chain would pull unrelated layers into this frozen mouth.
-/

namespace RepresentationArithmeticAtomProjectionDefect
namespace BorromeanPreRealization

universe u v w

/-! ## Type-level realization boundary -/

/-- Proof stages relevant to the positive Borromean route. -/
inductive BorromeanPositiveCoreStage where
  | preRealization
  | realizationCarrying
  deriving DecidableEq, Repr

/-- Endpoint realization is forbidden at the pre-realization stage and
allowed only after an explicit realization-carrying upgrade. -/
def EndpointRealizationAllowed : BorromeanPositiveCoreStage -> Prop
  | .preRealization => False
  | .realizationCarrying => True

/-- Capability required by new direct endpoint-realization APIs.

There is deliberately no inhabitant at `.preRealization`. -/
class EndpointRealizationCapability
    (stage : BorromeanPositiveCoreStage) : Prop where
  allowed : EndpointRealizationAllowed stage

/-- The realization-carrying stage has the expected capability. -/
instance : EndpointRealizationCapability .realizationCarrying where
  allowed := trivial

/-- A pre-realization core cannot carry endpoint-realization authority. -/
theorem noEndpointRealizationCapabilityAtPreRealization :
    Not (EndpointRealizationCapability .preRealization) := by
  intro capability
  exact capability.allowed

/-- Explicit wrapper for a diagnostic direct-realization mouth.

Legacy cores which already contain endpoint producers belong in this wrapper.
Source-only theorems must not accept it as their input. -/
structure DiagnosticDirectRealizationMouth
    (stage : BorromeanPositiveCoreStage) (EndpointPayload : Type w) where
  capability : EndpointRealizationCapability stage
  payload : EndpointPayload

/-- Construct a diagnostic mouth only at the realization-carrying stage. -/
def DiagnosticDirectRealizationMouth.ofRealizationCarrying
    {EndpointPayload : Type w} (payload : EndpointPayload) :
    DiagnosticDirectRealizationMouth .realizationCarrying EndpointPayload where
  capability := inferInstance
  payload := payload

/-- The type-level guard makes a diagnostic direct-realization mouth empty at
the source-only stage. -/
instance diagnosticDirectRealizationMouthIsEmptyAtPreRealization
    (EndpointPayload : Type w) :
    IsEmpty
      (DiagnosticDirectRealizationMouth .preRealization EndpointPayload) where
  false mouth :=
    noEndpointRealizationCapabilityAtPreRealization mouth.capability

/-! ## Compatibility names for canonical pre-P950 coordinates -/

/-- Backward-compatible name for the canonical pre-P950 Schubert syntax. -/
abbrev PreRealizationSU3Branch := CanonicalPreP950SU3Branch

/-- Backward-compatible name for the canonical pre-P950 incidence syntax. -/
abbrev PreRealizationSU7Incidence := CanonicalPreP950SU7Incidence

/-- Backward-compatible name for the canonical pre-P950 raw branching cell. -/
abbrev PreRealizationSU7BranchingCell :=
  CanonicalPreP950SU7BranchingCell

/-- Signed raw residual of a source branching cell from the even fiber. -/
def preRealizationRawResidual
    {n : Nat} (cell : PreRealizationSU7BranchingCell n) : Int :=
  canonicalPreP950RawResidual cell

/-- Absolute raw source energy.  This formula is kept local so the source core
does not import the later atomic/holonomy enumeration chain. -/
def preRealizationRawEnergy
    {n : Nat} (cell : PreRealizationSU7BranchingCell n) : Nat :=
  canonicalPreP950RawEnergy cell

/-- The local raw-energy formula unfolds to the endpoint-code residual
formula.  A later adapter must prove this equals the canonical SU(7) readout.
-/
theorem preRealizationRawEnergy_eq
    {n : Nat} (cell : PreRealizationSU7BranchingCell n) :
    preRealizationRawEnergy cell =
      Int.natAbs
        (((cell.leftWeightCode + cell.rightWeightCode : Nat) : Int) -
          ((2 * n : Nat) : Int)) := by
  rfl

/-! ## Minimal two-ring phase syntax -/

/-- Three time positions of one source phase ring. -/
inductive PreRealizationThreeCycleTime where
  | t0
  | t1
  | t2
  deriving DecidableEq, Repr, FintypeViaProxy

/-- Residual accumulated around one directed three-cycle. -/
def preRealizationThreeCycleResidual
    (cochain :
      PreRealizationThreeCycleTime ->
        PreRealizationThreeCycleTime -> Int) : Int :=
  cochain .t0 .t1 + cochain .t1 .t2 + cochain .t2 .t0

/-- Restrict a two-ring cochain to its left component. -/
def preRealizationLeftSelectedCochain
    {A : Type*}
    (cochain :
      Sum PreRealizationThreeCycleTime PreRealizationThreeCycleTime ->
        Sum PreRealizationThreeCycleTime PreRealizationThreeCycleTime -> A) :
    PreRealizationThreeCycleTime ->
      PreRealizationThreeCycleTime -> A :=
  fun i j => cochain (Sum.inl i) (Sum.inl j)

/-- Restrict a two-ring cochain to its right component. -/
def preRealizationRightSelectedCochain
    {A : Type*}
    (cochain :
      Sum PreRealizationThreeCycleTime PreRealizationThreeCycleTime ->
        Sum PreRealizationThreeCycleTime PreRealizationThreeCycleTime -> A) :
    PreRealizationThreeCycleTime ->
      PreRealizationThreeCycleTime -> A :=
  fun i j => cochain (Sum.inr i) (Sum.inr j)

/-! ## Genuine source/phase geometry -/

/-- Source-side Borromean geometry before any endpoint realization.

The core is independent of `k` and has no `targetBound`: it therefore cannot
smuggle an all-shell coverage law into a current-shell producer.  The
`sourceBound` index is used only by pointwise certificates below.
-/
structure ConcreteBorromeanPreRealizationSourceCoreGeometry
    (K : Type v) [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (sigma : K) (n sourceBound : Nat) where
  sigma_pos : 0 < sigma
  sigma_lt_one : sigma < 1
  SourceState : Type u
  initialState : SourceState
  nextState : SourceState -> SourceState
  source_path_faithful : SourcePathFaithful nextState
  branchingCellOf : SourceState -> PreRealizationSU7BranchingCell n
  branch_preserved :
    forall state,
      (branchingCellOf (nextState state)).branch =
        (branchingCellOf state).branch
  incidence_preserved :
    forall state,
      (branchingCellOf (nextState state)).incidence =
        (branchingCellOf state).incidence
  componentCochainOf :
    SourceState ->
      Sum PreRealizationThreeCycleTime PreRealizationThreeCycleTime ->
        Sum PreRealizationThreeCycleTime PreRealizationThreeCycleTime -> Int

namespace ConcreteBorromeanPreRealizationSourceCoreGeometry

variable {K : Type v} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {sigma : K} {n sourceBound : Nat}

/-- One deterministic source transition. -/
def sourceStep
    (G :
      ConcreteBorromeanPreRealizationSourceCoreGeometry
        K sigma n sourceBound) :
    G.SourceState -> G.SourceState -> Prop :=
  fun current next => next = G.nextState current

/-- The branch coordinate is invariant under one source transition. -/
theorem sourceStep_branch_preserved
    (G :
      ConcreteBorromeanPreRealizationSourceCoreGeometry
        K sigma n sourceBound)
    {current next : G.SourceState}
    (step : G.sourceStep current next) :
    (G.branchingCellOf next).branch =
      (G.branchingCellOf current).branch := by
  subst next
  exact G.branch_preserved current

/-- The incidence coordinate is invariant under one source transition. -/
theorem sourceStep_incidence_preserved
    (G :
      ConcreteBorromeanPreRealizationSourceCoreGeometry
        K sigma n sourceBound)
    {current next : G.SourceState}
    (step : G.sourceStep current next) :
    (G.branchingCellOf next).incidence =
      (G.branchingCellOf current).incidence := by
  subst next
  exact G.incidence_preserved current

/-- The branch coordinate remains coherent along an arbitrary generated
source path, not only across one transition. -/
theorem reachable_branch_preserved
    (G :
      ConcreteBorromeanPreRealizationSourceCoreGeometry
        K sigma n sourceBound)
    {state : G.SourceState}
    (reachable :
      Relation.ReflTransGen G.sourceStep G.initialState state) :
    (G.branchingCellOf state).branch =
      (G.branchingCellOf G.initialState).branch := by
  induction reachable with
  | refl => rfl
  | tail _ step ih =>
      exact (G.sourceStep_branch_preserved step).trans ih

/-- The incidence coordinate remains coherent along an arbitrary generated
source path, not only across one transition. -/
theorem reachable_incidence_preserved
    (G :
      ConcreteBorromeanPreRealizationSourceCoreGeometry
        K sigma n sourceBound)
    {state : G.SourceState}
    (reachable :
      Relation.ReflTransGen G.sourceStep G.initialState state) :
    (G.branchingCellOf state).incidence =
      (G.branchingCellOf G.initialState).incidence := by
  induction reachable with
  | refl => rfl
  | tail _ step ih =>
      exact (G.sourceStep_incidence_preserved step).trans ih

/-- A raw cell is generated at one exact source state when that state is
reachable from the geometry's initial state and the cell is the geometry's
own branching-cell readout at that state.

This predicate is strictly L0: it mentions no Boolean endpoint check,
generated list, canonical-rich/P950 witness, endpoint projection, Factor
realization, repair cell, or atom pair. -/
def SourceGeneratedCurrentCell
    (G :
      ConcreteBorromeanPreRealizationSourceCoreGeometry
        K sigma n sourceBound)
    (state : G.SourceState)
    (cell : PreRealizationSU7BranchingCell n) : Prop :=
  Relation.ReflTransGen G.sourceStep G.initialState state ∧
    cell = G.branchingCellOf state

/-- A pointwise current-shell certificate.

For shell key `k`, the source layer supplies one reachable raw cell at source
energy `k + 2`.  It does not supply a family for every key, endpoint atomhood,
or the later same-key `k + 1` projection equality. -/
structure SU7CurrentShellSourceCertificate
    (G :
      ConcreteBorromeanPreRealizationSourceCoreGeometry
        K sigma n sourceBound)
    (k : Nat) where
  state : G.SourceState
  reachable :
    Relation.ReflTransGen G.sourceStep G.initialState state
  left_code_bounded :
    (G.branchingCellOf state).leftWeightCode <= sourceBound
  right_code_bounded :
    (G.branchingCellOf state).rightWeightCode <= sourceBound
  left_component_residual_zero :
    preRealizationThreeCycleResidual
        (preRealizationLeftSelectedCochain
          (G.componentCochainOf state)) = 0
  right_component_residual_zero :
    preRealizationThreeCycleResidual
        (preRealizationRightSelectedCochain
          (G.componentCochainOf state)) = 0
  source_energy_successor :
    preRealizationRawEnergy (G.branchingCellOf state) = k + 2

namespace SU7CurrentShellSourceCertificate

/-- Exact L0 expansion of a current-shell source certificate.

The witness exposes the real raw cell and every source-only responsibility
needed by Task A: same-state reachability, sigma admissibility, crystal branch
and incidence coherence, code-room bounds, two-component phase closure, and
raw energy `k + 2`.  This is an elimination theorem for an already generated
certificate; it deliberately does not manufacture that certificate from a
bare runtime proposition or a downstream active cell. -/
theorem exists_sourceGeneratedCurrentCell
    (G :
      ConcreteBorromeanPreRealizationSourceCoreGeometry
        K sigma n sourceBound)
    {k : Nat}
    (certificate : SU7CurrentShellSourceCertificate G k) :
    ∃ cell : PreRealizationSU7BranchingCell n,
      SourceGeneratedCurrentCell G certificate.state cell ∧
        0 < sigma ∧
        sigma < 1 ∧
        cell.branch = (G.branchingCellOf G.initialState).branch ∧
        cell.incidence = (G.branchingCellOf G.initialState).incidence ∧
        cell.leftWeightCode ≤ sourceBound ∧
        cell.rightWeightCode ≤ sourceBound ∧
        preRealizationThreeCycleResidual
            (preRealizationLeftSelectedCochain
              (G.componentCochainOf certificate.state)) = 0 ∧
        preRealizationThreeCycleResidual
            (preRealizationRightSelectedCochain
              (G.componentCochainOf certificate.state)) = 0 ∧
        preRealizationRawEnergy cell = k + 2 := by
  refine ⟨G.branchingCellOf certificate.state, ?_⟩
  exact
    ⟨⟨certificate.reachable, rfl⟩,
      G.sigma_pos,
      G.sigma_lt_one,
      G.reachable_branch_preserved certificate.reachable,
      G.reachable_incidence_preserved certificate.reachable,
      certificate.left_code_bounded,
      certificate.right_code_bounded,
      certificate.left_component_residual_zero,
      certificate.right_component_residual_zero,
      certificate.source_energy_successor⟩

end SU7CurrentShellSourceCertificate

/-- Thin source datum exported by the pre-realization interface.

This record is intentionally weaker than the existing P950-backed
`SU7ThinSourceFeasibleDatum`: it stores no generated active cell and no
holonomy/atomicity payload. -/
structure SU7PreRealizationThinSourceDatum
    (n sourceBound sourceEnergy : Nat) where
  sourceCell : PreRealizationSU7BranchingCell n
  left_code_bounded : sourceCell.leftWeightCode <= sourceBound
  right_code_bounded : sourceCell.rightWeightCode <= sourceBound
  componentCochain :
    Sum PreRealizationThreeCycleTime PreRealizationThreeCycleTime ->
      Sum PreRealizationThreeCycleTime PreRealizationThreeCycleTime -> Int
  left_component_residual_zero :
    preRealizationThreeCycleResidual
        (preRealizationLeftSelectedCochain componentCochain) = 0
  right_component_residual_zero :
    preRealizationThreeCycleResidual
        (preRealizationRightSelectedCochain componentCochain) = 0
  affine_energy : preRealizationRawEnergy sourceCell = sourceEnergy

/-- Forget reachability while preserving exactly the pointwise raw source and
phase data.  This conversion performs no endpoint realization. -/
def SU7CurrentShellSourceCertificate.toThinSourceDatum
    (G :
      ConcreteBorromeanPreRealizationSourceCoreGeometry
        K sigma n sourceBound)
    {k : Nat} (certificate : SU7CurrentShellSourceCertificate G k) :
    SU7PreRealizationThinSourceDatum n sourceBound (k + 2) where
  sourceCell := G.branchingCellOf certificate.state
  left_code_bounded := certificate.left_code_bounded
  right_code_bounded := certificate.right_code_bounded
  componentCochain := G.componentCochainOf certificate.state
  left_component_residual_zero :=
    certificate.left_component_residual_zero
  right_component_residual_zero :=
    certificate.right_component_residual_zero
  affine_energy := certificate.source_energy_successor

@[simp] theorem SU7CurrentShellSourceCertificate.toThinSourceDatum_energy
    (G :
      ConcreteBorromeanPreRealizationSourceCoreGeometry
        K sigma n sourceBound)
    {k : Nat} (certificate : SU7CurrentShellSourceCertificate G k) :
    preRealizationRawEnergy
        (certificate.toThinSourceDatum G).sourceCell = k + 2 :=
  (certificate.toThinSourceDatum G).affine_energy

/-! ## Concrete pointwise left-anchor source grammar -/

/-- Raw source cell for one lower-half shell.

The left code remains `5`, while the right code varies with the current key.
At `n = 10, k = 6` this specializes to the historical `(5, 7)` source cell;
for other keys it is *not* the fixed five-seven label. -/
def canonicalLeftAnchorCurrentShellCell (n k : Nat) :
    PreRealizationSU7BranchingCell n where
  branch := .e
  incidence := .colorWeak
  leftWeightCode := 5
  rightWeightCode := 2 * n - (k + 7)

@[simp] theorem canonicalLeftAnchorCurrentShellCell_left
    (n k : Nat) :
    (canonicalLeftAnchorCurrentShellCell n k).leftWeightCode = 5 := by
  rfl

@[simp] theorem canonicalLeftAnchorCurrentShellCell_right
    (n k : Nat) :
    (canonicalLeftAnchorCurrentShellCell n k).rightWeightCode =
      2 * n - (k + 7) := by
  rfl

/-- In the lower-half source room, the pointwise cell has signed residual
`-(k + 2)`. -/
theorem canonicalLeftAnchorCurrentShellCell_rawResidual
    {n k : Nat} (hroom : k + 7 <= 2 * n) :
    preRealizationRawResidual
        (canonicalLeftAnchorCurrentShellCell n k) =
      -((k + 2 : Nat) : Int) := by
  unfold preRealizationRawResidual canonicalPreP950RawResidual
    canonicalLeftAnchorCurrentShellCell
  have hsum : 5 + (2 * n - (k + 7)) = 2 * n - (k + 2) := by
    omega
  rw [hsum]
  push_cast
  omega

/-- Consequently, its raw source energy is exactly `k + 2`. -/
theorem canonicalLeftAnchorCurrentShellCell_rawEnergy
    {n k : Nat} (hroom : k + 7 <= 2 * n) :
    preRealizationRawEnergy
        (canonicalLeftAnchorCurrentShellCell n k) = k + 2 := by
  unfold preRealizationRawEnergy canonicalPreP950RawEnergy
  have hresidual :
      canonicalPreP950RawResidual
          (canonicalLeftAnchorCurrentShellCell n k) =
        -((k + 2 : Nat) : Int) := by
    simpa [preRealizationRawResidual] using
      canonicalLeftAnchorCurrentShellCell_rawResidual hroom
  rw [hresidual]
  simp only [Int.natAbs_neg, Int.natAbs_natCast]

/-- Constant-state source/phase geometry for one current shell.

The source state and zero cochain make reachability and component phase
closure explicit without introducing a global shell family. -/
def concreteLeftAnchorCurrentShellSourceCoreGeometry
    (sigma_pos : 0 < sigma) (sigma_lt_one : sigma < 1)
    (n sourceBound k : Nat) :
    ConcreteBorromeanPreRealizationSourceCoreGeometry
      K sigma n sourceBound where
  sigma_pos := sigma_pos
  sigma_lt_one := sigma_lt_one
  SourceState := PUnit
  initialState := PUnit.unit
  nextState := id
  source_path_faithful := by
    intro x y h
    exact h
  branchingCellOf := fun _ => canonicalLeftAnchorCurrentShellCell n k
  branch_preserved := by
    intro _state
    rfl
  incidence_preserved := by
    intro _state
    rfl
  componentCochainOf := fun _state _i _j => 0

/-- The concrete pointwise grammar produces a genuine pre-realization current
shell certificate.

The only arithmetic hypotheses are lower-half room and raw-code bounds.  No
atomicity or endpoint-realization premise occurs. -/
def concreteLeftAnchorCurrentShellSourceCertificate
    (sigma_pos : 0 < sigma) (sigma_lt_one : sigma < 1)
    {n sourceBound k : Nat}
    (hroom : k + 7 <= 2 * n)
    (hleftBound : 5 <= sourceBound)
    (hrightBound : 2 * n - (k + 7) <= sourceBound) :
    SU7CurrentShellSourceCertificate
      (concreteLeftAnchorCurrentShellSourceCoreGeometry
        sigma_pos sigma_lt_one n sourceBound k)
      k where
  state := PUnit.unit
  reachable := Relation.ReflTransGen.refl
  left_code_bounded := by
    simpa [concreteLeftAnchorCurrentShellSourceCoreGeometry] using hleftBound
  right_code_bounded := by
    simpa [concreteLeftAnchorCurrentShellSourceCoreGeometry] using hrightBound
  left_component_residual_zero := by
    rfl
  right_component_residual_zero := by
    rfl
  source_energy_successor := by
    simpa [concreteLeftAnchorCurrentShellSourceCoreGeometry] using
      canonicalLeftAnchorCurrentShellCell_rawEnergy hroom

/-- The historical `n = 10, k = 6` source cell is exactly `(5, 7)`.

This theorem keeps that route pointwise; it does not generalize the five-seven
label to every key. -/
theorem canonicalLeftAnchorCurrentShellCell_n10_k6_codes :
    let cell := canonicalLeftAnchorCurrentShellCell 10 6
    cell.leftWeightCode = 5 /\ cell.rightWeightCode = 7 := by
  decide

end ConcreteBorromeanPreRealizationSourceCoreGeometry

end BorromeanPreRealization
end RepresentationArithmeticAtomProjectionDefect
