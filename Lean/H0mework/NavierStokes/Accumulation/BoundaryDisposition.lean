import H0mework.NavierStokes.Restart.NativeAccumulationVorticityCourt
import H0mework.Foundation.Inquiry.RevisionRecovery
import H0mework.Foundation.Runtime.EffectDynamics
import H0mework.Foundation.Runtime.EffectReactivation
import H0mework.Foundation.Inquiry.Engine
import H0mework.NavierStokes.PairRestart.SourcePairOccurrence
import H0mework.NavierStokes.Galerkin.KineticEnergyLedger
import H0mework.NavierStokes.Fourier.ShellViscousParseval

/-!
# Same-source native-accumulation boundary disposition

The authoritative native temporal root keeps its original physical compiler.
A bounded elapsed-time history compiles the exact cofinal obstruction; the
stored conditional strong-face law is only its predecessor-row readout.  The
obstruction emits the U7 theory-audit demand that generates the minimal
coface, typed revision, first native write, and recovery answer-and-next.

-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationBoundaryDisposition

open Set Filter Matrix
open ResponsibilityLifecycle
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.ObstructionGeneratedMinimalCoface
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.TypedSemanticWorldNetworkU8
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.TypedSemanticWorldNetworkU8Recovery
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeActualRoot
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFiniteTimeObstruction
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationVorticityCourt

noncomputable section

universe u

/-! The upgraded domain keeps the original supports, currents, events and
    live responsibility fibres.  Only obstruction/disposition visibility and
    the cofinal branch kind are versioned. -/

/-- Whole-state enstrophy power seen by one source-owned finite projection.
This is read from the actual receipt path, before any recursive disposition is
chosen. -/
def nativeTemporalProjectedWholeEnstrophyPower
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector)
    (actual : Real) : Real :=
  let state := (actualWholeProjectedTransversePath receipt actual).1
  2 * ∑ wave ∈ modes,
    complexCoordinateRealInner
      ((complexSharpSupportProjection modes state) wave)
      (wholeStateVorticityNonlinearCoefficientAt state wave)

/-- A positive native outflux is an actual full-receipt effect.  Its sign and
size are not supplied by the recursive-effect caller. -/
def NativeTemporalPositiveOutfluxAt
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector)
    (threshold : Real) : Prop :=
  ∀ actual ∈ Icc (0 : Real) requestedTime,
    threshold ≤
      -nativeTemporalProjectedWholeEnstrophyPower receipt modes actual

/-- The cofinal obstruction is an actual bounded-boundary occurrence, not the
conditional strong-face law stored in the predecessor row.  Its constructor
and local compiler stay private; the public engine exposes only the sealed
outcome generated at the fixed cofinal occurrence. -/
structure NativeTemporalActualCofinalBoundaryObstructionAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) : Type where
  private mk ::
  elapsedBounded : BddAbove (Set.range (elapsedTime initial))

/-- Internal compilation of the exact analytic boundary occurrence selected
by the fixed inquiry decision. -/
private def sourceGeneratedNativeTemporalActualCofinalBoundaryObstruction
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    NativeTemporalActualCofinalBoundaryObstructionAt initial where
  elapsedBounded := elapsedBounded

namespace NativeTemporalActualCofinalBoundaryObstructionAt

/-- The exact boundary occurrence is compiled from, rather than stored beside,
the source-owned boundedness occurrence. -/
def exactExit
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    (obstruction : NativeTemporalActualCofinalBoundaryObstructionAt initial) :
    NativeTemporalCofinalExactStrongFaceExitAt
      initial obstruction.elapsedBounded :=
  sourceGeneratedNativeTemporalCofinalExactStrongFaceExit
    initial obstruction.elapsedBounded

/-- The old strong-face law is only the predecessor-row readout of the actual
boundary occurrence. -/
def strongFaceFailure
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    (obstruction : NativeTemporalActualCofinalBoundaryObstructionAt initial) :
    NativeTemporalCofinalStrongFaceFailureAt initial :=
  obstruction.exactExit.strongFaceFailure

theorem strongFaceFailure_eq_sourceGenerated
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    (obstruction : NativeTemporalActualCofinalBoundaryObstructionAt initial) :
    obstruction.strongFaceFailure =
      nativeTemporalCofinalStrongFaceFailure initial := by
  exact
    obstruction.exactExit.strongFaceFailure_eq.trans
      (nativeTemporalCofinalWrite_targetFailure_eq initial)

end NativeTemporalActualCofinalBoundaryObstructionAt

/-- Exact finite-effect failure at the canonical target restart.  Projected
carrier output, the legacy single-row face, and the source-native outflux face
share the same authoritative finite boundary support and therefore enter the
same U7 calculus. -/
inductive NativeTemporalFiniteEffectRegenerationFailureAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) : Type where
  | projectedCarrierOutput
      (stage : Nat)
      (modes : Finset IntegerWavevector)
      (wave : IntegerWavevector)
      (waveNotMem : wave ∉ modes)
      (outputNonzero :
        wholeStateVorticityNonlinearCoefficientAt
          (complexSharpSupportProjection modes
            (run initial stage).initialState) wave ≠ 0)
  | positiveRow
      (stage : Nat)
      (output : IntegerWavevector)
      (coordinate : Fin 3)
      (threshold : Real)
      (sourcePositive : threshold <
        (wholeStateVorticityNonlinearCoefficientAt
          (run initial stage).initialState output coordinate).re)
      (targetNonpositive : ¬ threshold <
        (wholeStateVorticityNonlinearCoefficientAt
          (run initial (stage + 1)).initialState output coordinate).re)
  | positiveOutflux
      (stage : Nat)
      (modes : Finset IntegerWavevector)
      (threshold : Real)
      (sourcePositive : NativeTemporalPositiveOutfluxAt
        (run initial stage).contact.prefixReceipt modes threshold)
      (targetNonpositive : ¬ NativeTemporalPositiveOutfluxAt
        (run initial (stage + 1)).contact.prefixReceipt modes threshold)

def BoundaryObstructionAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    NativeTemporalSupport -> Type
  | .finite => NativeTemporalFiniteEffectRegenerationFailureAt initial
  | .cofinal => NativeTemporalActualCofinalBoundaryObstructionAt initial

inductive BoundaryDispositionAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    NativeTemporalSupport -> WorldDispositionKind -> Type
  | finiteTransfer : BoundaryDispositionAt initial .finite .transfer
  | transfer : BoundaryDispositionAt initial .cofinal .transfer
  | extension
      (obstruction : NativeTemporalActualCofinalBoundaryObstructionAt initial) :
      BoundaryDispositionAt initial .cofinal .lawSurfaceExtension

def boundaryNetwork
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    WorldRelationNetwork where
  Support := NativeTemporalSupport
  Anchor := NativeTemporalSupport
  Incidence := NativeTemporalSupport
  Lineage := GeneratedWholeRestartCurrent nu
  Responsibility := NativeTemporalResponsibility
  Claim := PUnit
  anchorAt := id
  incidenceAt := id
  lineageAt := fun _ => initial
  OpenAt := NativeTemporalOpenAt initial
  openClaimAt := fun _ => PUnit.unit
  HoldsAt := fun _ _ => PUnit
  ObstructionAt := BoundaryObstructionAt initial
  obstructionClaim := fun {_support} _ => PUnit.unit
  SemanticChangeAt := fun _ _ _ => PEmpty
  DispositionAt := BoundaryDispositionAt initial

abbrev BN {nu : Viscosity} (initial : GeneratedWholeRestartCurrent nu) :=
  boundaryNetwork initial

def boundaryVocabulary
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    ConstructiveRoot.Vocabulary where
  Current := NativeTemporalCurrent initial
  Anchor := NativeTemporalSupport
  Incidence := NativeTemporalSupport
  Lineage := GeneratedWholeRestartCurrent nu
  anchorAt := fun
    | .finite _ => .finite
    | .cofinal => .cofinal
    | .galerkin _ => .cofinal
  incidenceAt := fun
    | .finite _ => .finite
    | .cofinal => .cofinal
    | .galerkin _ => .cofinal
  lineageAt := fun _ => initial
  NativeWriteAt := nativeTemporalNativeWriteAt initial
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := nativeTemporalNativeTarget initial
  relationTarget := fun write => nomatch write
  continuedTarget := fun write => nomatch write
  redirectTarget := fun write => nomatch write
  cofinal :=
    { Event := GeneratedWholeRestartCanonicalWeakCofinalReceiptAt initial
      emit? := some
        (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial)
      pathAt := fun _event stage => .finite stage
      target := fun _event => .cofinal }

abbrev BV {nu : Viscosity} (initial : GeneratedWholeRestartCurrent nu) :=
  boundaryVocabulary initial

def boundaryEventAlgebra
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    SourceNativeEventAlgebra (BN initial) (BV initial) where
  EventAt := NativeTemporalRootEventAt initial
  compile := fun event =>
    match event with
    | .finite _ occurrence => .nativeWrite occurrence
    | .cofinal receipt => .nativeWrite receipt
    | .galerkin _ write => .nativeWrite write
  AffectedInventoryAt := fun {_current} {support} _ =>
    OpenResponsibilityAt (BN initial) support
  affectedInventoryPresentation := fun _ => ConstructivePresentation.refl _
  anchorKey := id
  incidenceKey := id
  lineageKey := id
  anchor_commutes := by intro current support event; cases event <;> rfl
  incidence_commutes := by intro current support event; cases event <;> rfl
  lineage_commutes := by intro current support event; cases event <;> rfl

def boundarySource
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    SourceNativeSource (BN initial) (BV initial) where
  initial := .finite 0
  law := boundaryEventAlgebra initial

def boundaryEmitted
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    (current : (BV initial).Current) ->
      (boundarySource initial).toRootSource.actual.OccurrenceAt current
  | .finite stage =>
      ⟨.finite, .finite stage
        (generatedWholeRestartNativeActualOccurrence initial stage)⟩
  | .cofinal =>
      ⟨.cofinal, .cofinal
        (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial)⟩
  | .galerkin radius =>
      ⟨.cofinal, .galerkin radius
        (sourceGeneratedNativeTemporalGalerkinWrite initial radius)⟩

def boundaryFiniteEntry
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    OpenResponsibilityAt (BN initial) .finite :=
  ⟨.finite, .finite⟩

/-- The finite NS row carries no structural progress credit.  This `Nat`
budget is the living-law no-refill clock, not a physical time or energy row. -/
@[simp] theorem boundaryFiniteEntry_progressBudget_eq_zero
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    (boundaryFiniteEntry initial).progressBudget = 0 := rfl

/-- All finite occurrences already share the same world standing.  Their
actual chronology and physical data live in the occurrence/current and effect
records; they are deliberately not smuggled into the `PUnit` world claim. -/
def boundaryFiniteEntry_sameStanding
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    RootStandingIdentityAt (BN initial)
      (boundaryFiniteEntry initial) (boundaryFiniteEntry initial) where
  anchor_eq := rfl
  incidence_eq := rfl
  lineage_eq := rfl
  responsibility_eq := rfl
  claim_eq := rfl

private theorem boundaryFiniteEntry_eq
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (entry : OpenResponsibilityAt (BN initial) .finite) :
    boundaryFiniteEntry initial = entry := by
  rcases entry with ⟨responsibility, openAt⟩
  cases openAt
  rfl

def boundaryCofinalEntry
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    OpenResponsibilityAt (BN initial) .cofinal :=
  ⟨.cofinal, .cofinal (nativeTemporalCofinalStrongFaceFailure initial)⟩

private theorem boundaryCofinalEntry_eq
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (entry : OpenResponsibilityAt (BN initial) .cofinal) :
    boundaryCofinalEntry initial = entry := by
  rcases entry with ⟨responsibility, openAt⟩
  cases openAt
  rfl

inductive BoundaryRowEventAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    {current : NativeTemporalCurrent initial} ->
      (occurrence : (boundarySource initial).toRootSource.actual.OccurrenceAt current) ->
      {targetSupport : NativeTemporalSupport} ->
      (sourceEntry : OpenResponsibilityAt (BN initial)
        ((boundarySource initial).toRootSource.account.supportOf occurrence)) ->
      (targetEntry : OpenResponsibilityAt (BN initial) targetSupport) -> Type
  | finite
      (stage : Nat)
      (occurrence : GeneratedWholeRestartNativeActualOccurrenceAt initial stage) :
      BoundaryRowEventAt initial
        (⟨.finite, .finite stage occurrence⟩ :
          (boundarySource initial).toRootSource.actual.OccurrenceAt (.finite stage))
        (boundaryFiniteEntry initial) (boundaryFiniteEntry initial)
  | cofinal (receipt : GeneratedWholeRestartCanonicalWeakCofinalReceiptAt initial) :
      BoundaryRowEventAt initial
        (⟨.cofinal, .cofinal receipt⟩ :
          (boundarySource initial).toRootSource.actual.OccurrenceAt .cofinal)
        (boundaryCofinalEntry initial) (boundaryCofinalEntry initial)
  | galerkin (radius : Nat) (write : NativeTemporalGalerkinWriteAt initial radius) :
      BoundaryRowEventAt initial
        (⟨.cofinal, .galerkin radius write⟩ :
          (boundarySource initial).toRootSource.actual.OccurrenceAt (.galerkin radius))
        (boundaryCofinalEntry initial) (boundaryCofinalEntry initial)

def boundaryWriteRowSource
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    LedgerWriteRowSourceAt (boundarySource initial) (by
      intro _ occurrence targetSupport _ _
      exact NativeTemporalExactTransitionAt occurrence.1 targetSupport) :=
  { IncidenceOccurrenceAt := BoundaryRowEventAt initial
    compileEvolution := fun event => by
      cases event with
      | finite =>
          exact .transferred BoundaryDispositionAt.finiteTransfer
            rfl rfl (Nat.le_refl _)
      | cofinal =>
          exact .carried rfl HEq.rfl
      | galerkin =>
          exact .transferred BoundaryDispositionAt.transfer
            rfl rfl (Nat.le_refl _)
    compileExact := fun event => by
      cases event <;> exact ⟨rfl⟩ }

def boundaryFinitePatch
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (stage : Nat)
    (occurrence : GeneratedWholeRestartNativeActualOccurrenceAt initial stage) :
    FiniteGeneratedLedgerWritePatchAt
      (boundaryWriteRowSource initial)
      (⟨.finite, .finite stage occurrence⟩ :
        (boundarySource initial).toRootSource.actual.OccurrenceAt (.finite stage))
      ⟨.finite⟩ :=
  .identityRemainder
    { size := 1
      sourceEntryAt := fun _ => boundaryFiniteEntry initial
      targetEntryAt := fun _ => boundaryFiniteEntry initial
      rowAt := fun _ =>
        (boundaryWriteRowSource initial).generate (.finite stage occurrence) }
    { destinationIndex := fun entry =>
        some ⟨⟨0, Nat.zero_lt_succ 0⟩, boundaryFiniteEntry_eq initial entry⟩
      originIndex := fun entry =>
        some ⟨⟨0, Nat.zero_lt_succ 0⟩, boundaryFiniteEntry_eq initial entry⟩ }

def boundaryCofinalPatch
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (receipt : GeneratedWholeRestartCanonicalWeakCofinalReceiptAt initial) :
    FiniteGeneratedLedgerWritePatchAt
      (boundaryWriteRowSource initial)
      (⟨.cofinal, .cofinal receipt⟩ :
        (boundarySource initial).toRootSource.actual.OccurrenceAt .cofinal)
      ⟨.cofinal⟩ :=
  .identityRemainder
    { size := 1
      sourceEntryAt := fun _ => boundaryCofinalEntry initial
      targetEntryAt := fun _ => boundaryCofinalEntry initial
      rowAt := fun _ => (boundaryWriteRowSource initial).generate (.cofinal receipt) }
    { destinationIndex := fun entry =>
        some ⟨⟨0, Nat.zero_lt_succ 0⟩, boundaryCofinalEntry_eq initial entry⟩
      originIndex := fun entry =>
        some ⟨⟨0, Nat.zero_lt_succ 0⟩, boundaryCofinalEntry_eq initial entry⟩ }

def boundaryGalerkinPatch
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (radius : Nat) (write : NativeTemporalGalerkinWriteAt initial radius) :
    FiniteGeneratedLedgerWritePatchAt
      (boundaryWriteRowSource initial)
      (⟨.cofinal, .galerkin radius write⟩ :
        (boundarySource initial).toRootSource.actual.OccurrenceAt (.galerkin radius))
      ⟨.cofinal⟩ :=
  .identityRemainder
    { size := 1
      sourceEntryAt := fun _ => boundaryCofinalEntry initial
      targetEntryAt := fun _ => boundaryCofinalEntry initial
      rowAt := fun _ => (boundaryWriteRowSource initial).generate (.galerkin radius write) }
    { destinationIndex := fun entry =>
        some ⟨⟨0, Nat.zero_lt_succ 0⟩, boundaryCofinalEntry_eq initial entry⟩
      originIndex := fun entry =>
        some ⟨⟨0, Nat.zero_lt_succ 0⟩, boundaryCofinalEntry_eq initial entry⟩ }

def boundaryTerminalRowSource
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    LedgerTerminalRowSourceAt (boundarySource initial) :=
  LedgerTerminalRowSourceAt.empty _

def boundaryGeneratedLedgerEvolution
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {current : NativeTemporalCurrent initial}
    (occurrence : (boundarySource initial).toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerEvolutionAt (boundarySource initial) occurrence := by
  rcases occurrence with ⟨support, event⟩
  change NativeTemporalRootEventAt initial current support at event
  cases event with
  | finite stage finiteOccurrence =>
      exact .nativeWrite finiteOccurrence rfl
        (boundaryEmitted initial (.finite (stage + 1)))
        (boundaryFinitePatch initial stage finiteOccurrence).toLedgerWriteEvolution
  | cofinal receipt =>
      exact .nativeWrite receipt rfl
        (boundaryEmitted initial (.galerkin 0))
        (boundaryCofinalPatch initial receipt).toLedgerWriteEvolution
  | galerkin radius write =>
      exact .nativeWrite write rfl
        (boundaryEmitted initial (.galerkin (radius + 1)))
        (boundaryGalerkinPatch initial radius write).toLedgerWriteEvolution

def boundaryLedgerCompiler
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    SourceNativeLedgerCompiler (boundarySource initial) where
  IncidenceTransitionAt := fun _ sourceIncidence targetIncidence =>
    NativeTemporalIncidenceTransitionAt sourceIncidence targetIncidence
  ExactTransitionAt := by
    intro _ occurrence targetSupport _ _
    exact NativeTemporalExactTransitionAt occurrence.1 targetSupport
  exact_incidence := by
    intro current occurrence targetSupport sourceEntry targetEntry exact
    exact ⟨exact.support_eq⟩
  exact_lineage := fun _ => rfl
  writeRowSource := boundaryWriteRowSource initial
  terminalRowSource := boundaryTerminalRowSource initial
  compile := boundaryGeneratedLedgerEvolution initial
  compilePatch := by
    intro current occurrence
    rcases occurrence with ⟨support, event⟩
    change NativeTemporalRootEventAt initial current support at event
    cases event with
    | finite stage finiteOccurrence =>
        exact ⟨boundaryFinitePatch initial stage finiteOccurrence, rfl⟩
    | cofinal receipt => exact ⟨boundaryCofinalPatch initial receipt, rfl⟩
    | galerkin radius write =>
        exact ⟨boundaryGalerkinPatch initial radius write, rfl⟩

def boundaryLedgerSource
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    SourceNativeLedgerSource (BN initial) (BV initial) where
  source := boundarySource initial
  ledgerCompiler := boundaryLedgerCompiler initial

def boundaryRoot
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    SourceNativeLedgerRootClosure (BN initial) (BV initial) where
  source := boundaryLedgerSource initial
  emitted := boundaryEmitted initial
  compiler_commutes := by intro current; cases current <;> rfl

private theorem boundaryFailure_subsingleton
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    Subsingleton (NativeTemporalCofinalStrongFaceFailureAt initial) := by
  constructor
  rintro ⟨leftFailure, leftTail, leftPDE, leftPair⟩
    ⟨rightFailure, rightTail, rightPDE, rightPair⟩
  congr

private theorem boundaryActualCofinalObstruction_subsingleton
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    Subsingleton
      (NativeTemporalActualCofinalBoundaryObstructionAt initial) := by
  constructor
  rintro ⟨leftBounded⟩ ⟨rightBounded⟩
  congr

private theorem boundaryOpenAt_subsingleton
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (support : NativeTemporalSupport)
    (responsibility : NativeTemporalResponsibility) :
    Subsingleton ((BN initial).OpenAt support responsibility) := by
  constructor
  intro left right
  cases left with
  | finite => cases right; rfl
  | cofinal leftFailure =>
      cases right with
      | cofinal rightFailure =>
          congr
          exact (boundaryFailure_subsingleton initial).elim
            leftFailure rightFailure

theorem boundaryOpenResponsibility_subsingleton
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (support : NativeTemporalSupport) :
    Subsingleton (OpenResponsibilityAt (BN initial) support) := by
  constructor
  rintro ⟨left, leftOpen⟩ ⟨right, rightOpen⟩
  cases leftOpen with
  | finite => cases rightOpen; rfl
  | cofinal leftFailure =>
      cases rightOpen with
      | cofinal rightFailure =>
          congr
          exact (boundaryFailure_subsingleton initial).elim
            leftFailure rightFailure

private def boundaryRestructuringLaw
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    SourceNativeLedgerRestructuringLaw (boundarySource initial) :=
  identityOnlyWorldLedgerRestructuringLaw
    (boundarySource initial) .finite (boundaryOpenAt_subsingleton initial)

private def boundaryRestructuringCertification
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {current : NativeTemporalCurrent initial}
    (occurrence : (boundarySource initial).toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerRestructuringCertificationAt
      (boundaryRestructuringLaw initial)
      ((boundaryLedgerCompiler initial).compile occurrence) := by
  rcases occurrence with ⟨support, event⟩
  change NativeTemporalRootEventAt initial current support at event
  cases event <;>
    exact ExactLedgerRestructuringCertificationAt.ofInjective
      (fun left right _ =>
        (boundaryOpenResponsibility_subsingleton initial _).elim left right)
      (fun left right _ =>
        (boundaryOpenResponsibility_subsingleton initial _).elim left right)

private def boundaryRestructuringCompiler
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    SourceNativeRestructuringLedgerCompiler (boundarySource initial) where
  ledgerCompiler := boundaryLedgerCompiler initial
  restructuringLaw := boundaryRestructuringLaw initial
  certifyRestructuring := boundaryRestructuringCertification initial

def boundaryRestructuringSource
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    SourceNativeRestructuringLedgerSource (BN initial) (BV initial) where
  source := boundarySource initial
  compiler := boundaryRestructuringCompiler initial

/-- The boundary presentation compiles the same physical cofinal write as the
original temporal root.  It cannot preload a structural U8 branch; only the
later, obstruction-indexed U7 event may issue a theory-audit demand. -/
theorem boundaryCofinal_compiles_nativeWrite
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    (boundaryLedgerCompiler initial).compile
        (boundaryEmitted initial .cofinal) =
      .nativeWrite
        (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial)
        rfl
        (boundaryEmitted initial (.galerkin 0))
        (boundaryCofinalPatch initial
          (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial)
          ).toLedgerWriteEvolution :=
  rfl

def boundaryProductiveHistory
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    ProductiveFiniteRootHistoryAt (boundaryRoot initial) where
  currentAt := fun stage => .finite stage
  initial_eq := rfl
  next_eq := fun _ => rfl

def boundaryCofinalVisit
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    SourceNativeCofinalVisitAt (boundaryRoot initial) :=
  (boundaryProductiveHistory initial).generatedCofinalVisit?
      (fun _emitted_eq _index => rfl) |>.get (by rfl)

/-- Boundary-ledger coordinate used by the faithful two-sided restriction to
the authoritative physical root. -/
def boundaryCofinalGeneratedEvolution
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    SourceNativeTemporalVisitGeneratedEvolutionAt
      (boundaryRoot initial) (.cofinal (boundaryCofinalVisit initial)) :=
  (boundaryRoot initial).generatedAtTemporalVisit
    (.cofinal (boundaryCofinalVisit initial))

def restrictOccurrence
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {current : NativeTemporalCurrent initial} :
    (boundarySource initial).toRootSource.actual.OccurrenceAt current ->
      (nativeTemporalSource initial).toRootSource.actual.OccurrenceAt current
  | ⟨support, event⟩ => ⟨support, event⟩

/-- The original native ledger has only the exact carried evolution between
its unique live rows.  Boundary-only transfer receipts therefore forget to a
unique old-row evolution without selecting a new row. -/
private theorem nativeLedgerEntryEvolution_subsingleton
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {sourceSupport targetSupport : NativeTemporalSupport}
    (sourceEntry : OpenResponsibilityAt (N initial) sourceSupport)
    (targetEntry : OpenResponsibilityAt (N initial) targetSupport) :
    Subsingleton
      (LedgerEntryEvolutionAt (N initial) sourceEntry targetEntry) := by
  constructor
  intro left right
  cases left with
  | carried leftSupportEq leftEntryEq =>
      cases right with
      | carried rightSupportEq rightEntryEq => congr
      | maintained _ _ _ _ _ strictDebit =>
          change 0 < 0 at strictDebit
          exact (Nat.lt_irrefl 0 strictDebit).elim
      | transferred receipt => exact nomatch receipt
  | maintained _ _ _ _ _ strictDebit =>
      change 0 < 0 at strictDebit
      exact (Nat.lt_irrefl 0 strictDebit).elim
  | transferred receipt => exact nomatch receipt

private theorem nativeLedgerWriteEvolution_subsingleton
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (source target : CompleteLiveLedgerAt (N initial)) :
    Subsingleton (LedgerWriteEvolutionAt (N initial) source target) := by
  constructor
  rintro ⟨leftDestination, leftOrigin⟩
    ⟨rightDestination, rightOrigin⟩
  congr
  · funext sourceEntry
    letI : Subsingleton target.Entry :=
      boundaryOpenResponsibility_subsingleton initial target.support
    rcases leftDestination sourceEntry with ⟨leftTarget, leftEvolution⟩
    rcases rightDestination sourceEntry with ⟨rightTarget, rightEvolution⟩
    have target_eq : leftTarget = rightTarget := Subsingleton.elim _ _
    subst rightTarget
    congr
    exact (nativeLedgerEntryEvolution_subsingleton initial _ _).elim _ _
  · funext targetEntry
    letI : Subsingleton source.Entry :=
      boundaryOpenResponsibility_subsingleton initial source.support
    rcases leftOrigin targetEntry with ⟨leftSource, leftEvolution⟩
    rcases rightOrigin targetEntry with ⟨rightSource, rightEvolution⟩
    have source_eq : leftSource = rightSource := Subsingleton.elim _ _
    subst rightSource
    congr
    exact (nativeLedgerEntryEvolution_subsingleton initial _ _).elim _ _

/-- Forget only the boundary transfer tag while retaining the exact source and
target entries selected by the boundary whole-ledger patch. -/
private def restrictBoundaryLedgerWriteEvolution
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {source target : CompleteLiveLedgerAt (BN initial)}
    (support_eq : source.support = target.support)
    (evolution : LedgerWriteEvolutionAt (BN initial) source target) :
    LedgerWriteEvolutionAt (N initial)
      ({ support := source.support } : CompleteLiveLedgerAt (N initial))
      ({ support := target.support } : CompleteLiveLedgerAt (N initial)) := by
  rcases source with ⟨sourceSupport⟩
  rcases target with ⟨targetSupport⟩
  dsimp only at support_eq ⊢
  subst targetSupport
  exact
    { destination := fun sourceEntry =>
        let targetEntry := (evolution.destination sourceEntry).1
        ⟨targetEntry,
          .carried rfl
            (heq_of_eq
              ((boundaryOpenResponsibility_subsingleton initial sourceSupport
                ).elim sourceEntry targetEntry))⟩
      origin := fun targetEntry =>
        let sourceEntry := (evolution.origin targetEntry).1
        ⟨sourceEntry,
          .carried rfl
            (heq_of_eq
              ((boundaryOpenResponsibility_subsingleton initial sourceSupport
                ).elim sourceEntry targetEntry))⟩ }

private def restrictBoundaryFiniteCompilerEvolution
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (stage : Nat)
    (finiteOccurrence : GeneratedWholeRestartNativeActualOccurrenceAt initial stage) :
    SourceNativeLedgerEvolutionAt (nativeTemporalSource initial)
      (restrictOccurrence initial
        (⟨.finite, .finite stage finiteOccurrence⟩ :
          (boundarySource initial).toRootSource.actual.OccurrenceAt (.finite stage))) :=
  .nativeWrite finiteOccurrence rfl
    (restrictOccurrence initial (boundaryEmitted initial (.finite (stage + 1))))
    (restrictBoundaryLedgerWriteEvolution initial rfl
      (boundaryFinitePatch initial stage finiteOccurrence).toLedgerWriteEvolution)

private def restrictBoundaryCofinalCompilerEvolution
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (receipt : GeneratedWholeRestartCanonicalWeakCofinalReceiptAt initial) :
    SourceNativeLedgerEvolutionAt (nativeTemporalSource initial)
      (restrictOccurrence initial
        (⟨.cofinal, .cofinal receipt⟩ :
          (boundarySource initial).toRootSource.actual.OccurrenceAt .cofinal)) :=
  .nativeWrite receipt rfl
    (restrictOccurrence initial (boundaryEmitted initial (.galerkin 0)))
    (restrictBoundaryLedgerWriteEvolution initial rfl
      (boundaryCofinalPatch initial receipt).toLedgerWriteEvolution)

private def restrictBoundaryGalerkinCompilerEvolution
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (radius : Nat)
    (write : NativeTemporalGalerkinWriteAt initial radius) :
    SourceNativeLedgerEvolutionAt (nativeTemporalSource initial)
      (restrictOccurrence initial
        (⟨.cofinal, .galerkin radius write⟩ :
          (boundarySource initial).toRootSource.actual.OccurrenceAt (.galerkin radius))) :=
  .nativeWrite write rfl
    (restrictOccurrence initial (boundaryEmitted initial (.galerkin (radius + 1))))
    (restrictBoundaryLedgerWriteEvolution initial rfl
      (boundaryGalerkinPatch initial radius write).toLedgerWriteEvolution)

/-- Faithful whole-carrier restriction of the upgraded compiler.  Each branch
is built from the exact boundary compiler patch; unlike the previous readout,
this function never calls the original compiler.  At the cofinal occurrence
it preserves the same native write, target occurrence, and both complete-ledger
maps while forgetting only the boundary presentation. -/
def restrictEvolution
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {current : NativeTemporalCurrent initial}
    (occurrence : (boundarySource initial).toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerEvolutionAt (nativeTemporalSource initial)
      (restrictOccurrence initial occurrence) := by
  rcases occurrence with ⟨support, event⟩
  change NativeTemporalRootEventAt initial current support at event
  cases event with
  | finite stage finiteOccurrence =>
      exact restrictBoundaryFiniteCompilerEvolution initial stage finiteOccurrence
  | cofinal receipt =>
      exact restrictBoundaryCofinalCompilerEvolution initial receipt
  | galerkin radius write =>
      exact restrictBoundaryGalerkinCompilerEvolution initial radius write

private theorem boundaryFiniteCompiler_commutes
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (stage : Nat)
    (finiteOccurrence : GeneratedWholeRestartNativeActualOccurrenceAt initial stage) :
    restrictBoundaryFiniteCompilerEvolution initial stage finiteOccurrence =
      (nativeTemporalLedgerCompiler initial).compile
        (restrictOccurrence initial
          (⟨.finite, .finite stage finiteOccurrence⟩ :
            (boundarySource initial).toRootSource.actual.OccurrenceAt (.finite stage))) := by
  have nativeGenerated_eq :
      (nativeTemporalLedgerCompiler initial).compile
          (restrictOccurrence initial
            (⟨.finite, .finite stage finiteOccurrence⟩ :
              (boundarySource initial).toRootSource.actual.OccurrenceAt (.finite stage))) =
        .nativeWrite finiteOccurrence rfl
          (nativeTemporalEmitted initial (.finite (stage + 1)))
          (nativeTemporalFiniteWritePatch initial stage finiteOccurrence
            ).toLedgerWriteEvolution := by
    rfl
  rw [nativeGenerated_eq]
  simp only [restrictBoundaryFiniteCompilerEvolution, restrictOccurrence,
    boundaryEmitted, nativeTemporalEmitted]
  congr
  exact (nativeLedgerWriteEvolution_subsingleton initial _ _).elim _ _

private theorem boundaryCofinalCompiler_commutes
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (receipt : GeneratedWholeRestartCanonicalWeakCofinalReceiptAt initial) :
    restrictBoundaryCofinalCompilerEvolution initial receipt =
      (nativeTemporalLedgerCompiler initial).compile
        (restrictOccurrence initial
          (⟨.cofinal, .cofinal receipt⟩ :
            (boundarySource initial).toRootSource.actual.OccurrenceAt .cofinal)) := by
  have nativeGenerated_eq :
      (nativeTemporalLedgerCompiler initial).compile
          (restrictOccurrence initial
            (⟨.cofinal, .cofinal receipt⟩ :
              (boundarySource initial).toRootSource.actual.OccurrenceAt .cofinal)) =
        .nativeWrite receipt rfl
          (nativeTemporalEmitted initial (.galerkin 0))
          (nativeTemporalCofinalWritePatch initial receipt).toLedgerWriteEvolution := by
    rfl
  rw [nativeGenerated_eq]
  simp only [restrictBoundaryCofinalCompilerEvolution, restrictOccurrence,
    boundaryEmitted, nativeTemporalEmitted]
  congr
  exact (nativeLedgerWriteEvolution_subsingleton initial _ _).elim _ _

private theorem boundaryGalerkinCompiler_commutes
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (radius : Nat)
    (write : NativeTemporalGalerkinWriteAt initial radius) :
    restrictBoundaryGalerkinCompilerEvolution initial radius write =
      (nativeTemporalLedgerCompiler initial).compile
        (restrictOccurrence initial
          (⟨.cofinal, .galerkin radius write⟩ :
            (boundarySource initial).toRootSource.actual.OccurrenceAt (.galerkin radius))) := by
  have nativeGenerated_eq :
      (nativeTemporalLedgerCompiler initial).compile
          (restrictOccurrence initial
            (⟨.cofinal, .galerkin radius write⟩ :
              (boundarySource initial).toRootSource.actual.OccurrenceAt (.galerkin radius))) =
        .nativeWrite write rfl
          (nativeTemporalEmitted initial (.galerkin (radius + 1)))
          (nativeTemporalGalerkinWritePatch initial radius write
            ).toLedgerWriteEvolution := by
    rfl
  rw [nativeGenerated_eq]
  simp only [restrictBoundaryGalerkinCompilerEvolution, restrictOccurrence,
    boundaryEmitted, nativeTemporalEmitted]
  congr
  exact (nativeLedgerWriteEvolution_subsingleton initial _ _).elim _ _

/-- The upgraded boundary compiler faithfully commutes with the original
native compiler on every exact occurrence.  This is a whole-carrier theorem:
the boundary patch's target occurrence, destination map and origin map are
transported before the boundary presentation is forgotten. -/
private theorem restrictEvolution_commutes
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {current : NativeTemporalCurrent initial}
    (occurrence :
      (boundarySource initial).toRootSource.actual.OccurrenceAt current) :
    restrictEvolution initial occurrence =
      (nativeTemporalLedgerCompiler initial).compile
        (restrictOccurrence initial occurrence) := by
  rcases occurrence with ⟨support, event⟩
  change NativeTemporalRootEventAt initial current support at event
  cases event with
  | finite stage finiteOccurrence =>
      exact boundaryFiniteCompiler_commutes initial stage finiteOccurrence
  | cofinal receipt =>
      exact boundaryCofinalCompiler_commutes initial receipt
  | galerkin radius write =>
      exact boundaryGalerkinCompiler_commutes initial radius write

/-- Transport an explicitly supplied boundary compiler image.  The equality
index prevents a caller from presenting a sibling evolution; after that exact
image is identified, `restrictEvolution` transports its occurrence-local
boundary patch rather than recomputing the original compiler. -/
def boundaryCofaceTransportEvolution
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {current : NativeTemporalCurrent initial}
    (occurrence :
      (boundarySource initial).toRootSource.actual.OccurrenceAt current)
    (generated :
      SourceNativeLedgerEvolutionAt (boundarySource initial) occurrence)
    (generated_eq : generated =
      (boundaryLedgerCompiler initial).compile occurrence) :
    SourceNativeLedgerEvolutionAt (nativeTemporalSource initial)
      (restrictOccurrence initial occurrence) := by
  cases generated_eq
  exact restrictEvolution initial occurrence

/-- Exact compiler-image commuting square for the faithful boundary coface
restriction.  The left side consumes the actual upgraded compiler image; the
right side is the original compiler at the same restricted occurrence. -/
theorem boundaryCofaceCompiler_commutes
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {current : NativeTemporalCurrent initial}
    (occurrence :
      (boundarySource initial).toRootSource.actual.OccurrenceAt current) :
    boundaryCofaceTransportEvolution initial occurrence
        ((boundaryLedgerCompiler initial).compile occurrence) rfl =
      (nativeTemporalLedgerCompiler initial).compile
        (restrictOccurrence initial occurrence) := by
  simpa only [boundaryCofaceTransportEvolution] using
    restrictEvolution_commutes initial occurrence

@[simp] theorem restrictEmitted
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (current : NativeTemporalCurrent initial) :
    restrictOccurrence initial (boundaryEmitted initial current) =
      nativeTemporalEmitted initial current := by
  cases current <;> rfl

@[simp] theorem restrictGeneratedEvolution
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {current : NativeTemporalCurrent initial}
    (occurrence : (boundarySource initial).toRootSource.actual.OccurrenceAt current) :
    restrictEvolution initial occurrence =
      nativeTemporalGeneratedLedgerEvolution initial
        (restrictOccurrence initial occurrence) := by
  change restrictEvolution initial occurrence =
    (nativeTemporalLedgerCompiler initial).compile
      (restrictOccurrence initial occurrence)
  exact restrictEvolution_commutes initial occurrence

theorem boundaryCofinal_occurrence_restricts
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    restrictOccurrence initial (boundaryCofinalGeneratedEvolution initial).occurrence =
      (nativeTemporalCofinalVisitAuthority initial).toLedgerReadout.occurrence :=
  rfl

theorem boundaryCofinal_wholeWrite_restricts
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    restrictEvolution initial (boundaryCofinalGeneratedEvolution initial).occurrence =
      (nativeTemporalCofinalVisitAuthority initial).toLedgerReadout.wholeLedgerWriteBack :=
  by
    have commutes := restrictEvolution_commutes
      (initial := initial)
      (current := (.cofinal : NativeTemporalCurrent initial))
      (boundaryCofinalGeneratedEvolution initial).occurrence
    exact commutes.trans rfl

theorem boundaryCofinal_targetOccurrence_restricts
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    restrictOccurrence initial (boundaryEmitted initial (.galerkin 0)) =
      nativeTemporalEmitted initial (.galerkin 0) :=
  rfl

theorem boundaryCofinal_actualGalerkinWrite_exact
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    (BV initial).nativeTarget (current := .cofinal)
        (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial) =
        (.galerkin 0 : NativeTemporalCurrent initial) ∧
      (nativeTemporalNativeTarget initial (current := .cofinal)
        (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial)) =
        (.galerkin 0 : NativeTemporalCurrent initial) ∧
      sourceGeneratedNativeTemporalGalerkinWrite initial 0 =
        sourceGeneratedNativeTemporalGalerkinWrite initial 0 := by
  exact ⟨rfl, rfl, rfl⟩

structure BoundaryRootFaithfulRestrictionAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) : Type where
  occurrence :
    restrictOccurrence initial (boundaryCofinalGeneratedEvolution initial).occurrence =
      (nativeTemporalCofinalVisitAuthority initial).toLedgerReadout.occurrence
  compilerCommutes :
    ∀ {current : NativeTemporalCurrent initial}
      (occurrence :
        (boundarySource initial).toRootSource.actual.OccurrenceAt current),
      boundaryCofaceTransportEvolution initial occurrence
          ((boundaryLedgerCompiler initial).compile occurrence) rfl =
        (nativeTemporalLedgerCompiler initial).compile
          (restrictOccurrence initial occurrence)
  sourceCurrent :
    (boundaryCofinalVisit initial).current =
      (nativeTemporalCofinalVisit initial).current
  targetCurrent :
    (BV initial).nativeTarget (current := .cofinal)
        (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial) =
      nativeTemporalNativeTarget initial (current := .cofinal)
        (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial)
  targetOccurrence :
    restrictOccurrence initial (boundaryEmitted initial (.galerkin 0)) =
      nativeTemporalEmitted initial (.galerkin 0)
  wholeWriteBack :
    restrictEvolution initial (boundaryCofinalGeneratedEvolution initial).occurrence =
      (nativeTemporalCofinalVisitAuthority initial).toLedgerReadout.wholeLedgerWriteBack
  galerkinWrite :
    sourceGeneratedNativeTemporalGalerkinWrite initial 0 =
      sourceGeneratedNativeTemporalGalerkinWrite initial 0
  finiteConservative : ∀ stage,
    restrictEvolution initial (boundaryEmitted initial (.finite stage)) =
      (nativeTemporalRoot initial).generatedLedgerAt (.finite stage)
  galerkinConservative : ∀ radius,
    restrictEvolution initial (boundaryEmitted initial (.galerkin radius)) =
      (nativeTemporalRoot initial).generatedLedgerAt (.galerkin radius)

def boundaryRootFaithfulRestriction
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    BoundaryRootFaithfulRestrictionAt initial where
  occurrence := rfl
  compilerCommutes := boundaryCofaceCompiler_commutes initial
  sourceCurrent := rfl
  targetCurrent := rfl
  targetOccurrence := rfl
  wholeWriteBack := boundaryCofinal_wholeWrite_restricts initial
  galerkinWrite := rfl
  finiteConservative := fun stage => by
    change restrictEvolution initial (boundaryEmitted initial (.finite stage)) =
      (nativeTemporalLedgerCompiler initial).compile
        (nativeTemporalEmitted initial (.finite stage))
    exact restrictEvolution_commutes initial
      (boundaryEmitted initial (.finite stage))
  galerkinConservative := fun radius => by
    change restrictEvolution initial (boundaryEmitted initial (.galerkin radius)) =
      (nativeTemporalLedgerCompiler initial).compile
        (nativeTemporalEmitted initial (.galerkin radius))
    exact restrictEvolution_commutes initial
      (boundaryEmitted initial (.galerkin radius))

/-! The bounded analytic fibre supplies evidence at the already fixed cofinal
    occurrence.  It does not occur in the upgraded network, vocabulary,
    source or root definitions. -/

private def boundaryObstruction
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    (BN initial).ObstructionAt .cofinal :=
  sourceGeneratedNativeTemporalActualCofinalBoundaryObstruction
    initial elapsedBounded

structure BoundaryLandingRealizationAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (obstruction : (BN initial).ObstructionAt .cofinal) : Type where
  landing : Nonempty
    (NativeAccumulationWholeVorticityStrongLandingAt
      initial obstruction.elapsedBounded)

private theorem boundaryLandingRealization_isEmpty
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (obstruction : (BN initial).ObstructionAt .cofinal) :
    IsEmpty (BoundaryLandingRealizationAt initial obstruction) :=
  ⟨fun realization => by
    rcases realization.landing with ⟨landing⟩
    exact (nativeAccumulationWholeVorticityStrongLandingAt_isEmpty
      initial obstruction.elapsedBounded).false landing⟩

def boundaryOldLawInventory
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    LawInventory (BN initial) where
  Version := PUnit
  version := PUnit.unit
  Law := PUnit
  RealizationAt := fun {support} obstruction =>
    match support with
    | .finite => PUnit
    | .cofinal => BoundaryLandingRealizationAt initial obstruction
  RealizationWithoutAt := fun _ {_support} _ => PUnit

def boundaryOldExpressionAt
    {nu : Viscosity}
    (_initial : GeneratedWholeRestartCurrent nu) :
    NativeTemporalSupport -> Type
  | .finite => PUnit
  | .cofinal => PEmpty

def boundaryOldTheory
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    TheoryState (BN initial) where
  inventory := boundaryOldLawInventory initial
  ExpressionAt := boundaryOldExpressionAt initial
  denotes := fun _ => PUnit.unit
  TheoremAt := fun _ => PUnit
  theoremPresentation := fun _ => ConstructivePresentation.refl PUnit

def boundaryExpressibilityFailure
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (obstruction : (BN initial).ObstructionAt .cofinal) :
    ActualExpressibilityFailure (boundaryOldTheory initial)
      obstruction where
  notExpressible := ⟨by
    rintro ⟨expression, _⟩
    exact PEmpty.elim expression⟩
  noLawfulRealization := boundaryLandingRealization_isEmpty initial obstruction

private theorem boundaryFiniteExpressibilityFailure_isEmpty
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (obstruction : (BN initial).ObstructionAt .finite) :
    IsEmpty (ActualExpressibilityFailure (boundaryOldTheory initial)
      obstruction) :=
  ⟨fun failure => failure.notExpressible.false
    ⟨PUnit.unit, rfl⟩⟩

structure BoundaryU7DemandAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (obstruction : (BN initial).ObstructionAt .cofinal) : Type where
  private mk ::

def BoundaryU7DemandAt.generated
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {obstruction : (BN initial).ObstructionAt .cofinal} :
    BoundaryU7DemandAt initial obstruction :=
  ⟨⟩

def boundaryU7
    {nu : Viscosity}
  (initial : GeneratedWholeRestartCurrent nu) :
    U7ProducerCalculus (BN initial) where
  DemandAt := fun {support} obstruction =>
    match support with
    | .finite => NativeTemporalFiniteEffectRegenerationFailureAt initial
    | .cofinal => BoundaryU7DemandAt initial obstruction
  generateDemand := by
    intro support obstruction
    cases support with
    | finite => exact obstruction
    | cofinal => exact BoundaryU7DemandAt.generated

private def boundaryU7ActualSource
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    U7ActualSuccessorSource (BN initial) (boundaryU7 initial) where
  EventAt := SourceGeneratedU7DemandAt (boundaryU7 initial)
  emit := fun obstruction => .canonical obstruction
  demandGeneratedAt := fun event => event
  demandEntryAt := by
    intro support obstruction demand event
    cases support with
    | finite => exact ⟨.finite, .finite⟩
    | cofinal =>
        exact ⟨.cofinal,
          .cofinal (nativeTemporalCofinalStrongFaceFailure initial)⟩

def boundaryU7Calculus
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    U7ObstructionEvolutionCalculus (BN initial) (boundaryU7 initial) where
  source := boundaryU7ActualSource initial
  compile := by
    intro support obstruction demand event
    cases support with
    | finite =>
        cases event
        exact
          { disposition := .redirected
              ⟨BoundaryDispositionAt.finiteTransfer, rfl⟩
            demandEntryDisposition :=
              ⟨ConstructiveRoot.LedgerEntryEvolutionAt.transferred
                BoundaryDispositionAt.finiteTransfer rfl rfl
                (Nat.le_refl _), rfl⟩ }
    | cofinal =>
        cases event
        exact
          { disposition := .requiresTheoryAudit
              (BoundaryDispositionAt.extension obstruction)
            demandEntryDisposition := PUnit.unit }

/-- A finite local redirect is the exact disposition of the same root row;
it is not a claim that the whole world has terminated. -/
theorem boundaryFiniteU7RootDispositionCommutes
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (stage : Nat)
    (obstruction : (BN initial).ObstructionAt .finite) :
    U7DemandEntryRootDispositionCommutesAt (boundaryU7Calculus initial)
      ((boundaryU7Calculus initial).source.emit obstruction)
      (boundaryFiniteEntry initial)
      (((boundaryLedgerCompiler initial).compile
        (boundaryEmitted initial (.finite stage))).entryDisposition
          (boundaryFiniteEntry initial)) := by
  unfold U7DemandEntryRootDispositionCommutesAt
  constructor
  · rfl
  · change HEq (LedgerEntryDispositionAt.evolved _)
      (LedgerEntryDispositionAt.evolved _)
    let occurrence := generatedWholeRestartNativeActualOccurrence initial stage
    let selected :=
      ((boundaryFinitePatch initial stage occurrence).canonicalGeneratedSourceRow?
        (boundaryFiniteEntry initial)).get (by rfl)
    let u7Event := (boundaryU7Calculus initial).source.emit obstruction
    let u7Entry := U7ActualSuccessorSource.demandEntry u7Event
    have source_eq : boundaryFiniteEntry initial = u7Entry := rfl
    have target_eq : selected.targetEntry = u7Entry := by
      cases source_eq
      rfl
    have selected_heq : HEq selected.row.evolution
        ((boundaryU7Calculus initial).compile u7Event
          ).demandEntryDisposition.1 := by
      cases source_eq
      cases target_eq
      rfl
    have root_heq := selected.evolution_heq_fold.symm.trans selected_heq
    cases root_heq
    rfl

/-- The actual cofinal obstruction compiles to a theory-audit demand.  This is
the positive U8 gate; it contains no semantic change, revision candidate, or
revised equation. -/
def boundaryCofinalU7TheoryAudit
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (obstruction : (BN initial).ObstructionAt .cofinal) :
    SourceNativeU7TheoryAuditAt (boundaryU7Calculus initial)
      ((boundaryU7Calculus initial).source.emit obstruction) := by
  change PUnit
  exact PUnit.unit

/-- A finite redirect is a legitimate U7 continuation but cannot acquire U8
revision authority. -/
theorem boundaryFiniteU7TheoryAudit_isEmpty
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (obstruction : (BN initial).ObstructionAt .finite) :
    IsEmpty (SourceNativeU7TheoryAuditAt (boundaryU7Calculus initial)
      ((boundaryU7Calculus initial).source.emit obstruction)) := by
  constructor
  intro impossible
  change PEmpty at impossible
  exact PEmpty.elim impossible

/-! A positive actual finite nonlinear row recursively compiles either its
    canonical positive successor or the exact finite U7 obstruction. -/

structure BoundaryFiniteEffectOperational where
  stage : Nat
  elapsed : Real
  coefficientCeiling : Real
  contactTime : Real

def boundaryPositiveRowEffectAtLower
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (output : IntegerWavevector)
    {current : NativeTemporalCurrent initial}
    (occurrence :
      (boundarySource initial).toRootSource.actual.OccurrenceAt current) :
    ComplexCoordinateVector := by
  rcases occurrence with ⟨support, event⟩
  cases event with
  | finite stage _ =>
      exact wholeStateVorticityNonlinearCoefficientAt
        (run initial stage).initialState output
  | cofinal _ => exact 0
  | galerkin _ _ => exact 0

def boundaryPositiveRowOperationalAtLower
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {current : NativeTemporalCurrent initial}
    (occurrence :
      (boundarySource initial).toRootSource.actual.OccurrenceAt current) :
    BoundaryFiniteEffectOperational := by
  rcases occurrence with ⟨support, event⟩
  cases event with
  | finite stage _ =>
      exact
        { stage := stage
          elapsed := elapsedTime initial stage
          coefficientCeiling := restartCoefficientCeiling initial stage
          contactTime := (run initial stage).contact.time.1 }
  | cofinal _ =>
      exact { stage := 0, elapsed := 0, coefficientCeiling := 0, contactTime := 0 }
  | galerkin radius _ =>
      exact
        { stage := radius
          elapsed := 0
          coefficientCeiling := 0
          contactTime := 0 }

def boundaryPositiveRowEventVocabulary
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (output : IntegerWavevector) :
    SourceNativeEffectEventVocabulary (boundaryLedgerSource initial) where
  Effect := ComplexCoordinateVector
  Operational := BoundaryFiniteEffectOperational
  effectAt := boundaryPositiveRowEffectAtLower initial output
  operationalAt := boundaryPositiveRowOperationalAtLower initial

inductive BoundaryPositiveRowActiveAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (output : IntegerWavevector)
    (coordinate : Fin 3)
    (threshold : Real) :
    {current : NativeTemporalCurrent initial} →
      SourceNativeEffectOccurrenceAt
        (boundaryPositiveRowEventVocabulary initial output) current → Type
  | finite
      (stage : Nat)
      (occurrence : GeneratedWholeRestartNativeActualOccurrenceAt initial stage)
      (positive : threshold <
        (wholeStateVorticityNonlinearCoefficientAt
          (run initial stage).initialState output coordinate).re) :
      BoundaryPositiveRowActiveAt initial output coordinate threshold
        ((boundaryPositiveRowEventVocabulary initial output).emit
          ⟨.finite, .finite stage occurrence⟩)

instance boundaryPositiveRowActiveAt_subsingleton
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {output : IntegerWavevector}
    {coordinate : Fin 3}
    {threshold : Real}
    {current : NativeTemporalCurrent initial}
    {occurrence : SourceNativeEffectOccurrenceAt
      (boundaryPositiveRowEventVocabulary initial output) current} :
    Subsingleton
      (BoundaryPositiveRowActiveAt initial output coordinate threshold
        occurrence) where
  allEq := by
    intro left right
    cases left
    cases right
    rfl

def boundaryPositiveRowVocabulary
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (output : IntegerWavevector)
    (coordinate : Fin 3)
    (threshold : Real) :
    SourceNativeEffectDynamicalVocabulary
      (boundaryPositiveRowEventVocabulary initial output) where
  ActiveAt := BoundaryPositiveRowActiveAt initial output coordinate threshold
  InactiveAt := fun occurrence =>
    PLift (IsEmpty
      (BoundaryPositiveRowActiveAt initial output coordinate threshold occurrence))
  classify := by
    intro current occurrence
    classical
    by_cases active : Nonempty
        (BoundaryPositiveRowActiveAt initial output coordinate threshold occurrence)
    · exact .inl active.some
    · exact .inr ⟨⟨fun effect => active ⟨effect⟩⟩⟩
  effectEntryAt := by
    intro current occurrence active
    cases active
    exact boundaryFiniteEntry initial
  updateEffectAt := by
    intro current occurrence active sourceEffect
    cases active with
    | finite stage _ _ =>
        exact wholeStateVorticityNonlinearCoefficientAt
          (run initial (stage + 1)).initialState output
  updateOperationalAt := by
    intro current occurrence active sourceEffect sourceOperational
    cases active with
    | finite stage _ _ =>
        exact
          { stage := stage + 1
            elapsed := elapsedTime initial (stage + 1)
            coefficientCeiling := restartCoefficientCeiling initial (stage + 1)
            contactTime := (run initial (stage + 1)).contact.time.1 }

def boundaryFiniteGeneratedEffectEntry
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (stage : Nat)
    (occurrence : GeneratedWholeRestartNativeActualOccurrenceAt initial stage) :
    SourceNativeEffectGeneratedEntryAt
      (source := boundaryLedgerSource initial)
      (occurrence := ⟨.finite, .finite stage occurrence⟩)
      (boundaryFiniteEntry initial) :=
  ⟨(sourceNativeFiniteLedgerPatchGeneratedEntry?
      (boundarySource initial)
      (boundaryLedgerCompiler initial).ExactTransitionAt
      (boundaryWriteRowSource initial)
      (boundaryTerminalRowSource initial)
      ((boundaryLedgerCompiler initial).compile
        ⟨.finite, .finite stage occurrence⟩)
      ((boundaryLedgerCompiler initial).compilePatch
        ⟨.finite, .finite stage occurrence⟩)
      (boundaryFiniteEntry initial)).get (by rfl)⟩

def boundaryPositiveRowGenerate
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (output : IntegerWavevector)
    (coordinate : Fin 3)
    (threshold : Real)
    {current : NativeTemporalCurrent initial}
    (occurrence : SourceNativeEffectOccurrenceAt
      (boundaryPositiveRowEventVocabulary initial output) current)
    (active : BoundaryPositiveRowActiveAt initial output coordinate threshold
      occurrence) :
    SourceNativeEffectDynamicalDispositionAt
      (boundaryPositiveRowVocabulary initial output coordinate threshold)
      (boundaryU7Calculus initial) occurrence active
      ((boundaryLedgerCompiler initial).compile occurrence.lower) := by
  cases active with
  | finite stage finiteOccurrence sourcePositive =>
      let successor :=
        (@SourceNativeEffectGeneratedSuccessorAt.ofGenerated?
          (BN initial) (BV initial) (boundaryLedgerSource initial)
          (.finite stage) ⟨.finite, .finite stage finiteOccurrence⟩
          ((boundaryLedgerCompiler initial).compile
            ⟨.finite, .finite stage finiteOccurrence⟩)).get (by rfl)
      by_cases targetPositive : threshold <
          (wholeStateVorticityNonlinearCoefficientAt
            (run initial (stage + 1)).initialState output coordinate).re
      · let targetActive :
            BoundaryPositiveRowActiveAt initial output coordinate threshold
              ((boundaryPositiveRowEventVocabulary initial output).emit
                successor.targetOccurrence) :=
          .finite (stage + 1)
            (generatedWholeRestartNativeActualOccurrence initial (stage + 1))
            targetPositive
        exact .next
          (boundaryFiniteGeneratedEffectEntry initial stage finiteOccurrence)
          successor targetActive
          (by
            classical
            change
              (if witness : Nonempty
                    (BoundaryPositiveRowActiveAt initial output coordinate
                      threshold
                      ((boundaryPositiveRowEventVocabulary initial output).emit
                        successor.targetOccurrence)) then
                  Sum.inl witness.some
                else Sum.inr _) = Sum.inl targetActive
            rw [dif_pos ⟨targetActive⟩]
            congr
            exact (boundaryPositiveRowActiveAt_subsingleton
              (initial := initial)
              (output := output)
              (coordinate := coordinate)
              (threshold := threshold)
              (current := successor.targetCurrent)
              (occurrence :=
                (boundaryPositiveRowEventVocabulary initial output).emit
                  successor.targetOccurrence)).allEq _ _)
          ⟨by rfl⟩ rfl rfl
          (.operationalChanged (fun operationalEq => by
            have stageEq := congrArg BoundaryFiniteEffectOperational.stage
              operationalEq
            exact (Nat.ne_of_lt (Nat.lt_succ_self stage)) stageEq))
      · let row :=
          boundaryFiniteGeneratedEffectEntry initial stage finiteOccurrence
        refine .cut row successor
          (.positiveRow stage output coordinate threshold
            sourcePositive targetPositive) rfl ?_
        have commutes := row.down.commutes_with_world
        rcases commutes with ⟨_, evolution_heq⟩
        cases evolution_heq
        rfl

def boundaryPositiveRowClosureLaw
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (output : IntegerWavevector)
    (coordinate : Fin 3)
    (threshold : Real) :
    SourceNativeEffectDynamicalClosureLaw (boundaryLedgerSource initial) :=
  .create (boundaryU7 initial) (boundaryU7Calculus initial)
    (boundaryPositiveRowEventVocabulary initial output)
    (boundaryPositiveRowVocabulary initial output coordinate threshold)
    (boundaryPositiveRowGenerate initial output coordinate threshold)

@[simp] theorem boundaryPositiveRowClosureLaw_project
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (output : IntegerWavevector)
    (coordinate : Fin 3)
    (threshold : Real)
    {current : NativeTemporalCurrent initial}
    (occurrence :
      (boundarySource initial).toRootSource.actual.OccurrenceAt current)
    (active : BoundaryPositiveRowActiveAt initial output coordinate threshold
      ((boundaryPositiveRowEventVocabulary initial output).emit occurrence)) :
    (boundaryPositiveRowClosureLaw initial output coordinate threshold
      ).toProjectionLaw.project PUnit.unit occurrence active =
      boundaryPositiveRowGenerate initial output coordinate threshold
        ((boundaryPositiveRowEventVocabulary initial output).emit occurrence)
      active :=
  rfl

def BoundaryPositiveRowDispositionIsNext
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {output : IntegerWavevector}
    {coordinate : Fin 3}
    {threshold : Real}
    {current : NativeTemporalCurrent initial}
    {occurrence : (boundarySource initial).toRootSource.actual.OccurrenceAt current}
    {active : BoundaryPositiveRowActiveAt initial output coordinate threshold
      ((boundaryPositiveRowEventVocabulary initial output).emit occurrence)}
    (disposition : SourceNativeGeneratedEffectDynamicalClosureAt
      (boundaryPositiveRowClosureLaw initial output coordinate threshold)
      occurrence active) : Prop :=
  match disposition with
  | .next .. => True
  | .settled .. | .cut .. => False

def BoundaryPositiveRowDispositionIsCut
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {output : IntegerWavevector}
    {coordinate : Fin 3}
    {threshold : Real}
    {current : NativeTemporalCurrent initial}
    {occurrence : (boundarySource initial).toRootSource.actual.OccurrenceAt current}
    {active : BoundaryPositiveRowActiveAt initial output coordinate threshold
      ((boundaryPositiveRowEventVocabulary initial output).emit occurrence)}
    (disposition : SourceNativeGeneratedEffectDynamicalClosureAt
      (boundaryPositiveRowClosureLaw initial output coordinate threshold)
      occurrence active) : Prop :=
  match disposition with
  | .cut .. => True
  | .settled .. | .next .. => False

private theorem boundaryPositiveRowGenerate_finite_isNext
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (output : IntegerWavevector)
    (coordinate : Fin 3)
    (threshold : Real)
    (stage : Nat)
    (sourcePositive : threshold <
      (wholeStateVorticityNonlinearCoefficientAt
        (run initial stage).initialState output coordinate).re)
    (targetPositive : threshold <
      (wholeStateVorticityNonlinearCoefficientAt
        (run initial (stage + 1)).initialState output coordinate).re) :
    BoundaryPositiveRowDispositionIsNext
      (boundaryPositiveRowGenerate initial output coordinate threshold
        ((boundaryPositiveRowEventVocabulary initial output).emit
          ⟨.finite, .finite stage
            (generatedWholeRestartNativeActualOccurrence initial stage)⟩)
        (.finite stage
          (generatedWholeRestartNativeActualOccurrence initial stage)
          sourcePositive)) := by
  simp only [boundaryPositiveRowGenerate, dif_pos targetPositive,
    BoundaryPositiveRowDispositionIsNext]

private theorem boundaryPositiveRowGenerate_finite_isCut
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (output : IntegerWavevector)
    (coordinate : Fin 3)
    (threshold : Real)
    (stage : Nat)
    (sourcePositive : threshold <
      (wholeStateVorticityNonlinearCoefficientAt
        (run initial stage).initialState output coordinate).re)
    (targetNonpositive : ¬ threshold <
      (wholeStateVorticityNonlinearCoefficientAt
        (run initial (stage + 1)).initialState output coordinate).re) :
    BoundaryPositiveRowDispositionIsCut
      (boundaryPositiveRowGenerate initial output coordinate threshold
        ((boundaryPositiveRowEventVocabulary initial output).emit
          ⟨.finite, .finite stage
            (generatedWholeRestartNativeActualOccurrence initial stage)⟩)
        (.finite stage
          (generatedWholeRestartNativeActualOccurrence initial stage)
          sourcePositive)) := by
  simp only [boundaryPositiveRowGenerate, dif_neg targetNonpositive,
    BoundaryPositiveRowDispositionIsCut]

theorem boundaryPositiveRow_project_isNext_of_target
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (output : IntegerWavevector)
    (coordinate : Fin 3)
    (threshold : Real)
    (stage : Nat)
    (active : BoundaryPositiveRowActiveAt initial output coordinate threshold
      ((boundaryPositiveRowEventVocabulary initial output).emit
        (boundaryEmitted initial (.finite stage))))
    (targetPositive : threshold <
      (wholeStateVorticityNonlinearCoefficientAt
        (run initial (stage + 1)).initialState output coordinate).re) :
    BoundaryPositiveRowDispositionIsNext
      ((boundaryPositiveRowClosureLaw initial output coordinate threshold
        ).toProjectionLaw.project PUnit.unit
          (boundaryEmitted initial (.finite stage)) active) := by
  simp only [boundaryEmitted] at active ⊢
  have sourcePositive : threshold <
      (wholeStateVorticityNonlinearCoefficientAt
        (run initial stage).initialState output coordinate).re := by
    cases active with
    | finite _ _ positive => exact positive
  let canonicalActive : BoundaryPositiveRowActiveAt initial output coordinate
      threshold
      ((boundaryPositiveRowEventVocabulary initial output).emit
        ⟨.finite, .finite stage
          (generatedWholeRestartNativeActualOccurrence initial stage)⟩) :=
    .finite stage (generatedWholeRestartNativeActualOccurrence initial stage)
      sourcePositive
  have activeEq : active = canonicalActive := Subsingleton.elim _ _
  have generatedIsNext := boundaryPositiveRowGenerate_finite_isNext
    initial output coordinate threshold stage sourcePositive targetPositive
  change BoundaryPositiveRowDispositionIsNext
    (boundaryPositiveRowGenerate initial output coordinate threshold
      ((boundaryPositiveRowEventVocabulary initial output).emit
        ⟨.finite, .finite stage
          (generatedWholeRestartNativeActualOccurrence initial stage)⟩)
      active)
  rw [activeEq]
  simpa only [canonicalActive] using generatedIsNext

theorem boundaryPositiveRow_project_isCut_of_target_failure
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (output : IntegerWavevector)
    (coordinate : Fin 3)
    (threshold : Real)
    (stage : Nat)
    (active : BoundaryPositiveRowActiveAt initial output coordinate threshold
      ((boundaryPositiveRowEventVocabulary initial output).emit
        (boundaryEmitted initial (.finite stage))))
    (targetNonpositive : ¬ threshold <
      (wholeStateVorticityNonlinearCoefficientAt
        (run initial (stage + 1)).initialState output coordinate).re) :
    BoundaryPositiveRowDispositionIsCut
      ((boundaryPositiveRowClosureLaw initial output coordinate threshold
        ).toProjectionLaw.project PUnit.unit
          (boundaryEmitted initial (.finite stage)) active) := by
  simp only [boundaryEmitted] at active ⊢
  have sourcePositive : threshold <
      (wholeStateVorticityNonlinearCoefficientAt
        (run initial stage).initialState output coordinate).re := by
    cases active with
    | finite _ _ positive => exact positive
  let canonicalActive : BoundaryPositiveRowActiveAt initial output coordinate
      threshold
      ((boundaryPositiveRowEventVocabulary initial output).emit
        ⟨.finite, .finite stage
          (generatedWholeRestartNativeActualOccurrence initial stage)⟩) :=
    .finite stage (generatedWholeRestartNativeActualOccurrence initial stage)
      sourcePositive
  have activeEq : active = canonicalActive := Subsingleton.elim _ _
  have generatedIsCut := boundaryPositiveRowGenerate_finite_isCut
    initial output coordinate threshold stage sourcePositive targetNonpositive
  change BoundaryPositiveRowDispositionIsCut
    (boundaryPositiveRowGenerate initial output coordinate threshold
      ((boundaryPositiveRowEventVocabulary initial output).emit
        ⟨.finite, .finite stage
          (generatedWholeRestartNativeActualOccurrence initial stage)⟩)
      active)
  rw [activeEq]
  simpa only [canonicalActive] using generatedIsCut

/-! The outflux law installs an actual receipt-wide nonlinear depletion as the
    recursive effect.  A generated `next` contains the dependent target
    receipt witness; failure to regenerate that exact witness is the finite
    obstruction sent to the same-root U7 calculus. -/

def boundaryPositiveOutfluxEffectAtLower
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    {current : NativeTemporalCurrent initial}
    (occurrence :
      (boundarySource initial).toRootSource.actual.OccurrenceAt current) :
    Real := by
  rcases occurrence with ⟨support, event⟩
  cases event with
  | finite stage _ =>
      exact -nativeTemporalProjectedWholeEnstrophyPower
        (run initial stage).contact.prefixReceipt modes 0
  | cofinal _ => exact 0
  | galerkin _ _ => exact 0

def boundaryPositiveOutfluxEventVocabulary
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector) :
    SourceNativeEffectEventVocabulary (boundaryLedgerSource initial) where
  Effect := Real
  Operational := BoundaryFiniteEffectOperational
  effectAt := boundaryPositiveOutfluxEffectAtLower initial modes
  operationalAt := boundaryPositiveRowOperationalAtLower initial

inductive BoundaryPositiveOutfluxActiveAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (threshold : Real) :
    {current : NativeTemporalCurrent initial} →
      SourceNativeEffectOccurrenceAt
        (boundaryPositiveOutfluxEventVocabulary initial modes) current → Type
  | finite
      (stage : Nat)
      (occurrence : GeneratedWholeRestartNativeActualOccurrenceAt initial stage)
      (positive : NativeTemporalPositiveOutfluxAt
        (run initial stage).contact.prefixReceipt modes threshold) :
      BoundaryPositiveOutfluxActiveAt initial modes threshold
        ((boundaryPositiveOutfluxEventVocabulary initial modes).emit
          ⟨.finite, .finite stage occurrence⟩)

instance boundaryPositiveOutfluxActiveAt_subsingleton
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {modes : Finset IntegerWavevector}
    {threshold : Real}
    {current : NativeTemporalCurrent initial}
    {occurrence : SourceNativeEffectOccurrenceAt
      (boundaryPositiveOutfluxEventVocabulary initial modes) current} :
  Subsingleton
      (BoundaryPositiveOutfluxActiveAt initial modes threshold occurrence) where
  allEq := by
    intro left right
    cases left
    cases right
    rfl

def boundaryPositiveOutfluxVocabulary
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (threshold : Real) :
    SourceNativeEffectDynamicalVocabulary
      (boundaryPositiveOutfluxEventVocabulary initial modes) where
  ActiveAt := BoundaryPositiveOutfluxActiveAt initial modes threshold
  InactiveAt := fun occurrence =>
    PLift (IsEmpty
      (BoundaryPositiveOutfluxActiveAt initial modes threshold occurrence))
  classify := by
    intro current occurrence
    classical
    by_cases active : Nonempty
        (BoundaryPositiveOutfluxActiveAt initial modes threshold occurrence)
    · exact .inl active.some
    · exact .inr ⟨⟨fun effect => active ⟨effect⟩⟩⟩
  effectEntryAt := by
    intro current occurrence active
    cases active
    exact boundaryFiniteEntry initial
  updateEffectAt := by
    intro current occurrence active sourceEffect
    cases active with
    | finite stage _ _ =>
      exact -nativeTemporalProjectedWholeEnstrophyPower
        (run initial (stage + 1)).contact.prefixReceipt modes 0
  updateOperationalAt := by
    intro current occurrence active sourceEffect sourceOperational
    cases active with
    | finite stage _ _ =>
      exact
        { stage := stage + 1
          elapsed := elapsedTime initial (stage + 1)
          coefficientCeiling := restartCoefficientCeiling initial (stage + 1)
          contactTime := (run initial (stage + 1)).contact.time.1 }

def boundaryPositiveOutfluxGenerate
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (threshold : Real)
    {current : NativeTemporalCurrent initial}
    (occurrence : SourceNativeEffectOccurrenceAt
      (boundaryPositiveOutfluxEventVocabulary initial modes) current)
    (active : BoundaryPositiveOutfluxActiveAt initial modes threshold occurrence) :
    SourceNativeEffectDynamicalDispositionAt
      (boundaryPositiveOutfluxVocabulary initial modes threshold)
      (boundaryU7Calculus initial) occurrence active
      ((boundaryLedgerCompiler initial).compile occurrence.lower) := by
  cases active with
  | finite stage finiteOccurrence sourcePositive =>
      let successor :=
        (@SourceNativeEffectGeneratedSuccessorAt.ofGenerated?
          (BN initial) (BV initial) (boundaryLedgerSource initial)
          (.finite stage) ⟨.finite, .finite stage finiteOccurrence⟩
          ((boundaryLedgerCompiler initial).compile
            ⟨.finite, .finite stage finiteOccurrence⟩)).get (by rfl)
      by_cases targetPositive : NativeTemporalPositiveOutfluxAt
          (run initial (stage + 1)).contact.prefixReceipt modes threshold
      · let targetActive :
            BoundaryPositiveOutfluxActiveAt initial modes threshold
              ((boundaryPositiveOutfluxEventVocabulary initial modes).emit
                successor.targetOccurrence) :=
          .finite (stage + 1)
            (generatedWholeRestartNativeActualOccurrence initial (stage + 1))
            targetPositive
        exact .next
          (boundaryFiniteGeneratedEffectEntry initial stage finiteOccurrence)
          successor targetActive
          (by
            classical
            change
              (if witness : Nonempty
                    (BoundaryPositiveOutfluxActiveAt initial modes threshold
                      ((boundaryPositiveOutfluxEventVocabulary initial modes).emit
                        successor.targetOccurrence)) then
                  Sum.inl witness.some
                else Sum.inr _) = Sum.inl targetActive
            rw [dif_pos ⟨targetActive⟩]
            congr
            exact (boundaryPositiveOutfluxActiveAt_subsingleton
              (initial := initial)
              (modes := modes)
              (threshold := threshold)
              (current := successor.targetCurrent)
              (occurrence :=
                (boundaryPositiveOutfluxEventVocabulary initial modes).emit
                  successor.targetOccurrence)).allEq _ _)
          ⟨by rfl⟩ rfl rfl
          (.operationalChanged (fun progressEq => by
            have stageEq := congrArg BoundaryFiniteEffectOperational.stage
              progressEq
            exact (Nat.ne_of_lt (Nat.lt_succ_self stage)) stageEq))
      · let row :=
          boundaryFiniteGeneratedEffectEntry initial stage finiteOccurrence
        refine .cut row successor
          (.positiveOutflux stage modes threshold sourcePositive targetPositive)
          rfl ?_
        have commutes := row.down.commutes_with_world
        rcases commutes with ⟨_, evolution_heq⟩
        cases evolution_heq
        rfl

def boundaryPositiveOutfluxClosureLaw
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (threshold : Real) :
    SourceNativeEffectDynamicalClosureLaw (boundaryLedgerSource initial) :=
  .create (boundaryU7 initial) (boundaryU7Calculus initial)
    (boundaryPositiveOutfluxEventVocabulary initial modes)
    (boundaryPositiveOutfluxVocabulary initial modes threshold)
    (boundaryPositiveOutfluxGenerate initial modes threshold)

@[simp] theorem boundaryPositiveOutfluxClosureLaw_project
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (threshold : Real)
    {current : NativeTemporalCurrent initial}
    (occurrence :
      (boundarySource initial).toRootSource.actual.OccurrenceAt current)
    (active : BoundaryPositiveOutfluxActiveAt initial modes threshold
      ((boundaryPositiveOutfluxEventVocabulary initial modes).emit occurrence)) :
    (boundaryPositiveOutfluxClosureLaw initial modes threshold
      ).toProjectionLaw.project PUnit.unit occurrence active =
      boundaryPositiveOutfluxGenerate initial modes threshold
        ((boundaryPositiveOutfluxEventVocabulary initial modes).emit occurrence)
        active :=
  rfl

def BoundaryPositiveOutfluxDispositionIsNext
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {modes : Finset IntegerWavevector}
    {threshold : Real}
    {current : NativeTemporalCurrent initial}
    {occurrence : (boundarySource initial).toRootSource.actual.OccurrenceAt current}
    {active : BoundaryPositiveOutfluxActiveAt initial modes threshold
      ((boundaryPositiveOutfluxEventVocabulary initial modes).emit occurrence)}
    (disposition : SourceNativeGeneratedEffectDynamicalClosureAt
      (boundaryPositiveOutfluxClosureLaw initial modes threshold)
      occurrence active) : Prop :=
  match disposition with
  | .next .. => True
  | .settled .. | .cut .. => False

def BoundaryPositiveOutfluxDispositionIsCut
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {modes : Finset IntegerWavevector}
    {threshold : Real}
    {current : NativeTemporalCurrent initial}
    {occurrence : (boundarySource initial).toRootSource.actual.OccurrenceAt current}
    {active : BoundaryPositiveOutfluxActiveAt initial modes threshold
      ((boundaryPositiveOutfluxEventVocabulary initial modes).emit occurrence)}
    (disposition : SourceNativeGeneratedEffectDynamicalClosureAt
      (boundaryPositiveOutfluxClosureLaw initial modes threshold)
      occurrence active) : Prop :=
  match disposition with
  | .cut .. => True
  | .settled .. | .next .. => False

private theorem boundaryPositiveOutfluxGenerate_finite_isNext
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (threshold : Real)
    (stage : Nat)
    (sourcePositive : NativeTemporalPositiveOutfluxAt
      (run initial stage).contact.prefixReceipt modes threshold)
    (targetPositive : NativeTemporalPositiveOutfluxAt
      (run initial (stage + 1)).contact.prefixReceipt modes threshold) :
    BoundaryPositiveOutfluxDispositionIsNext
      (boundaryPositiveOutfluxGenerate initial modes threshold
        ((boundaryPositiveOutfluxEventVocabulary initial modes).emit
          ⟨.finite, .finite stage
            (generatedWholeRestartNativeActualOccurrence initial stage)⟩)
        (.finite stage
          (generatedWholeRestartNativeActualOccurrence initial stage)
          sourcePositive)) := by
  simp only [boundaryPositiveOutfluxGenerate, dif_pos targetPositive,
    BoundaryPositiveOutfluxDispositionIsNext]

private theorem boundaryPositiveOutfluxGenerate_finite_isCut
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (threshold : Real)
    (stage : Nat)
    (sourcePositive : NativeTemporalPositiveOutfluxAt
      (run initial stage).contact.prefixReceipt modes threshold)
    (targetNonpositive : ¬ NativeTemporalPositiveOutfluxAt
      (run initial (stage + 1)).contact.prefixReceipt modes threshold) :
    BoundaryPositiveOutfluxDispositionIsCut
      (boundaryPositiveOutfluxGenerate initial modes threshold
        ((boundaryPositiveOutfluxEventVocabulary initial modes).emit
          ⟨.finite, .finite stage
            (generatedWholeRestartNativeActualOccurrence initial stage)⟩)
        (.finite stage
          (generatedWholeRestartNativeActualOccurrence initial stage)
          sourcePositive)) := by
  simp only [boundaryPositiveOutfluxGenerate, dif_neg targetNonpositive,
    BoundaryPositiveOutfluxDispositionIsCut]

theorem boundaryPositiveOutflux_project_isNext_of_target
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (threshold : Real)
    (stage : Nat)
    (active : BoundaryPositiveOutfluxActiveAt initial modes threshold
      ((boundaryPositiveOutfluxEventVocabulary initial modes).emit
        (boundaryEmitted initial (.finite stage))))
    (targetPositive : NativeTemporalPositiveOutfluxAt
      (run initial (stage + 1)).contact.prefixReceipt modes threshold) :
    BoundaryPositiveOutfluxDispositionIsNext
      ((boundaryPositiveOutfluxClosureLaw initial modes threshold
        ).toProjectionLaw.project PUnit.unit
          (boundaryEmitted initial (.finite stage)) active) := by
  simp only [boundaryEmitted] at active ⊢
  have sourcePositive : NativeTemporalPositiveOutfluxAt
      (run initial stage).contact.prefixReceipt modes threshold := by
    cases active with
    | finite _ _ positive => exact positive
  let canonicalActive : BoundaryPositiveOutfluxActiveAt initial modes threshold
      ((boundaryPositiveOutfluxEventVocabulary initial modes).emit
        ⟨.finite, .finite stage
          (generatedWholeRestartNativeActualOccurrence initial stage)⟩) :=
    .finite stage (generatedWholeRestartNativeActualOccurrence initial stage)
      sourcePositive
  have activeEq : active = canonicalActive := Subsingleton.elim _ _
  have generatedIsNext := boundaryPositiveOutfluxGenerate_finite_isNext
    initial modes threshold stage sourcePositive targetPositive
  change BoundaryPositiveOutfluxDispositionIsNext
    (boundaryPositiveOutfluxGenerate initial modes threshold
      ((boundaryPositiveOutfluxEventVocabulary initial modes).emit
        ⟨.finite, .finite stage
          (generatedWholeRestartNativeActualOccurrence initial stage)⟩)
      active)
  rw [activeEq]
  simpa only [canonicalActive] using generatedIsNext

theorem boundaryPositiveOutflux_project_isCut_of_target_failure
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (threshold : Real)
    (stage : Nat)
    (active : BoundaryPositiveOutfluxActiveAt initial modes threshold
      ((boundaryPositiveOutfluxEventVocabulary initial modes).emit
        (boundaryEmitted initial (.finite stage))))
    (targetNonpositive : ¬ NativeTemporalPositiveOutfluxAt
      (run initial (stage + 1)).contact.prefixReceipt modes threshold) :
    BoundaryPositiveOutfluxDispositionIsCut
      ((boundaryPositiveOutfluxClosureLaw initial modes threshold
        ).toProjectionLaw.project PUnit.unit
          (boundaryEmitted initial (.finite stage)) active) := by
  simp only [boundaryEmitted] at active ⊢
  have sourcePositive : NativeTemporalPositiveOutfluxAt
      (run initial stage).contact.prefixReceipt modes threshold := by
    cases active with
    | finite _ _ positive => exact positive
  let canonicalActive : BoundaryPositiveOutfluxActiveAt initial modes threshold
      ((boundaryPositiveOutfluxEventVocabulary initial modes).emit
        ⟨.finite, .finite stage
          (generatedWholeRestartNativeActualOccurrence initial stage)⟩) :=
    .finite stage (generatedWholeRestartNativeActualOccurrence initial stage)
      sourcePositive
  have activeEq : active = canonicalActive := Subsingleton.elim _ _
  have generatedIsCut := boundaryPositiveOutfluxGenerate_finite_isCut
    initial modes threshold stage sourcePositive targetNonpositive
  change BoundaryPositiveOutfluxDispositionIsCut
    (boundaryPositiveOutfluxGenerate initial modes threshold
      ((boundaryPositiveOutfluxEventVocabulary initial modes).emit
        ⟨.finite, .finite stage
          (generatedWholeRestartNativeActualOccurrence initial stage)⟩)
      active)
  rw [activeEq]
  simpa only [canonicalActive] using generatedIsCut

/-! ## No-free reactivation of a recursive effect

The active effect compiler above closes only an active visit.  The same
installed row also needs a source-owned disposition while its observed
outflux is inactive; otherwise a later positive occurrence could be
registered independently of the causal row which previously cut. -/

def boundaryPositiveOutfluxInactiveEntryAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (threshold : Real)
    {current : NativeTemporalCurrent initial}
    (occurrence : SourceNativeEffectOccurrenceAt
      (boundaryPositiveOutfluxEventVocabulary initial modes) current)
    (_inactive : (boundaryPositiveOutfluxVocabulary initial modes threshold
      ).InactiveAt occurrence) :
    OpenResponsibilityAt (BN initial)
      ((boundarySource initial).toRootSource.account.supportOf occurrence.lower) := by
  rcases occurrence with ⟨lower⟩
  rcases lower with ⟨support, event⟩
  change NativeTemporalRootEventAt initial current support at event
  cases event with
  | finite => exact boundaryFiniteEntry initial
  | cofinal => exact boundaryCofinalEntry initial
  | galerkin => exact boundaryCofinalEntry initial

/-- A return to positive outflux records the exact source stage and the
canonical next-stage positive witness.  The receipt contains no caller-picked
future path; its successor remains in the surrounding dependent index. -/
structure BoundaryPositiveOutfluxReactivationReceiptAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (threshold : Real)
    {current : NativeTemporalCurrent initial}
    (occurrence : SourceNativeEffectOccurrenceAt
      (boundaryPositiveOutfluxEventVocabulary initial modes) current)
    (_inactive : (boundaryPositiveOutfluxVocabulary initial modes threshold
      ).InactiveAt occurrence)
    {generated : SourceNativeLedgerEvolutionAt (boundarySource initial)
      occurrence.lower}
    (successor : SourceNativeEffectGeneratedSuccessorAt occurrence.lower generated)
    (targetActive : (boundaryPositiveOutfluxVocabulary initial modes threshold
      ).ActiveAt ((boundaryPositiveOutfluxEventVocabulary initial modes).emit
        successor.targetOccurrence)) : Type where
  sourceStage : Nat
  sourceOccurrence_eq : HEq occurrence.lower
    (boundaryEmitted initial (.finite sourceStage))
  targetPositive : NativeTemporalPositiveOutfluxAt
    (run initial (sourceStage + 1)).contact.prefixReceipt modes threshold
  targetActive_eq : HEq targetActive
    (BoundaryPositiveOutfluxActiveAt.finite (sourceStage + 1)
      (generatedWholeRestartNativeActualOccurrence initial (sourceStage + 1))
      targetPositive)

private theorem boundaryFiniteActualOccurrence_eq_canonical
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (stage : Nat)
    (occurrence : GeneratedWholeRestartNativeActualOccurrenceAt initial stage) :
    occurrence = generatedWholeRestartNativeActualOccurrence initial stage := by
  rcases occurrence with ⟨response, generated⟩
  have response_eq : response =
      (generatedWholeRestartNativeActualOccurrence initial stage).response := by
    apply Option.some.inj
    exact generated.symm.trans
      (generatedWholeRestartNativeActualOccurrence initial stage).generated
  cases response_eq
  rfl

def boundaryPositiveOutfluxDormantVocabulary
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (threshold : Real) :
    SourceNativeEffectDormantVocabulary
      (boundaryPositiveOutfluxVocabulary initial modes threshold) where
  inactiveEntryAt :=
    boundaryPositiveOutfluxInactiveEntryAt initial modes threshold
  ReactivationReceiptAt :=
    BoundaryPositiveOutfluxReactivationReceiptAt initial modes threshold

private def boundaryCofinalGeneratedEffectEntry
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (receipt : GeneratedWholeRestartCanonicalWeakCofinalReceiptAt initial) :
    SourceNativeEffectGeneratedEntryAt
      (source := boundaryLedgerSource initial)
      (occurrence := ⟨.cofinal, .cofinal receipt⟩)
      (boundaryCofinalEntry initial) :=
  ⟨(sourceNativeFiniteLedgerPatchGeneratedEntry?
      (boundarySource initial)
      (boundaryLedgerCompiler initial).ExactTransitionAt
      (boundaryWriteRowSource initial)
      (boundaryTerminalRowSource initial)
      ((boundaryLedgerCompiler initial).compile ⟨.cofinal, .cofinal receipt⟩)
      ((boundaryLedgerCompiler initial).compilePatch ⟨.cofinal, .cofinal receipt⟩)
      (boundaryCofinalEntry initial)).get (by rfl)⟩

private def boundaryGalerkinGeneratedEffectEntry
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (radius : Nat)
    (write : NativeTemporalGalerkinWriteAt initial radius) :
    SourceNativeEffectGeneratedEntryAt
      (source := boundaryLedgerSource initial)
      (occurrence := ⟨.cofinal, .galerkin radius write⟩)
      (boundaryCofinalEntry initial) :=
  ⟨(sourceNativeFiniteLedgerPatchGeneratedEntry?
      (boundarySource initial)
      (boundaryLedgerCompiler initial).ExactTransitionAt
      (boundaryWriteRowSource initial)
      (boundaryTerminalRowSource initial)
      ((boundaryLedgerCompiler initial).compile
        ⟨.cofinal, .galerkin radius write⟩)
      ((boundaryLedgerCompiler initial).compilePatch
        ⟨.cofinal, .galerkin radius write⟩)
      (boundaryCofinalEntry initial)).get (by rfl)⟩

def boundaryPositiveOutfluxGenerateInactive
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (threshold : Real)
    {current : NativeTemporalCurrent initial}
    (occurrence : SourceNativeEffectOccurrenceAt
      (boundaryPositiveOutfluxEventVocabulary initial modes) current)
    (inactive : (boundaryPositiveOutfluxVocabulary initial modes threshold
      ).InactiveAt occurrence) :
    SourceNativeDormantEffectDispositionAt
      (boundaryPositiveOutfluxVocabulary initial modes threshold)
      (boundaryPositiveOutfluxDormantVocabulary initial modes threshold)
      (boundaryU7Calculus initial) occurrence inactive
      ((boundaryLedgerCompiler initial).compile occurrence.lower) := by
  rcases occurrence with ⟨lower⟩
  rcases lower with ⟨support, event⟩
  change NativeTemporalRootEventAt initial current support at event
  cases event with
  | finite stage finiteOccurrence =>
      let successor :=
        (@SourceNativeEffectGeneratedSuccessorAt.ofGenerated?
          (BN initial) (BV initial) (boundaryLedgerSource initial)
          (.finite stage) ⟨.finite, .finite stage finiteOccurrence⟩
          ((boundaryLedgerCompiler initial).compile
            ⟨.finite, .finite stage finiteOccurrence⟩)).get (by rfl)
      let row := boundaryFiniteGeneratedEffectEntry initial stage finiteOccurrence
      by_cases targetPositive : NativeTemporalPositiveOutfluxAt
          (run initial (stage + 1)).contact.prefixReceipt modes threshold
      · let targetActive : BoundaryPositiveOutfluxActiveAt initial modes threshold
            ((boundaryPositiveOutfluxEventVocabulary initial modes).emit
              successor.targetOccurrence) :=
          .finite (stage + 1)
            (generatedWholeRestartNativeActualOccurrence initial (stage + 1))
            targetPositive
        have classifyEq :
            (boundaryPositiveOutfluxVocabulary initial modes threshold).classify
                ((boundaryPositiveOutfluxEventVocabulary initial modes).emit
                  successor.targetOccurrence) = .inl targetActive := by
          classical
          change (if witness : Nonempty
              (BoundaryPositiveOutfluxActiveAt initial modes threshold
                ((boundaryPositiveOutfluxEventVocabulary initial modes).emit
                  successor.targetOccurrence))
            then Sum.inl witness.some else Sum.inr _) = Sum.inl targetActive
          rw [dif_pos ⟨targetActive⟩]
          exact congrArg Sum.inl
            ((boundaryPositiveOutfluxActiveAt_subsingleton
              (initial := initial) (modes := modes) (threshold := threshold)
              (current := successor.targetCurrent)
              (occurrence :=
                (boundaryPositiveOutfluxEventVocabulary initial modes).emit
                  successor.targetOccurrence)).allEq _ _)
        have targetEntryEq :
            (successor.ledgerEvolution.destination
              (boundaryPositiveOutfluxInactiveEntryAt initial modes threshold
                (⟨⟨.finite, .finite stage finiteOccurrence⟩⟩ :
                  SourceNativeEffectOccurrenceAt
                    (boundaryPositiveOutfluxEventVocabulary initial modes)
                    (.finite stage)) inactive)).1 =
              (boundaryPositiveOutfluxVocabulary initial modes threshold
                ).effectEntryAt
                  ((boundaryPositiveOutfluxEventVocabulary initial modes).emit
                    successor.targetOccurrence) targetActive :=
          (boundaryOpenResponsibility_subsingleton initial .finite).elim _ _
        have sourceOccurrenceEq : HEq
            (⟨.finite, .finite stage finiteOccurrence⟩ :
              (boundarySource initial).toRootSource.actual.OccurrenceAt
                (.finite stage))
            (boundaryEmitted initial (.finite stage)) := by
          cases boundaryFiniteActualOccurrence_eq_canonical
            initial stage finiteOccurrence
          exact HEq.rfl
        exact .reactivated row successor targetActive classifyEq
          ⟨targetEntryEq⟩
          ⟨stage, sourceOccurrenceEq, targetPositive, HEq.rfl⟩
      · let targetInactive :
            (boundaryPositiveOutfluxVocabulary initial modes threshold).InactiveAt
              ((boundaryPositiveOutfluxEventVocabulary initial modes).emit
                successor.targetOccurrence) :=
          ⟨⟨fun active => by
            cases active with
            | finite _ _ positive => exact targetPositive positive⟩⟩
        have classifyEq :
            (boundaryPositiveOutfluxVocabulary initial modes threshold).classify
                ((boundaryPositiveOutfluxEventVocabulary initial modes).emit
                  successor.targetOccurrence) = .inr targetInactive := by
          classical
          change (if witness : Nonempty
              (BoundaryPositiveOutfluxActiveAt initial modes threshold
                ((boundaryPositiveOutfluxEventVocabulary initial modes).emit
                  successor.targetOccurrence))
            then Sum.inl witness.some else Sum.inr _) = Sum.inr targetInactive
          rw [dif_neg (fun witness => targetPositive <| by
            rcases witness with ⟨active⟩
            cases active with
            | finite _ _ positive => exact positive)]
        have targetEntryEq :
            (successor.ledgerEvolution.destination
              (boundaryPositiveOutfluxInactiveEntryAt initial modes threshold
                (⟨⟨.finite, .finite stage finiteOccurrence⟩⟩ :
                  SourceNativeEffectOccurrenceAt
                    (boundaryPositiveOutfluxEventVocabulary initial modes)
                    (.finite stage)) inactive)).1 =
              (boundaryPositiveOutfluxDormantVocabulary initial modes threshold
                ).inactiveEntryAt
                  ((boundaryPositiveOutfluxEventVocabulary initial modes).emit
                    successor.targetOccurrence) targetInactive :=
          (boundaryOpenResponsibility_subsingleton initial .finite).elim _ _
        exact .dormantNext row successor targetInactive classifyEq
          ⟨targetEntryEq⟩
  | cofinal receipt =>
      let successor :=
        (@SourceNativeEffectGeneratedSuccessorAt.ofGenerated?
          (BN initial) (BV initial) (boundaryLedgerSource initial)
          .cofinal ⟨.cofinal, .cofinal receipt⟩
          ((boundaryLedgerCompiler initial).compile
            ⟨.cofinal, .cofinal receipt⟩)).get (by rfl)
      let row := boundaryCofinalGeneratedEffectEntry initial receipt
      let targetInactive :
          (boundaryPositiveOutfluxVocabulary initial modes threshold).InactiveAt
            ((boundaryPositiveOutfluxEventVocabulary initial modes).emit
              successor.targetOccurrence) :=
        ⟨⟨fun active => by cases active⟩⟩
      have classifyEq :
          (boundaryPositiveOutfluxVocabulary initial modes threshold).classify
              ((boundaryPositiveOutfluxEventVocabulary initial modes).emit
                successor.targetOccurrence) = .inr targetInactive := by
        classical
        change (if witness : Nonempty
            (BoundaryPositiveOutfluxActiveAt initial modes threshold
              ((boundaryPositiveOutfluxEventVocabulary initial modes).emit
                successor.targetOccurrence))
          then Sum.inl witness.some else Sum.inr _) = Sum.inr targetInactive
        rw [dif_neg (fun witness => by rcases witness with ⟨active⟩; cases active)]
      have targetEntryEq :
          (successor.ledgerEvolution.destination (boundaryCofinalEntry initial)).1 =
            (boundaryPositiveOutfluxDormantVocabulary initial modes threshold
              ).inactiveEntryAt
                ((boundaryPositiveOutfluxEventVocabulary initial modes).emit
                  successor.targetOccurrence) targetInactive :=
        (boundaryOpenResponsibility_subsingleton initial .cofinal).elim _ _
      exact .dormantNext row successor targetInactive classifyEq ⟨targetEntryEq⟩
  | galerkin radius write =>
      let successor :=
        (@SourceNativeEffectGeneratedSuccessorAt.ofGenerated?
          (BN initial) (BV initial) (boundaryLedgerSource initial)
          (.galerkin radius) ⟨.cofinal, .galerkin radius write⟩
          ((boundaryLedgerCompiler initial).compile
            ⟨.cofinal, .galerkin radius write⟩)).get (by rfl)
      let row := boundaryGalerkinGeneratedEffectEntry initial radius write
      let targetInactive :
          (boundaryPositiveOutfluxVocabulary initial modes threshold).InactiveAt
            ((boundaryPositiveOutfluxEventVocabulary initial modes).emit
              successor.targetOccurrence) :=
        ⟨⟨fun active => by cases active⟩⟩
      have classifyEq :
          (boundaryPositiveOutfluxVocabulary initial modes threshold).classify
              ((boundaryPositiveOutfluxEventVocabulary initial modes).emit
                successor.targetOccurrence) = .inr targetInactive := by
        classical
        change (if witness : Nonempty
            (BoundaryPositiveOutfluxActiveAt initial modes threshold
              ((boundaryPositiveOutfluxEventVocabulary initial modes).emit
                successor.targetOccurrence))
          then Sum.inl witness.some else Sum.inr _) = Sum.inr targetInactive
        rw [dif_neg (fun witness => by rcases witness with ⟨active⟩; cases active)]
      have targetEntryEq :
          (successor.ledgerEvolution.destination (boundaryCofinalEntry initial)).1 =
            (boundaryPositiveOutfluxDormantVocabulary initial modes threshold
              ).inactiveEntryAt
                ((boundaryPositiveOutfluxEventVocabulary initial modes).emit
                  successor.targetOccurrence) targetInactive :=
        (boundaryOpenResponsibility_subsingleton initial .cofinal).elim _ _
      exact .dormantNext row successor targetInactive classifyEq ⟨targetEntryEq⟩

def boundaryPositiveOutfluxReactivationLaw
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (threshold : Real) :
    SourceNativeEffectReactivationClosureLaw (boundaryLedgerSource initial) :=
  .create (boundaryPositiveOutfluxClosureLaw initial modes threshold)
    (boundaryPositiveOutfluxDormantVocabulary initial modes threshold)
    (boundaryPositiveOutfluxGenerateInactive initial modes threshold)

/-! ## Fixed original-root inquiry projection

The final authoritative root keeps the conservative whole-ledger coordinate
and the inquiry coordinates emitted by its fixed compiler.  Their carrier is
public for faithful downstream restriction, but coordinate construction stays
private so a caller cannot turn an external proposition into root authority.
-/

private inductive BoundaryFinalProjectionCoordinate
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) : Type
  | evolution
  | resolution
  | answer
  | consumer
  | failure
  | positiveRow
      (output : IntegerWavevector)
      (coordinate : Fin 3)
      (threshold : Real)
  | positiveOutflux
      (modes : Finset IntegerWavevector)
      (threshold : Real)
  | positiveOutfluxLifecycle
      (modes : Finset IntegerWavevector)
      (threshold : Real)

/-- Projection coordinates are readable outside this module but can only be
issued by the fixed boundary source compiler.  In particular, an external
boundedness proof cannot be repackaged as a root failure coordinate. -/
structure BoundaryFinalProjection
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) : Type where
  private mk ::
  private coordinate : BoundaryFinalProjectionCoordinate initial

namespace BoundaryFinalProjection

private def evolution
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu} :
    BoundaryFinalProjection initial :=
  ⟨BoundaryFinalProjectionCoordinate.evolution⟩

private def resolution
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu} :
    BoundaryFinalProjection initial :=
  ⟨BoundaryFinalProjectionCoordinate.resolution⟩

private def answer
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu} :
    BoundaryFinalProjection initial :=
  ⟨BoundaryFinalProjectionCoordinate.answer⟩

private def consumer
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu} :
    BoundaryFinalProjection initial :=
  ⟨BoundaryFinalProjectionCoordinate.consumer⟩

private def failure
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu} :
    BoundaryFinalProjection initial :=
  ⟨BoundaryFinalProjectionCoordinate.failure⟩

private def positiveRow
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    (output : IntegerWavevector)
    (coordinate : Fin 3)
    (threshold : Real) :
    BoundaryFinalProjection initial :=
  ⟨BoundaryFinalProjectionCoordinate.positiveRow output coordinate threshold⟩

private def positiveOutflux
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    (modes : Finset IntegerWavevector)
    (threshold : Real) :
    BoundaryFinalProjection initial :=
  ⟨BoundaryFinalProjectionCoordinate.positiveOutflux modes threshold⟩

private def positiveOutfluxLifecycle
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    (modes : Finset IntegerWavevector)
    (threshold : Real) :
    BoundaryFinalProjection initial :=
  ⟨BoundaryFinalProjectionCoordinate.positiveOutfluxLifecycle modes threshold⟩

end BoundaryFinalProjection

def boundaryInquiryEvent
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :=
  ULift.up.{1, 0} (boundaryEmitted initial .cofinal)

@[simp] theorem boundaryInquiryEvent_down
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    (boundaryInquiryEvent initial).down = boundaryEmitted initial .cofinal :=
  rfl

/-- Domain presentation of the answer coordinate emitted by the root.  This
is a projection payload, not an independent inquiry result contract. -/
inductive BoundaryInquiryResultAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) : Type
  | unbounded
      (elapsedUnbounded : ¬ BddAbove (Set.range (elapsedTime initial)))
  | revised
      (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))

/-- Source-native decision emitted at the exact cofinal boundary. -/
private inductive BoundaryInquiryDecisionAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) : Type
  | unbounded (receipt : ¬ BddAbove (Set.range (elapsedTime initial)))
  | requiresRevision (receipt : BddAbove (Set.range (elapsedTime initial)))

private noncomputable def boundaryInquiryDecision
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    BoundaryInquiryDecisionAt initial := by
  by_cases elapsedBounded : BddAbove (Set.range (elapsedTime initial))
  · exact .requiresRevision elapsedBounded
  · exact .unbounded elapsedBounded

/-- The original cofinal source either answers in the old language or emits
the exact obstruction whose U7 theory-audit demand opens revision audit. -/
noncomputable def boundaryInquiryFrontAudit
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    SourceNativeInquiryFrontAuditAt
      (boundaryU7 initial) (boundaryU7Calculus initial)
      (boundaryOldTheory initial) .cofinal :=
  match boundaryInquiryDecision initial with
  | .unbounded _ => .answered
  | .requiresRevision elapsedBounded =>
      let obstruction := boundaryObstruction initial elapsedBounded
      .obstructed obstruction
        (.requiresU8
          (boundaryCofinalU7TheoryAudit initial obstruction)
          (boundaryExpressibilityFailure initial obstruction))

private structure BoundaryInquiryTokenAnswerAt
    {nu : Viscosity}
    (_initial : GeneratedWholeRestartCurrent nu) : Type 1 where
  Carrier : Type
  readout : Carrier

/-- Source-level answer identity paired with the boundary inquiry audit. -/
private noncomputable def boundaryInquiryTokenAnswer
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    BoundaryInquiryTokenAnswerAt initial :=
  match boundaryInquiryDecision initial with
  | .unbounded elapsedUnbounded =>
      ⟨BoundaryInquiryResultAt initial, .unbounded elapsedUnbounded⟩
  | .requiresRevision _ => ⟨PUnit, PUnit.unit⟩

private def boundaryFinalProjectionActiveAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (projection : BoundaryFinalProjection initial)
    {current : (BV initial).Current}
    (_occurrence :
      (boundarySource initial).toRootSource.actual.OccurrenceAt current) : Type :=
  match projection.coordinate with
  | .evolution => PUnit
  | .resolution => PLift (current = .cofinal)
  | .answer => PLift
      (current = .cofinal ∧ ¬ BddAbove (Set.range (elapsedTime initial)))
  | .consumer => PLift
      (current = .cofinal ∧ ¬ BddAbove (Set.range (elapsedTime initial)))
  | .failure => PLift
      (current = .cofinal ∧ BddAbove (Set.range (elapsedTime initial)))
  | .positiveRow output coordinate threshold =>
      (boundaryPositiveRowClosureLaw initial output coordinate threshold
        ).toProjectionLaw.ActiveAt PUnit.unit _occurrence
  | .positiveOutflux modes threshold =>
      (boundaryPositiveOutfluxClosureLaw initial modes threshold
        ).toProjectionLaw.ActiveAt PUnit.unit _occurrence
  | .positiveOutfluxLifecycle modes threshold =>
      (boundaryPositiveOutfluxReactivationLaw initial modes threshold
        ).toProjectionLaw.ActiveAt PUnit.unit _occurrence

private def boundaryFinalProjectionInactiveAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (projection : BoundaryFinalProjection initial)
    {current : (BV initial).Current}
    (_occurrence :
      (boundarySource initial).toRootSource.actual.OccurrenceAt current) : Type :=
  match projection.coordinate with
  | .evolution => PEmpty
  | .resolution => PLift (current ≠ .cofinal)
  | .answer => PLift
      (current ≠ .cofinal ∨ BddAbove (Set.range (elapsedTime initial)))
  | .consumer => PLift
      (current ≠ .cofinal ∨ BddAbove (Set.range (elapsedTime initial)))
  | .failure => PLift
      (current ≠ .cofinal ∨ ¬ BddAbove (Set.range (elapsedTime initial)))
  | .positiveRow output coordinate threshold =>
      (boundaryPositiveRowClosureLaw initial output coordinate threshold
        ).toProjectionLaw.InactiveAt PUnit.unit _occurrence
  | .positiveOutflux modes threshold =>
      (boundaryPositiveOutfluxClosureLaw initial modes threshold
        ).toProjectionLaw.InactiveAt PUnit.unit _occurrence
  | .positiveOutfluxLifecycle modes threshold =>
      (boundaryPositiveOutfluxReactivationLaw initial modes threshold
        ).toProjectionLaw.InactiveAt PUnit.unit _occurrence

private def boundaryFinalProjectionPayloadAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (projection : BoundaryFinalProjection initial)
    {current : (BV initial).Current}
    (occurrence :
      (boundarySource initial).toRootSource.actual.OccurrenceAt current)
    (active : boundaryFinalProjectionActiveAt initial projection occurrence) :
    Type := by
  rcases projection with ⟨coordinate⟩
  cases coordinate with
  | evolution =>
      exact SourceNativeLedgerEvolutionAt (boundarySource initial) occurrence
  | resolution =>
      exact SourceNativeInquiryCompilationTokenAt
        (boundaryCofinalEntry initial) PUnit.unit
        (ULift.up.{1, 0} occurrence)
        (boundaryInquiryFrontAudit initial)
        (boundaryInquiryTokenAnswer initial).Carrier
  | answer => exact BoundaryInquiryResultAt initial
  | consumer =>
      exact SourceNativeInquiryAnswerConsumerTokenAt
        PUnit.unit (ULift.up.{1, 0} occurrence)
        (boundaryCofinalEntry initial)
        (.unbounded active.down.2 : BoundaryInquiryResultAt initial)
  | failure =>
      let obstruction := boundaryObstruction initial active.down.2
      exact SourceNativeRootExpressibilityFailureTokenAt
        (boundaryExpressibilityFailure initial obstruction)
        (boundaryU7Calculus initial)
        ((boundaryU7Calculus initial).source.emit obstruction)
  | positiveRow output coordinate threshold =>
      exact (boundaryPositiveRowClosureLaw initial output coordinate threshold
        ).toProjectionLaw.PayloadAt PUnit.unit occurrence active
  | positiveOutflux modes threshold =>
      exact (boundaryPositiveOutfluxClosureLaw initial modes threshold
        ).toProjectionLaw.PayloadAt PUnit.unit occurrence active
  | positiveOutfluxLifecycle modes threshold =>
      exact (boundaryPositiveOutfluxReactivationLaw initial modes threshold
        ).toProjectionLaw.PayloadAt PUnit.unit occurrence active

def boundaryFinalProjectionLaw
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    SourceNativeProjectionLaw
      (boundaryRestructuringSource initial).toLedgerSource where
  Projection := BoundaryFinalProjection initial
  ActiveAt := boundaryFinalProjectionActiveAt initial
  InactiveAt := boundaryFinalProjectionInactiveAt initial
  classify := by
    intro projection current occurrence
    rcases projection with ⟨coordinate⟩
    cases coordinate with
    | evolution => exact .inl PUnit.unit
    | resolution =>
        cases current with
        | finite stage =>
            exact .inr ⟨by intro equality; cases equality⟩
        | cofinal => exact .inl ⟨rfl⟩
        | galerkin radius =>
            exact .inr ⟨by intro equality; cases equality⟩
    | answer =>
        cases current with
        | finite _ =>
            exact .inr ⟨Or.inl (by intro equality; cases equality)⟩
        | cofinal =>
            by_cases elapsedBounded : BddAbove (Set.range (elapsedTime initial))
            · exact .inr ⟨Or.inr elapsedBounded⟩
            · exact .inl ⟨rfl, elapsedBounded⟩
        | galerkin _ =>
            exact .inr ⟨Or.inl (by intro equality; cases equality)⟩
    | consumer =>
        cases current with
        | finite _ =>
            exact .inr ⟨Or.inl (by intro equality; cases equality)⟩
        | cofinal =>
            by_cases elapsedBounded : BddAbove (Set.range (elapsedTime initial))
            · exact .inr ⟨Or.inr elapsedBounded⟩
            · exact .inl ⟨rfl, elapsedBounded⟩
        | galerkin _ =>
            exact .inr ⟨Or.inl (by intro equality; cases equality)⟩
    | failure =>
        cases current with
        | finite _ =>
            exact .inr ⟨Or.inl (by intro equality; cases equality)⟩
        | cofinal =>
            by_cases elapsedBounded : BddAbove (Set.range (elapsedTime initial))
            · exact .inl ⟨rfl, elapsedBounded⟩
            · exact .inr ⟨Or.inr elapsedBounded⟩
        | galerkin _ =>
            exact .inr ⟨Or.inl (by intro equality; cases equality)⟩
    | positiveRow output coordinate threshold =>
        exact (boundaryPositiveRowClosureLaw initial output coordinate threshold
          ).toProjectionLaw.classify PUnit.unit occurrence
    | positiveOutflux modes threshold =>
        exact (boundaryPositiveOutfluxClosureLaw initial modes threshold
          ).toProjectionLaw.classify PUnit.unit occurrence
    | positiveOutfluxLifecycle modes threshold =>
        exact (boundaryPositiveOutfluxReactivationLaw initial modes threshold
          ).toProjectionLaw.classify PUnit.unit occurrence
  PayloadAt := boundaryFinalProjectionPayloadAt initial
  project := by
    intro projection current occurrence active
    rcases projection with ⟨coordinate⟩
    cases coordinate with
    | evolution =>
        exact (boundaryLedgerCompiler initial).compile occurrence
    | resolution =>
        exact SourceNativeInquiryCompilationTokenAt.canonical
          (boundaryInquiryTokenAnswer initial).readout
    | answer => exact .unbounded active.down.2
    | consumer => exact .canonical
    | failure =>
        exact SourceNativeRootExpressibilityFailureTokenAt.canonical
    | positiveRow output coordinate threshold =>
        exact (boundaryPositiveRowClosureLaw initial output coordinate threshold
          ).toProjectionLaw.project PUnit.unit occurrence active
    | positiveOutflux modes threshold =>
        exact (boundaryPositiveOutfluxClosureLaw initial modes threshold
          ).toProjectionLaw.project PUnit.unit occurrence active
    | positiveOutfluxLifecycle modes threshold =>
        exact (boundaryPositiveOutfluxReactivationLaw initial modes threshold
          ).toProjectionLaw.project PUnit.unit occurrence active

private def boundaryFinalAuthoritySource
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    SourceNativeAuthoritySource (BN initial) (BV initial) where
  restructuringSource := boundaryRestructuringSource initial
  eventInventoryAdmission :=
    .reflOfNoFaithfulTerminal (boundaryRestructuringSource initial)
      (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := boundaryOldTheory initial
  projectionLaw := boundaryFinalProjectionLaw initial

private def boundaryFinalAuthoritativeRoot
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    SourceNativeAuthoritativeRootClosure (BN initial) (BV initial) where
  source := boundaryFinalAuthoritySource initial
  emitted := boundaryEmitted initial
  compiler_commutes := by intro current; cases current <;> rfl

def boundaryFinalLivingRoot
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    SourceNativeLivingRootClosure (BN initial) (BV initial) :=
  (boundaryFinalAuthoritativeRoot initial).toLivingWithoutFaithfulTerminal
    (fun current => by
      cases current <;> exact ⟨fun terminal => nomatch terminal⟩)

/-- Every positive-row effect coordinate was already installed in the final
boundary source before its emitter.  The singleton component projection is
only a coordinate selector; its complete dependent payload is the one read by
the fixed root inventory. -/
def boundaryPositiveRowInstallation
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (output : IntegerWavevector)
    (coordinate : Fin 3)
    (threshold : Real) :
    SourceNativeProjectionLaw.InstallationAt
      (boundaryPositiveRowClosureLaw initial output coordinate threshold
        ).toProjectionLaw
      (boundaryFinalProjectionLaw initial) where
  embed := fun _ => BoundaryFinalProjection.positiveRow output coordinate threshold
  embed_injective := by
    intro left right _
    cases left
    cases right
    rfl
  outcome_heq := by
    intro current occurrence projection
    cases projection
    unfold SourceNativeProjectionLaw.outcomeAt
    have classify_eq :
        (boundaryFinalProjectionLaw initial).classify
            (BoundaryFinalProjection.positiveRow output coordinate threshold)
            occurrence =
          (boundaryPositiveRowClosureLaw initial output coordinate threshold
            ).toProjectionLaw.classify PUnit.unit occurrence := rfl
    rw [classify_eq]
    generalize
      (boundaryPositiveRowClosureLaw initial output coordinate threshold
        ).toProjectionLaw.classify PUnit.unit occurrence = classified
    cases classified <;> rfl

/-- Every positive-outflux effect coordinate is likewise a restriction of the
same final boundary source, not a sibling source assembled after emission. -/
def boundaryPositiveOutfluxInstallation
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (threshold : Real) :
    SourceNativeProjectionLaw.InstallationAt
      (boundaryPositiveOutfluxClosureLaw initial modes threshold).toProjectionLaw
      (boundaryFinalProjectionLaw initial) where
  embed := fun _ => BoundaryFinalProjection.positiveOutflux modes threshold
  embed_injective := by
    intro left right _
    cases left
    cases right
    rfl
  outcome_heq := by
    intro current occurrence projection
    cases projection
    unfold SourceNativeProjectionLaw.outcomeAt
    have classify_eq :
        (boundaryFinalProjectionLaw initial).classify
            (BoundaryFinalProjection.positiveOutflux modes threshold)
            occurrence =
          (boundaryPositiveOutfluxClosureLaw initial modes threshold
            ).toProjectionLaw.classify PUnit.unit occurrence := rfl
    rw [classify_eq]
    generalize
      (boundaryPositiveOutfluxClosureLaw initial modes threshold
        ).toProjectionLaw.classify PUnit.unit occurrence = classified
    cases classified <;> rfl

/-- The total active/dormant lifecycle is another installed face of the same
original boundary root.  Its inactive payload computes dormant continuation,
paid reactivation, or same-row cut from the canonical compiler image. -/
def boundaryPositiveOutfluxReactivationInstallation
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (threshold : Real) :
    SourceNativeProjectionLaw.InstallationAt
      (boundaryPositiveOutfluxReactivationLaw initial modes threshold
        ).toProjectionLaw
      (boundaryFinalProjectionLaw initial) where
  embed := fun _ =>
    BoundaryFinalProjection.positiveOutfluxLifecycle modes threshold
  embed_injective := by
    intro left right _
    cases left
    cases right
    rfl
  outcome_heq := by
    intro current occurrence projection
    cases projection
    unfold SourceNativeProjectionLaw.outcomeAt
    have classify_eq :
        (boundaryFinalProjectionLaw initial).classify
            (BoundaryFinalProjection.positiveOutfluxLifecycle modes threshold)
            occurrence =
          (boundaryPositiveOutfluxReactivationLaw initial modes threshold
            ).toProjectionLaw.classify PUnit.unit occurrence := rfl
    rw [classify_eq]
    rfl

/-- Same-root recognition of the no-free reactivation face. -/
def boundaryPositiveOutfluxReactivationRecognition
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (threshold : Real) :
    SourceNativeEffectReactivationRecognitionAt
      (boundaryFinalLivingRoot initial) where
  lifecycleLaw :=
    boundaryPositiveOutfluxReactivationLaw initial modes threshold
  installation :=
    boundaryPositiveOutfluxReactivationInstallation initial modes threshold

/-- The cofinal visit of the original physical root.  U8 must reflect a
failure face at this visit; a sibling source with the same emitter is not a
substitute for that registration. -/
private def boundaryOriginalCofinalVisit
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    SourceNativeTemporalVisitAt
      (boundaryFinalAuthoritativeRoot initial).toLedgerRoot :=
  SourceNativeTemporalVisitAt.cofinal (boundaryCofinalVisit initial)

abbrev BoundaryRootFailureFaceAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (obstruction : (BN initial).ObstructionAt .cofinal) :=
  SourceNativeRootExpressibilityFailureFaceAt
    (boundaryFinalAuthoritativeRoot initial)
    (boundaryOriginalCofinalVisit initial)
    (U7 := boundaryU7 initial)
    (boundaryExpressibilityFailure initial obstruction)

abbrev BoundaryRootedActualExpressibilityFailureAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (obstruction : (BN initial).ObstructionAt .cofinal) :=
  RootedActualExpressibilityFailureAt
    (boundaryFinalAuthoritativeRoot initial)
    (boundaryOriginalCofinalVisit initial)
    (boundaryU7 initial)
    (boundaryExpressibilityFailure initial obstruction)

/-- The fixed inquiry compiler selects the failure role at the original root.
The coordinate carries no obstruction value: its payload is derived from the
source decision, so a sibling obstruction cannot be smuggled through the
projection inventory. -/
private def sourceGeneratedBoundaryRootFailureFace
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    BoundaryRootFailureFaceAt initial
      (boundaryObstruction initial elapsedBounded) := by
  let obstruction := boundaryObstruction initial elapsedBounded
  refine
    { lawSurface_eq := rfl
      projection := BoundaryFinalProjection.failure
      active := ?_
      classifier_eq := ?_
      calculus := boundaryU7Calculus initial
      u7Event := (boundaryU7Calculus initial).source.emit obstruction
      u7Event_eq_emit := rfl
      theoryAudit := boundaryCofinalU7TheoryAudit initial obstruction
      support_eq := rfl
      rootEntry := boundaryCofinalEntry initial
      rootEntryAtFailure_eq := ?_
      rootDispositionCommutes := ?_
      project_heq := ?_ }
  · change boundaryFinalProjectionActiveAt initial
      BoundaryFinalProjection.failure (boundaryEmitted initial .cofinal)
    exact ⟨rfl, elapsedBounded⟩
  · change (boundaryFinalProjectionLaw initial).classify
      BoundaryFinalProjection.failure (boundaryEmitted initial .cofinal) = .inl _
    simp [boundaryFinalProjectionLaw, BoundaryFinalProjection.failure,
      elapsedBounded]
    congr
  · exact (boundaryOpenResponsibility_subsingleton initial .cofinal).elim _ _
  · unfold U7DemandEntryRootDispositionCommutesAt
    constructor
    · exact heq_of_eq
        ((boundaryOpenResponsibility_subsingleton initial .cofinal).elim _ _)
    · change HEq (LedgerEntryDispositionAt.evolved _)
        (LedgerEntryDispositionAt.evolved _)
      let receipt := sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial
      let selected :=
        ((boundaryCofinalPatch initial receipt).canonicalGeneratedSourceRow?
          (boundaryCofinalEntry initial)).get (by rfl)
      let u7Event := (boundaryU7Calculus initial).source.emit obstruction
      let u7Entry := U7ActualSuccessorSource.demandEntry u7Event
      have source_eq : boundaryCofinalEntry initial = u7Entry :=
        (boundaryOpenResponsibility_subsingleton initial .cofinal).elim _ _
      have target_eq : selected.targetEntry = u7Entry :=
        (boundaryOpenResponsibility_subsingleton initial .cofinal).elim _ _
      have selected_heq : HEq selected.row.evolution
          (LedgerEntryEvolutionAt.carried
            (N := BN initial)
            (source := u7Entry)
            (target := u7Entry)
            rfl HEq.rfl) := by
        cases source_eq
        cases target_eq
        rfl
      have root_heq := selected.evolution_heq_fold.symm.trans selected_heq
      cases root_heq
      rfl
  · exact HEq.rfl

private def boundaryOriginalCofinalEvolution
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    SourceNativeTemporalVisitGeneratedEvolutionAt
      (boundaryFinalAuthoritativeRoot initial).toLedgerRoot
      (boundaryOriginalCofinalVisit initial) :=
  (boundaryFinalAuthoritativeRoot initial).toLedgerRoot
    |>.generatedAtTemporalVisit (boundaryOriginalCofinalVisit initial)

private def boundaryOriginalCofinalEntryRow
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    (boundaryOriginalCofinalEvolution initial).GeneratedEntryRowAt
      (boundaryCofinalEntry initial) :=
  ((boundaryOriginalCofinalEvolution initial).canonicalGeneratedEntryRow?
    (boundaryCofinalEntry initial)).get (by rfl)

private def boundaryOriginalCofinalEntryAuthority
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    SourceNativeAuthoritativeTemporalCausalEntryAuthorityAt
      (boundaryFinalAuthoritativeRoot initial)
      (boundaryOriginalCofinalVisit initial)
      (boundaryCofinalEntry initial) :=
  SourceNativeAuthoritativeTemporalCausalEntryAuthorityAt.generatedFromCofinalRow
    (boundaryFinalAuthoritativeRoot initial)
    (boundaryCofinalVisit initial)
    (boundaryCofinalEntry initial)
    (boundaryOriginalCofinalEntryRow initial)

private def boundaryOriginalLivingCofinalEntryAuthority
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt
      (boundaryFinalLivingRoot initial)
      (boundaryOriginalCofinalVisit initial)
      (boundaryCofinalEntry initial) :=
  SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromCofinalRow
    (boundaryFinalLivingRoot initial)
    (boundaryCofinalVisit initial)
    (boundaryCofinalEntry initial)
    (boundaryOriginalCofinalEntryRow initial)

private def boundaryRootFailureFaceAuthority
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {obstruction : (BN initial).ObstructionAt .cofinal}
    (face : BoundaryRootFailureFaceAt initial obstruction) :
    SourceNativeAuthoritativeTemporalCausalEntryAuthorityAt
      (boundaryFinalAuthoritativeRoot initial)
      (boundaryOriginalCofinalVisit initial)
      face.rootEntry := by
  have entry_eq : face.rootEntry = boundaryCofinalEntry initial :=
    (boundaryOpenResponsibility_subsingleton initial _).elim _ _
  rw [entry_eq]
  exact boundaryOriginalCofinalEntryAuthority initial

private def boundaryRootFailureFaceSuccessor
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {obstruction : (BN initial).ObstructionAt .cofinal}
    (face : BoundaryRootFailureFaceAt initial obstruction) :
    CausalEntrySuccessorAt
      (boundaryFinalAuthoritativeRoot initial).toLedgerRoot
      (boundaryOriginalCofinalVisit initial)
      face.rootEntry :=
  CausalEntrySuccessorAt.ofNonterminal rfl

/-- U8 authority starts only from a failure face already emitted by the
original physical root.  The boundedness theorem and the historical
conditional strong-face readout do not construct this face. -/
private def sourceGeneratedBoundaryRootedFailure
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {obstruction : (BN initial).ObstructionAt .cofinal}
    (face : BoundaryRootFailureFaceAt initial obstruction) :
    BoundaryRootedActualExpressibilityFailureAt initial obstruction :=
  RootedActualExpressibilityFailureAt.ofRootFailureFace face
    (boundaryRootFailureFaceAuthority face)
    (boundaryRootFailureFaceSuccessor face)

/-! A concrete revised root on the canonical minimal coface. -/

private inductive BoundaryRevisedCurrent
  | initial
  | next (radius : Nat)

/-- Forget the U8 coface coordinate while retaining the exact post-cofinal
native current.  The revised initial occurrence is the old radius-zero
occurrence, and every generated successor keeps its original radius. -/
private def restrictBoundaryRevisedCurrent
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    BoundaryRevisedCurrent -> NativeTemporalCurrent initial
  | .initial => .galerkin 0
  | .next radius => .galerkin radius

private def boundaryRevisedVocabulary
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {obstruction : (BN initial).ObstructionAt .cofinal}
    (rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction)
    (coface : GeneratedMinimalCofaceAt
      rooted) :
    ConstructiveRoot.Vocabulary where
  Current := BoundaryRevisedCurrent
  Anchor := coface.worldNetwork.Anchor
  Incidence := coface.worldNetwork.Incidence
  Lineage := coface.worldNetwork.Lineage
  anchorAt := fun _ => coface.worldNetwork.anchorAt coface.cofaceSupport
  incidenceAt := fun _ => coface.worldNetwork.incidenceAt coface.cofaceSupport
  lineageAt := fun _ => coface.worldNetwork.lineageAt coface.cofaceSupport
  NativeWriteAt := fun _ => PUnit
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := by
    intro current _write
    cases current with
    | initial => exact .next 1
    | next radius => exact .next (radius + 1)
  relationTarget := fun write => nomatch write
  continuedTarget := fun write => nomatch write
  redirectTarget := fun write => nomatch write

private inductive BoundaryRevisedEventAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {obstruction : (BN initial).ObstructionAt .cofinal}
    (rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction)
    (coface : GeneratedMinimalCofaceAt
      rooted) :
    BoundaryRevisedCurrent -> coface.worldNetwork.Support -> Type
  | initial (write : NativeTemporalGalerkinWriteAt initial 0) :
      BoundaryRevisedEventAt initial rooted coface .initial coface.cofaceSupport
  | next (radius : Nat) (write : NativeTemporalGalerkinWriteAt initial radius) :
      BoundaryRevisedEventAt initial rooted coface (.next radius)
        coface.cofaceSupport

private def boundaryRevisedEventAlgebra
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {obstruction : (BN initial).ObstructionAt .cofinal}
    (rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction)
    (coface : GeneratedMinimalCofaceAt
      rooted) :
    SourceNativeEventAlgebra coface.worldNetwork
      (boundaryRevisedVocabulary initial rooted coface) where
  EventAt := BoundaryRevisedEventAt initial rooted coface
  compile := fun event => match event with
    | .initial _write => .nativeWrite PUnit.unit
    | .next _radius _write => .nativeWrite PUnit.unit
  AffectedInventoryAt := fun {_current} {support} _ =>
    OpenResponsibilityAt coface.worldNetwork support
  affectedInventoryPresentation := fun _ => ConstructivePresentation.refl _
  anchorKey := id
  incidenceKey := id
  lineageKey := id
  anchor_commutes := by intro current support event; cases event <;> rfl
  incidence_commutes := by intro current support event; cases event <;> rfl
  lineage_commutes := by intro current support event; cases event <;> rfl

private def boundaryRevisedSource
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {obstruction : (BN initial).ObstructionAt .cofinal}
    (rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction)
    (coface : GeneratedMinimalCofaceAt
      rooted) :
    SourceNativeSource coface.worldNetwork
      (boundaryRevisedVocabulary initial rooted coface) where
  initial := .initial
  law := boundaryRevisedEventAlgebra initial rooted coface

private def boundaryRevisedEmitted
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {obstruction : (BN initial).ObstructionAt .cofinal}
    (rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction)
    (coface : GeneratedMinimalCofaceAt
      rooted) :
    (current : BoundaryRevisedCurrent) ->
      (boundaryRevisedSource initial rooted coface).toRootSource.actual.OccurrenceAt
        current
  | .initial => ⟨coface.cofaceSupport, .initial
      (sourceGeneratedNativeTemporalGalerkinWrite initial 0)⟩
  | .next radius => ⟨coface.cofaceSupport, .next radius
      (sourceGeneratedNativeTemporalGalerkinWrite initial radius)⟩

/-- Occurrence component of the faithful restriction from the revised root
to the original post-cofinal native root.  It preserves the literal source
write; no replacement event is selected by the caller. -/
private def restrictBoundaryRevisedOccurrence
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {obstruction : (BN initial).ObstructionAt .cofinal}
    (rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction)
    (coface : GeneratedMinimalCofaceAt
      rooted)
    {current : BoundaryRevisedCurrent}
    (occurrence :
      (boundaryRevisedSource initial rooted coface).toRootSource.actual.OccurrenceAt
        current) :
    (nativeTemporalSource initial).toRootSource.actual.OccurrenceAt
      (restrictBoundaryRevisedCurrent initial current) := by
  rcases occurrence with ⟨support, event⟩
  change BoundaryRevisedEventAt initial rooted coface current support at event
  cases event with
  | initial write => exact ⟨.cofinal, .galerkin 0 write⟩
  | next radius write => exact ⟨.cofinal, .galerkin radius write⟩

private def boundaryRevisedOldEntry
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {obstruction : (BN initial).ObstructionAt .cofinal}
    (rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction)
    (coface : GeneratedMinimalCofaceAt
      rooted) :
    OpenResponsibilityAt coface.worldNetwork coface.cofaceSupport :=
  coface.cofaceLedgerRetract.forward
    rooted.targetEntry

private def boundaryRevisedNewEntry
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {obstruction : (BN initial).ObstructionAt .cofinal}
    (rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction)
    (coface : GeneratedMinimalCofaceAt
      rooted) :
    OpenResponsibilityAt coface.worldNetwork coface.cofaceSupport :=
  coface.obstructionEntry

private theorem boundaryRevisedEntry_eq_of_responsibility_eq
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {obstruction : (BN initial).ObstructionAt .cofinal}
    (rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction)
    (coface : GeneratedMinimalCofaceAt rooted)
    (left right : OpenResponsibilityAt
      coface.worldNetwork coface.cofaceSupport)
    (responsibility_eq : left.1 = right.1) : left = right := by
  rcases left with ⟨leftResponsibility, leftOpen⟩
  rcases right with ⟨rightResponsibility, rightOpen⟩
  dsimp only at responsibility_eq
  cases responsibility_eq
  cases leftResponsibility with
  | inl oldResponsibility =>
      have open_eq : leftOpen = rightOpen :=
        (boundaryOpenAt_subsingleton initial _ oldResponsibility).elim _ _
      cases open_eq
      rfl
  | inr direction =>
      cases direction
      cases leftOpen
      cases rightOpen
      rfl

private theorem boundaryRevisedEntry_eq_old_or_new
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {obstruction : (BN initial).ObstructionAt .cofinal}
    (rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction)
    (coface : GeneratedMinimalCofaceAt
      rooted)
    (entry : OpenResponsibilityAt coface.worldNetwork coface.cofaceSupport) :
    entry = boundaryRevisedOldEntry initial rooted coface ∨
      entry = boundaryRevisedNewEntry initial rooted coface := by
  rcases entry with ⟨responsibility, isOpen⟩
  cases responsibility with
  | inl oldResponsibility =>
      left
      have oldEntryEq :
          (⟨oldResponsibility, isOpen⟩ : OpenResponsibilityAt (BN initial)
            ((boundaryFinalAuthoritativeRoot initial).toRoot.supportAt
              rooted.oldSuccessor.next)) =
            rooted.targetEntry :=
        (boundaryOpenResponsibility_subsingleton initial _).elim _ _
      exact congrArg coface.cofaceLedgerRetract.forward oldEntryEq
  | inr generatedResponsibility =>
      right
      cases generatedResponsibility
      cases isOpen
      rfl

private structure BoundaryRevisedExactTransitionAt
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {obstruction : (BN initial).ObstructionAt .cofinal}
    {rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction}
    {coface : GeneratedMinimalCofaceAt
      rooted}
    (source target : coface.worldNetwork.Support) : Type where
  support_eq : source = target

private inductive BoundaryRevisedRowEventAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {obstruction : (BN initial).ObstructionAt .cofinal}
    (rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction)
    (coface : GeneratedMinimalCofaceAt
      rooted) :
    {current : BoundaryRevisedCurrent} ->
    (occurrence : (boundaryRevisedSource initial rooted coface).toRootSource.actual.OccurrenceAt current) ->
    {targetSupport : coface.worldNetwork.Support} ->
    (sourceEntry : OpenResponsibilityAt coface.worldNetwork
      ((boundaryRevisedSource initial rooted coface).toRootSource.account.supportOf
        occurrence)) ->
    (targetEntry : OpenResponsibilityAt coface.worldNetwork targetSupport) -> Type
  | initialOld (write : NativeTemporalGalerkinWriteAt initial 0) :
      BoundaryRevisedRowEventAt initial rooted coface
      ⟨coface.cofaceSupport, .initial write⟩
      (boundaryRevisedOldEntry initial rooted coface)
      (boundaryRevisedOldEntry initial rooted coface)
  | initialNew (write : NativeTemporalGalerkinWriteAt initial 0) :
      BoundaryRevisedRowEventAt initial rooted coface
      ⟨coface.cofaceSupport, .initial write⟩
      (boundaryRevisedNewEntry initial rooted coface)
      (boundaryRevisedNewEntry initial rooted coface)
  | nextOld (radius : Nat)
      (write : NativeTemporalGalerkinWriteAt initial radius) :
      BoundaryRevisedRowEventAt initial rooted coface
      ⟨coface.cofaceSupport, .next radius write⟩
      (boundaryRevisedOldEntry initial rooted coface)
      (boundaryRevisedOldEntry initial rooted coface)
  | nextNew (radius : Nat)
      (write : NativeTemporalGalerkinWriteAt initial radius) :
      BoundaryRevisedRowEventAt initial rooted coface
      ⟨coface.cofaceSupport, .next radius write⟩
      (boundaryRevisedNewEntry initial rooted coface)
      (boundaryRevisedNewEntry initial rooted coface)

private def boundaryRevisedWriteRowSource
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {obstruction : (BN initial).ObstructionAt .cofinal}
    (rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction)
    (coface : GeneratedMinimalCofaceAt
      rooted) :
    LedgerWriteRowSourceAt (boundaryRevisedSource initial rooted coface) (by
      intro _ occurrence targetSupport _ _
      exact BoundaryRevisedExactTransitionAt occurrence.1 targetSupport) :=
  { IncidenceOccurrenceAt := BoundaryRevisedRowEventAt initial rooted coface
    compileEvolution := fun event => by
      cases event <;> exact .carried rfl HEq.rfl
    compileExact := fun event => by
      cases event <;> exact ⟨rfl⟩ }

private def boundaryRevisedFinZero : Fin 2 :=
  ⟨0, Nat.zero_lt_succ 1⟩

private def boundaryRevisedFinOne : Fin 2 :=
  ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 0)⟩

private def boundaryRevisedRowsInitial
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {obstruction : (BN initial).ObstructionAt .cofinal}
    (rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction)
    (coface : GeneratedMinimalCofaceAt
      rooted)
    (write : NativeTemporalGalerkinWriteAt initial 0) :
    FiniteGeneratedLedgerWriteRowsAt
      (boundaryRevisedWriteRowSource initial rooted coface)
      ⟨coface.cofaceSupport, .initial write⟩
      ⟨coface.cofaceSupport⟩ where
  size := 2
  sourceEntryAt := Fin.cases
    (boundaryRevisedOldEntry initial rooted coface)
    (fun _ => boundaryRevisedNewEntry initial rooted coface)
  targetEntryAt := Fin.cases
    (boundaryRevisedOldEntry initial rooted coface)
    (fun _ => boundaryRevisedNewEntry initial rooted coface)
  rowAt := Fin.cases
    ((boundaryRevisedWriteRowSource initial rooted coface).generate
      (.initialOld write))
    (fun _ =>
      (boundaryRevisedWriteRowSource initial rooted coface).generate
        (.initialNew write))

private def boundaryRevisedRowsNext
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {obstruction : (BN initial).ObstructionAt .cofinal}
    (rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction)
    (coface : GeneratedMinimalCofaceAt
      rooted)
    (radius : Nat)
    (write : NativeTemporalGalerkinWriteAt initial radius) :
    FiniteGeneratedLedgerWriteRowsAt
      (boundaryRevisedWriteRowSource initial rooted coface)
      ⟨coface.cofaceSupport, .next radius write⟩
      ⟨coface.cofaceSupport⟩ where
  size := 2
  sourceEntryAt := Fin.cases
    (boundaryRevisedOldEntry initial rooted coface)
    (fun _ => boundaryRevisedNewEntry initial rooted coface)
  targetEntryAt := Fin.cases
    (boundaryRevisedOldEntry initial rooted coface)
    (fun _ => boundaryRevisedNewEntry initial rooted coface)
  rowAt := Fin.cases
    ((boundaryRevisedWriteRowSource initial rooted coface).generate
      (.nextOld radius write))
    (fun _ =>
      (boundaryRevisedWriteRowSource initial rooted coface).generate
        (.nextNew radius write))

private def boundaryRevisedEntryIndex
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {obstruction : (BN initial).ObstructionAt .cofinal}
    (rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction)
    (coface : GeneratedMinimalCofaceAt
      rooted)
    (entry : OpenResponsibilityAt coface.worldNetwork coface.cofaceSupport) :
    { index : Fin 2 //
      Fin.cases
        (boundaryRevisedOldEntry initial rooted coface)
        (fun _ => boundaryRevisedNewEntry initial rooted coface) index = entry } := by
  rcases entry with ⟨responsibility, isOpen⟩
  cases responsibility with
  | inl oldResponsibility =>
      refine ⟨boundaryRevisedFinZero, ?_⟩
      have oldEntryEq :
          (⟨oldResponsibility, isOpen⟩ : OpenResponsibilityAt (BN initial)
            ((boundaryFinalAuthoritativeRoot initial).toRoot.supportAt
              rooted.oldSuccessor.next)) =
            rooted.targetEntry :=
        (boundaryOpenResponsibility_subsingleton initial _).elim _ _
      exact (congrArg coface.cofaceLedgerRetract.forward oldEntryEq).symm
  | inr generatedResponsibility =>
      cases generatedResponsibility
      refine ⟨boundaryRevisedFinOne, ?_⟩
      cases isOpen
      rfl

private def boundaryRevisedCoverageInitial
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {obstruction : (BN initial).ObstructionAt .cofinal}
    (rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction)
    (coface : GeneratedMinimalCofaceAt
      rooted)
    (write : NativeTemporalGalerkinWriteAt initial 0) :
    LedgerIdentityRemainderCoverageAt
      (boundaryRevisedRowsInitial initial rooted coface write) where
  destinationIndex := fun entry =>
    some (boundaryRevisedEntryIndex initial rooted coface entry)
  originIndex := fun entry =>
    some (boundaryRevisedEntryIndex initial rooted coface entry)

private def boundaryRevisedCoverageNext
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {obstruction : (BN initial).ObstructionAt .cofinal}
    (rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction)
    (coface : GeneratedMinimalCofaceAt
      rooted)
    (radius : Nat)
    (write : NativeTemporalGalerkinWriteAt initial radius) :
    LedgerIdentityRemainderCoverageAt
      (boundaryRevisedRowsNext initial rooted coface radius write) where
  destinationIndex := fun entry =>
    some (boundaryRevisedEntryIndex initial rooted coface entry)
  originIndex := fun entry =>
    some (boundaryRevisedEntryIndex initial rooted coface entry)

private def boundaryRevisedPatchInitial
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {obstruction : (BN initial).ObstructionAt .cofinal}
    (rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction)
    (coface : GeneratedMinimalCofaceAt
      rooted)
    (write : NativeTemporalGalerkinWriteAt initial 0) :
    FiniteGeneratedLedgerWritePatchAt
      (boundaryRevisedWriteRowSource initial rooted coface)
      ⟨coface.cofaceSupport, .initial write⟩
      ⟨coface.cofaceSupport⟩ :=
  .identityRemainder
    (boundaryRevisedRowsInitial initial rooted coface write)
    (boundaryRevisedCoverageInitial initial rooted coface write)

private def boundaryRevisedPatchNext
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {obstruction : (BN initial).ObstructionAt .cofinal}
    (rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction)
    (coface : GeneratedMinimalCofaceAt
      rooted)
    (radius : Nat)
    (write : NativeTemporalGalerkinWriteAt initial radius) :
    FiniteGeneratedLedgerWritePatchAt
      (boundaryRevisedWriteRowSource initial rooted coface)
      ⟨coface.cofaceSupport, .next radius write⟩
      ⟨coface.cofaceSupport⟩ :=
  .identityRemainder
    (boundaryRevisedRowsNext initial rooted coface radius write)
    (boundaryRevisedCoverageNext initial rooted coface radius write)

private theorem boundaryRevisedPatchInitial_destination_eq
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {obstruction : (BN initial).ObstructionAt .cofinal}
    (rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction)
    (coface : GeneratedMinimalCofaceAt
      rooted)
    (write : NativeTemporalGalerkinWriteAt initial 0)
    (entry : OpenResponsibilityAt coface.worldNetwork coface.cofaceSupport) :
    (((boundaryRevisedPatchInitial initial rooted coface write).toLedgerWriteEvolution
      ).destination entry).1 = entry := by
  rcases boundaryRevisedEntry_eq_old_or_new initial rooted coface entry with
    oldEq | newEq
  · subst entry
    apply boundaryRevisedEntry_eq_of_responsibility_eq initial rooted coface
    rfl
  · subst entry
    apply boundaryRevisedEntry_eq_of_responsibility_eq initial rooted coface
    rfl

private theorem boundaryRevisedPatchNext_destination_eq
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {obstruction : (BN initial).ObstructionAt .cofinal}
    (rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction)
    (coface : GeneratedMinimalCofaceAt
      rooted)
    (radius : Nat)
    (write : NativeTemporalGalerkinWriteAt initial radius)
    (entry : OpenResponsibilityAt coface.worldNetwork coface.cofaceSupport) :
    (((boundaryRevisedPatchNext initial rooted coface radius write).toLedgerWriteEvolution
      ).destination entry).1 = entry := by
  rcases boundaryRevisedEntry_eq_old_or_new initial rooted coface entry with
    oldEq | newEq
  · subst entry
    apply boundaryRevisedEntry_eq_of_responsibility_eq initial rooted coface
    rfl
  · subst entry
    apply boundaryRevisedEntry_eq_of_responsibility_eq initial rooted coface
    rfl

private theorem boundaryRevisedPatchInitial_origin_eq
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {obstruction : (BN initial).ObstructionAt .cofinal}
    (rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction)
    (coface : GeneratedMinimalCofaceAt
      rooted)
    (write : NativeTemporalGalerkinWriteAt initial 0)
    (entry : OpenResponsibilityAt coface.worldNetwork coface.cofaceSupport) :
    (((boundaryRevisedPatchInitial initial rooted coface write).toLedgerWriteEvolution
      ).origin entry).1 = entry := by
  rcases boundaryRevisedEntry_eq_old_or_new initial rooted coface entry with
    oldEq | newEq
  · subst entry
    apply boundaryRevisedEntry_eq_of_responsibility_eq initial rooted coface
    rfl
  · subst entry
    apply boundaryRevisedEntry_eq_of_responsibility_eq initial rooted coface
    rfl

private theorem boundaryRevisedPatchNext_origin_eq
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {obstruction : (BN initial).ObstructionAt .cofinal}
    (rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction)
    (coface : GeneratedMinimalCofaceAt
      rooted)
    (radius : Nat)
    (write : NativeTemporalGalerkinWriteAt initial radius)
    (entry : OpenResponsibilityAt coface.worldNetwork coface.cofaceSupport) :
    (((boundaryRevisedPatchNext initial rooted coface radius write).toLedgerWriteEvolution
      ).origin entry).1 = entry := by
  rcases boundaryRevisedEntry_eq_old_or_new initial rooted coface entry with
    oldEq | newEq
  · subst entry
    apply boundaryRevisedEntry_eq_of_responsibility_eq initial rooted coface
    rfl
  · subst entry
    apply boundaryRevisedEntry_eq_of_responsibility_eq initial rooted coface
    rfl

private def boundaryRevisedTerminalRowSource
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {obstruction : (BN initial).ObstructionAt .cofinal}
    (rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction)
    (coface : GeneratedMinimalCofaceAt
      rooted) :
    LedgerTerminalRowSourceAt (boundaryRevisedSource initial rooted coface) :=
  LedgerTerminalRowSourceAt.empty _

private def boundaryRevisedGeneratedLedgerEvolution
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {obstruction : (BN initial).ObstructionAt .cofinal}
    (rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction)
    (coface : GeneratedMinimalCofaceAt
      rooted)
    {current : BoundaryRevisedCurrent}
    (occurrence : (boundaryRevisedSource initial rooted coface).toRootSource.actual.OccurrenceAt
      current) :
    SourceNativeLedgerEvolutionAt
      (boundaryRevisedSource initial rooted coface) occurrence := by
  rcases occurrence with ⟨support, event⟩
  change BoundaryRevisedEventAt initial rooted coface current support at event
  cases event with
  | initial write =>
      exact .nativeWrite PUnit.unit rfl
        (boundaryRevisedEmitted initial rooted coface (.next 1))
        (boundaryRevisedPatchInitial initial rooted coface write
          ).toLedgerWriteEvolution
  | next radius write =>
      exact .nativeWrite PUnit.unit rfl
        (boundaryRevisedEmitted initial rooted coface (.next (radius + 1)))
        (boundaryRevisedPatchNext initial rooted coface radius write
          ).toLedgerWriteEvolution

private def boundaryRevisedLedgerCompiler
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {obstruction : (BN initial).ObstructionAt .cofinal}
    (rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction)
    (coface : GeneratedMinimalCofaceAt
      rooted) :
    SourceNativeLedgerCompiler (boundaryRevisedSource initial rooted coface) where
  IncidenceTransitionAt := fun _ sourceIncidence targetIncidence =>
    PUnit
  ExactTransitionAt := by
    intro _ occurrence targetSupport _ _
    exact BoundaryRevisedExactTransitionAt occurrence.1 targetSupport
  exact_incidence := by
    intro _ _ _ _ _ _
    exact PUnit.unit
  exact_lineage := by
    intro _ _ _ _ _ exact
    cases exact.support_eq
    rfl
  writeRowSource := boundaryRevisedWriteRowSource initial rooted coface
  terminalRowSource := boundaryRevisedTerminalRowSource initial rooted coface
  compile := boundaryRevisedGeneratedLedgerEvolution initial rooted coface
  compilePatch := by
    intro current occurrence
    rcases occurrence with ⟨support, event⟩
    change BoundaryRevisedEventAt initial rooted coface current support at event
    cases event with
    | initial write =>
        exact ⟨boundaryRevisedPatchInitial initial rooted coface write, rfl⟩
    | next radius write =>
        exact
          ⟨boundaryRevisedPatchNext initial rooted coface radius write, rfl⟩

private def boundaryRevisedLedgerSource
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {obstruction : (BN initial).ObstructionAt .cofinal}
    (rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction)
    (coface : GeneratedMinimalCofaceAt
      rooted) :
    SourceNativeLedgerSource coface.worldNetwork
      (boundaryRevisedVocabulary initial rooted coface) where
  source := boundaryRevisedSource initial rooted coface
  ledgerCompiler := boundaryRevisedLedgerCompiler initial rooted coface

private def boundaryRevisedRoot
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {obstruction : (BN initial).ObstructionAt .cofinal}
    (rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction)
    (coface : GeneratedMinimalCofaceAt
      rooted) :
    SourceNativeLedgerRootClosure coface.worldNetwork
      (boundaryRevisedVocabulary initial rooted coface) where
  source := boundaryRevisedLedgerSource initial rooted coface
  emitted := boundaryRevisedEmitted initial rooted coface
  compiler_commutes := by intro current; cases current <;> rfl

private theorem boundaryRevisedOpenAt_subsingleton
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {obstruction : (BN initial).ObstructionAt .cofinal}
    (rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction)
    (coface : GeneratedMinimalCofaceAt
      rooted)
    (support : coface.worldNetwork.Support)
    (responsibility : coface.worldNetwork.Responsibility) :
    Subsingleton (coface.worldNetwork.OpenAt support responsibility) := by
  constructor
  intro left right
  cases support with
  | inl oldSupport =>
      cases responsibility with
      | inl oldResponsibility =>
          exact (boundaryOpenAt_subsingleton initial _ _).elim left right
      | inr generatedResponsibility => exact PEmpty.elim left
  | inr generatedSupport =>
      cases responsibility with
      | inl oldResponsibility =>
          exact (boundaryOpenAt_subsingleton initial _ _).elim left right
      | inr generatedResponsibility =>
          cases left
          cases right
          rfl

private def boundaryRevisedRestructuringLaw
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {obstruction : (BN initial).ObstructionAt .cofinal}
    (rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction)
    (coface : GeneratedMinimalCofaceAt
      rooted) :
    SourceNativeLedgerRestructuringLaw
      (boundaryRevisedSource initial rooted coface) :=
  identityOnlyWorldLedgerRestructuringLaw
    (boundaryRevisedSource initial rooted coface)
    (coface.worldNetwork.anchorAt coface.cofaceSupport)
    (boundaryRevisedOpenAt_subsingleton initial rooted coface)

private def boundaryRevisedRestructuringCertification
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {obstruction : (BN initial).ObstructionAt .cofinal}
    (rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction)
    (coface : GeneratedMinimalCofaceAt
      rooted)
    {current : BoundaryRevisedCurrent}
    (occurrence : (boundaryRevisedSource initial rooted coface).toRootSource.actual.OccurrenceAt
      current) :
    SourceNativeLedgerRestructuringCertificationAt
      (boundaryRevisedRestructuringLaw initial rooted coface)
      ((boundaryRevisedLedgerCompiler initial rooted coface).compile occurrence) := by
  rcases occurrence with ⟨support, event⟩
  change BoundaryRevisedEventAt initial rooted coface current support at event
  cases event with
  | initial write =>
      exact ExactLedgerRestructuringCertificationAt.ofInjective
        (fun left right equality => by
          exact (boundaryRevisedPatchInitial_origin_eq
            initial rooted coface write left).symm.trans
              (equality.trans (boundaryRevisedPatchInitial_origin_eq
                initial rooted coface write right)))
        (fun left right equality => by
          exact (boundaryRevisedPatchInitial_destination_eq
            initial rooted coface write left).symm.trans
              (equality.trans (boundaryRevisedPatchInitial_destination_eq
                initial rooted coface write right)))
  | next radius write =>
      exact ExactLedgerRestructuringCertificationAt.ofInjective
        (fun left right equality => by
          exact (boundaryRevisedPatchNext_origin_eq
            initial rooted coface radius write left).symm.trans
              (equality.trans (boundaryRevisedPatchNext_origin_eq
                initial rooted coface radius write right)))
        (fun left right equality => by
          exact (boundaryRevisedPatchNext_destination_eq
            initial rooted coface radius write left).symm.trans
              (equality.trans (boundaryRevisedPatchNext_destination_eq
                initial rooted coface radius write right)))

private def boundaryRevisedRestructuringCompiler
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {obstruction : (BN initial).ObstructionAt .cofinal}
    (rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction)
    (coface : GeneratedMinimalCofaceAt
      rooted) :
    SourceNativeRestructuringLedgerCompiler
      (boundaryRevisedSource initial rooted coface) where
  ledgerCompiler := boundaryRevisedLedgerCompiler initial rooted coface
  restructuringLaw := boundaryRevisedRestructuringLaw initial rooted coface
  certifyRestructuring :=
    boundaryRevisedRestructuringCertification initial rooted coface

private def boundaryRevisedRestructuringSource
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {obstruction : (BN initial).ObstructionAt .cofinal}
    (rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction)
    (coface : GeneratedMinimalCofaceAt
      rooted) :
    SourceNativeRestructuringLedgerSource coface.worldNetwork
      (boundaryRevisedVocabulary initial rooted coface) where
  source := boundaryRevisedSource initial rooted coface
  compiler := boundaryRevisedRestructuringCompiler initial rooted coface

private def BoundaryGalerkinPhysicalEquationAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (radius : Nat)
    (write : NativeTemporalGalerkinWriteAt initial radius) : Prop :=
  ∀ time ∈ Set.Icc (0 : Real) 1,
    HasDerivAt write.trajectory
        (finiteStateVorticityGenerator
          (wholeRestartModes radius) nu.coeff (write.trajectory time)) time ∧
      (∀ wave, wave ∉ wholeRestartModes radius ->
        write.trajectory time wave = 0) ∧
      (∀ wave, dotProduct (complexWavevector wave)
        (write.trajectory time wave) = 0) ∧
      FiniteStateFourierReality (write.trajectory time)

/-- Domain stage carried by one source-generated revised occurrence.  The
revised native write itself is only `PUnit`; the actual Galerkin trajectory
remains in the occurrence event and is recovered by dependent elimination. -/
private def BoundaryRevisedGalerkinStageAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    BoundaryRevisedCurrent -> Type
  | .initial => NativeTemporalGalerkinWriteAt initial 0
  | .next radius => NativeTemporalGalerkinWriteAt initial radius

private def boundaryRevisedGeneratedGalerkinStageAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {obstruction : (BN initial).ObstructionAt .cofinal}
    (rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction)
    (coface : GeneratedMinimalCofaceAt rooted)
    {current : BoundaryRevisedCurrent}
    (occurrence :
      (boundaryRevisedSource initial rooted coface).toRootSource.actual.OccurrenceAt
        current) :
    BoundaryRevisedGalerkinStageAt initial current := by
  rcases occurrence with ⟨support, event⟩
  change BoundaryRevisedEventAt initial rooted coface current support at event
  cases event with
  | initial write => exact write
  | next _radius write => exact write

private def BoundaryRevisedGalerkinPhysicalEquationAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (current : BoundaryRevisedCurrent)
    (stage : BoundaryRevisedGalerkinStageAt initial current) : Prop :=
  match current with
  | .initial => BoundaryGalerkinPhysicalEquationAt initial 0 stage
  | .next radius => BoundaryGalerkinPhysicalEquationAt initial radius stage

/-- The Galerkin equation is a dependent face of the exact revised source
occurrence.  It is not a U8 normal form or attaching payload. -/
private def BoundaryGeneratedPhysicalEquationFaceAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {obstruction : (BN initial).ObstructionAt .cofinal}
    (rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction)
    (coface : GeneratedMinimalCofaceAt rooted)
    {current : (boundaryRevisedVocabulary initial rooted coface).Current}
    (occurrence :
      (boundaryRevisedLedgerSource initial rooted coface).source.toRootSource.actual.OccurrenceAt
        current) : Type :=
  PLift <| BoundaryRevisedGalerkinPhysicalEquationAt initial current
    (boundaryRevisedGeneratedGalerkinStageAt initial rooted coface occurrence)

/-- The dependent equation face is read directly from the same source event. -/
private def boundaryGeneratedPhysicalEquationFace
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {obstruction : (BN initial).ObstructionAt .cofinal}
    (rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction)
    (coface : GeneratedMinimalCofaceAt rooted)
    {current : (boundaryRevisedVocabulary initial rooted coface).Current}
    (occurrence :
      (boundaryRevisedLedgerSource initial rooted coface).source.toRootSource.actual.OccurrenceAt
        current) :
    BoundaryGeneratedPhysicalEquationFaceAt initial rooted coface
      occurrence := by
  rcases occurrence with ⟨support, event⟩
  change BoundaryRevisedEventAt initial rooted coface current support at event
  cases event with
  | initial write => exact ⟨write.physical⟩
  | next _radius write => exact ⟨write.physical⟩

/-- The same exact occurrence generates its ledger successor; no target is a
physical-face field. -/
private def boundaryRevisedGeneratedSuccessorAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {obstruction : (BN initial).ObstructionAt .cofinal}
    (rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction)
    (coface : GeneratedMinimalCofaceAt rooted)
    {current : (boundaryRevisedVocabulary initial rooted coface).Current}
    (occurrence :
      (boundaryRevisedLedgerSource initial rooted coface).source.toRootSource.actual.OccurrenceAt
        current) :
    SourceNativeLedgerGeneratedSuccessorAt occurrence
      ((boundaryRevisedLedgerSource initial rooted coface).ledgerCompiler.compile occurrence) := by
  rcases occurrence with ⟨support, event⟩
  change BoundaryRevisedEventAt initial rooted coface current support at event
  cases event <;> exact PUnit.unit

/-- Zero-information consumer seal for the physical equation read from the
same revised occurrence.  The equation face and generated successor are
indices, so the seal cannot consume a sibling equation or select another
next current. -/
private inductive BoundaryGeneratedPhysicalEquationConsumerAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {obstruction : (BN initial).ObstructionAt .cofinal}
    (rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction)
    (coface : GeneratedMinimalCofaceAt rooted)
    {current : (boundaryRevisedVocabulary initial rooted coface).Current}
    (occurrence :
      (boundaryRevisedLedgerSource initial rooted coface).source.toRootSource.actual.OccurrenceAt
        current)
    (_equation : BoundaryGeneratedPhysicalEquationFaceAt initial rooted coface
      occurrence)
    (_next : SourceNativeLedgerGeneratedSuccessorAt occurrence
      ((boundaryRevisedLedgerSource initial rooted coface).ledgerCompiler.compile occurrence)) :
    Type
  | canonical

private inductive BoundaryRevisedProjection
  | ledger
  | physicalEquation
  | physicalConsumer

private def boundaryRevisedProjectionLaw
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {obstruction : (BN initial).ObstructionAt .cofinal}
    (rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction)
    (coface : GeneratedMinimalCofaceAt
      rooted) :
    SourceNativeProjectionLaw
      (boundaryRevisedRestructuringSource initial rooted coface).toLedgerSource where
  Projection := BoundaryRevisedProjection
  ActiveAt := fun projection {_current} _occurrence =>
    match projection with
    | .ledger => PUnit
    | .physicalEquation => PUnit
    | .physicalConsumer => PUnit
  InactiveAt := fun projection {_current} _occurrence =>
    match projection with
    | .ledger => PEmpty
    | .physicalEquation => PEmpty
    | .physicalConsumer => PEmpty
  classify := fun projection {_current} _occurrence =>
    match projection with
    | .ledger => .inl PUnit.unit
    | .physicalEquation => .inl PUnit.unit
    | .physicalConsumer => .inl PUnit.unit
  PayloadAt := fun projection {_current} occurrence _ =>
    match projection with
    | .ledger => SourceNativeLedgerEvolutionAt
        (boundaryRevisedSource initial rooted coface) occurrence
    | .physicalEquation =>
        BoundaryGeneratedPhysicalEquationFaceAt initial rooted coface
          occurrence
    | .physicalConsumer =>
        let equation := boundaryGeneratedPhysicalEquationFace initial rooted coface
          occurrence
        BoundaryGeneratedPhysicalEquationConsumerAt initial rooted coface
          occurrence equation
            (boundaryRevisedGeneratedSuccessorAt initial rooted coface occurrence)
  project := fun projection {_current} occurrence _ => by
    cases projection with
    | ledger =>
        exact (boundaryRevisedLedgerCompiler initial rooted coface).compile occurrence
    | physicalEquation =>
        exact boundaryGeneratedPhysicalEquationFace initial rooted coface
          occurrence
    | physicalConsumer => exact .canonical

private def boundaryRevisedAuthoritySource
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {obstruction : (BN initial).ObstructionAt .cofinal}
    (rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction)
    (coface : GeneratedMinimalCofaceAt
      rooted) :
    SourceNativeAuthoritySource coface.worldNetwork
      (boundaryRevisedVocabulary initial rooted coface) where
  restructuringSource := boundaryRevisedRestructuringSource initial rooted coface
  eventInventoryAdmission :=
    .reflOfNoFaithfulTerminal
      (boundaryRevisedRestructuringSource initial rooted coface)
      (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := .rootSemantic coface.worldNetwork
  projectionLaw := boundaryRevisedProjectionLaw initial rooted coface

private def boundaryRevisedAuthoritativeRoot
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {obstruction : (BN initial).ObstructionAt .cofinal}
    (rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction)
    (coface : GeneratedMinimalCofaceAt
      rooted) :
    SourceNativeAuthoritativeRootClosure coface.worldNetwork
      (boundaryRevisedVocabulary initial rooted coface) where
  source := boundaryRevisedAuthoritySource initial rooted coface
  emitted := boundaryRevisedEmitted initial rooted coface
  compiler_commutes := by intro current; cases current <;> rfl

private def boundaryRevisedTerminalHandoff
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {obstruction : (BN initial).ObstructionAt .cofinal}
    (rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction)
    (coface : GeneratedMinimalCofaceAt
      rooted) :
    SourceNativeTerminalHandoffLaw
      (boundaryRevisedAuthoritativeRoot initial rooted coface).source :=
  SourceNativeAuthoritySource.emptyFaithfulTerminalHandoff
    (boundaryRevisedAuthoritativeRoot initial rooted coface).source
    (fun _ => ⟨fun terminal => nomatch terminal⟩)

/-- The revised source is born as one living root.  Its future handoff law is
part of the same source identity as the first revised write. -/
private def boundaryRevisedLivingRoot
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {obstruction : (BN initial).ObstructionAt .cofinal}
    (rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction)
    (coface : GeneratedMinimalCofaceAt rooted) :
    SourceNativeLivingRootClosure coface.worldNetwork
      (boundaryRevisedVocabulary initial rooted coface) where
  source :=
    { base := (boundaryRevisedAuthoritativeRoot initial rooted coface).source
      terminalHandoff := boundaryRevisedTerminalHandoff initial rooted coface }
  emitted := boundaryRevisedEmitted initial rooted coface
  compiler_commutes := by intro current; cases current <;> rfl

private def boundaryRevisedOccurrencePresentation
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {obstruction : (BN initial).ObstructionAt .cofinal}
    (rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction)
    (coface : GeneratedMinimalCofaceAt
      rooted) :
    ConstructivePresentation
      ((boundaryFinalAuthoritativeRoot initial).toRoot.actual.OccurrenceAt
        (.galerkin 0))
      ((boundaryRevisedAuthoritativeRoot initial rooted coface).toRoot.actual.OccurrenceAt
        .initial) where
  forward := by
    rintro ⟨support, event⟩
    change NativeTemporalRootEventAt initial (.galerkin 0) support at event
    cases event with
    | galerkin radius write =>
        exact ⟨coface.cofaceSupport, .initial write⟩
  backward := by
    rintro ⟨support, event⟩
    change BoundaryRevisedEventAt initial rooted coface .initial support at event
    cases event with
    | initial write => exact ⟨.cofinal, .galerkin 0 write⟩
  backward_forward := by
    rintro ⟨support, event⟩
    change NativeTemporalRootEventAt initial (.galerkin 0) support at event
    cases event
    rfl
  forward_backward := by
    rintro ⟨support, event⟩
    change BoundaryRevisedEventAt initial rooted coface .initial support at event
    cases event
    rfl

private def boundaryRevisedFirstWrite
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {obstruction : (BN initial).ObstructionAt .cofinal}
    (rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction)
    (coface : GeneratedMinimalCofaceAt
      rooted) :
    CanonicalFirstRootWriteAt
      (boundaryRevisedAuthoritativeRoot initial rooted coface).toLedgerRoot :=
  PUnit.unit

private def boundaryRevisedInitialGeneratedEvolution
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {obstruction : (BN initial).ObstructionAt .cofinal}
    (rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction)
    (coface : GeneratedMinimalCofaceAt
      rooted) :
    SourceNativeTemporalVisitGeneratedEvolutionAt
      (boundaryRevisedAuthoritativeRoot initial rooted coface).toLedgerRoot
      (.finite
        (boundaryRevisedAuthoritativeRoot initial rooted coface).toRoot.initialVisit) :=
  ((boundaryRevisedAuthoritativeRoot initial rooted coface).toLedgerRoot
    ).generatedAtTemporalVisit (.finite
      (boundaryRevisedAuthoritativeRoot initial rooted coface).toRoot.initialVisit)

private def boundaryRevisedOldEntryRow
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {obstruction : (BN initial).ObstructionAt .cofinal}
    (rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction)
    (coface : GeneratedMinimalCofaceAt
      rooted) :
    (boundaryRevisedInitialGeneratedEvolution initial rooted coface
      ).GeneratedEntryRowAt (boundaryRevisedOldEntry initial rooted coface) :=
  ((boundaryRevisedInitialGeneratedEvolution initial rooted coface
    ).canonicalGeneratedEntryRow?
      (boundaryRevisedOldEntry initial rooted coface)).get (by rfl)

/-- Every inherited old entry is the same source-owned old row in this
boundary fibre and therefore appears in the actual revised initial patch. -/
private def boundaryRevisedOldEntryRows
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {obstruction : (BN initial).ObstructionAt .cofinal}
    (rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction)
    (coface : GeneratedMinimalCofaceAt rooted)
    (oldEntry : OpenResponsibilityAt (BN initial)
      ((boundaryFinalAuthoritativeRoot initial).toRoot.supportAt
        rooted.oldSuccessor.next)) :
    (boundaryRevisedInitialGeneratedEvolution initial rooted coface
      ).GeneratedEntryRowAt (coface.cofaceLedgerRetract.forward oldEntry) := by
  have oldEntry_eq : oldEntry = rooted.targetEntry :=
    (boundaryOpenResponsibility_subsingleton initial _).elim _ _
  subst oldEntry
  exact boundaryRevisedOldEntryRow initial rooted coface

private def boundaryRevisedNewEntryRow
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {obstruction : (BN initial).ObstructionAt .cofinal}
    (rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction)
    (coface : GeneratedMinimalCofaceAt
      rooted) :
    (boundaryRevisedInitialGeneratedEvolution initial rooted coface
      ).GeneratedEntryRowAt (boundaryRevisedNewEntry initial rooted coface) :=
  ((boundaryRevisedInitialGeneratedEvolution initial rooted coface
    ).canonicalGeneratedEntryRow?
      (boundaryRevisedNewEntry initial rooted coface)).get (by rfl)

private def boundaryGeneratedTypedRevision
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (obstruction : (BN initial).ObstructionAt .cofinal)
    (rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction)
    (coface : GeneratedMinimalCofaceAt rooted) :
    GeneratedTypedSemanticWorldNetworkRevisionAt rooted where
  NewN := coface.worldNetwork
  translation := coface.translation
  NewV := boundaryRevisedVocabulary initial rooted coface
  newLivingRoot := boundaryRevisedLivingRoot initial rooted coface
  new_support_restricts :=
    coface.firstWrite_targetSupport_is_cofaceRestriction
  oldTargetOpenLedger := coface.cofaceLedgerRetract
  oldTargetOpenClaim_commutes := fun _ => rfl
  oldTargetOpenProgressBudget_not_refilled := fun _ => Nat.le_refl _
  occurrencePresentation :=
    boundaryRevisedOccurrencePresentation initial rooted coface
  occurrence_commutes := rfl
  firstWrite := boundaryRevisedFirstWrite initial rooted coface
  newOnlyEntry := boundaryRevisedNewEntry initial rooted coface
  newOnlyProgressBudget_eq_zero := rfl
  revisedClaimHolds := coface.obstructionClaimHolds
  semanticChange := coface.obstructionSemanticChange
  revisedClaim_hasNoOldPreimage := coface.obstructionClaim_hasNoOldPreimage
  newOnlyIncidence_hasNoOldPreimage :=
    coface.obstructionIncidence_hasNoOldPreimage
  oldEntryRows := boundaryRevisedOldEntryRows initial rooted coface
  newOnlyEntry_hasNoOldPreimage := coface.obstructionEntry_hasNoOldPreimage
  newOnlyEntryRow := boundaryRevisedNewEntryRow initial rooted coface

private theorem boundaryGeneratedTypedRevisionFieldGrounding
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (obstruction : (BN initial).ObstructionAt .cofinal)
    (rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction)
    (coface : GeneratedMinimalCofaceAt rooted) :
    (boundaryGeneratedTypedRevision initial obstruction rooted coface
      ).ExactFieldGrounding where
  network_eq := rfl
  lawSurface_heq := HEq.rfl
  translation_heq := HEq.rfl
  initialSupport_heq := HEq.rfl
  oldTargetOpenLedger_heq := HEq.rfl
  newOnlyEntry_heq := HEq.rfl
  revisedClaimHolds_heq := HEq.rfl
  semanticChange_heq := HEq.rfl

private def boundaryTypedRevisionSource
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (obstruction : (BN initial).ObstructionAt .cofinal)
    (rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction) :
    FieldGroundedTypedSemanticWorldNetworkRevisionAt rooted :=
  FieldGroundedTypedSemanticWorldNetworkRevisionAt.ofGeneratedOccurrence
    (boundaryGeneratedTypedRevision initial obstruction rooted
      (root_obstruction_generates_minimal_coface rooted))
    (boundaryGeneratedTypedRevisionFieldGrounding initial obstruction rooted
      (root_obstruction_generates_minimal_coface rooted))

private def sourceGeneratedBoundaryTypedRevision
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (obstruction : (BN initial).ObstructionAt .cofinal)
    (rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction) :
    GeneratedTypedSemanticWorldNetworkRevisionAt rooted :=
  (boundaryTypedRevisionSource initial obstruction rooted).generate

private abbrev SourceGeneratedBoundaryRecoveryAnswerAndNextAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (obstruction : (BN initial).ObstructionAt .cofinal)
    (rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction) :=
  SourceNativeLivingCausalEntryAnswerAndNextAt
      (boundaryTypedRevisionSource initial obstruction rooted).generate.newLivingRoot
      (TypedSemanticWorldNetworkU8Lifecycle.oldFirstWriteSuccessor
        (boundaryTypedRevisionSource initial obstruction rooted)).targetVisit
      (TypedSemanticWorldNetworkU8Lifecycle.oldFirstWriteSuccessor
        (boundaryTypedRevisionSource initial obstruction rooted)).targetEntry
      (TypedSemanticWorldNetworkU8Lifecycle.oldFirstWriteTargetAuthority
        (boundaryTypedRevisionSource initial obstruction rooted))

private def sourceGeneratedBoundaryRecoveryAnswerAndNext
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (obstruction : (BN initial).ObstructionAt .cofinal)
    (rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction) :
    SourceGeneratedBoundaryRecoveryAnswerAndNextAt initial obstruction rooted :=
  generatedOldTargetAnswerAndNext
    (boundaryTypedRevisionSource initial obstruction rooted)

private def sourceGeneratedNativeAccumulationBoundaryAnswerAndNext
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (obstruction : (BN initial).ObstructionAt .cofinal)
    (rooted : BoundaryRootedActualExpressibilityFailureAt initial obstruction) :
    SourceGeneratedBoundaryRecoveryAnswerAndNextAt initial obstruction rooted :=
  sourceGeneratedBoundaryRecoveryAnswerAndNext initial obstruction rooted

/-! ## Source-generated native boundary U8 payload -/

/-- The source-generated U8 branch retains the original cofinal entry authority,
the rooted failure and no independently replaceable revision payload.  Every
coface, equation, write and recovery readout below is recomputed from that one
fixed failure face. -/
structure SourceGeneratedNativeAccumulationBoundaryU8At
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) : Type 12 where
  private mk ::
  private rootFailureFace : BoundaryRootFailureFaceAt initial
    (boundaryObstruction initial elapsedBounded)

namespace SourceGeneratedNativeAccumulationBoundaryU8At

/-- Exact boundary obstruction selected by the same fixed inquiry occurrence. -/
def actualObstruction
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {elapsedBounded : BddAbove (Set.range (elapsedTime initial))}
    (_u8 : SourceGeneratedNativeAccumulationBoundaryU8At
      initial elapsedBounded) :
    (BN initial).ObstructionAt .cofinal :=
  boundaryObstruction initial elapsedBounded

/-- The physical exit is read from the exact obstruction, not stored beside it. -/
def exactExit
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {elapsedBounded : BddAbove (Set.range (elapsedTime initial))}
    (u8 : SourceGeneratedNativeAccumulationBoundaryU8At
      initial elapsedBounded) :
    NativeTemporalCofinalExactStrongFaceExitAt initial elapsedBounded :=
  u8.actualObstruction.exactExit

/-- The rooted failure is a dependent readout of the sealed U8 payload. -/
def rootedFailure
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {elapsedBounded : BddAbove (Set.range (elapsedTime initial))}
    (u8 : SourceGeneratedNativeAccumulationBoundaryU8At
      initial elapsedBounded) :
    BoundaryRootedActualExpressibilityFailureAt initial
      u8.actualObstruction :=
  sourceGeneratedBoundaryRootedFailure u8.rootFailureFace

/-- The cofinal strong-face failure is the original source-generated failure. -/
theorem strongFaceFailure_eq
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {elapsedBounded : BddAbove (Set.range (elapsedTime initial))}
    (u8 : SourceGeneratedNativeAccumulationBoundaryU8At
      initial elapsedBounded) :
    u8.exactExit.strongFaceFailure =
      nativeTemporalCofinalStrongFaceFailure initial :=
  u8.actualObstruction.strongFaceFailure_eq_sourceGenerated

/-- The typed revision is generated from the sealed rooted failure. -/
def typedRevision
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {elapsedBounded : BddAbove (Set.range (elapsedTime initial))}
    (u8 : SourceGeneratedNativeAccumulationBoundaryU8At
      initial elapsedBounded) :
    GeneratedTypedSemanticWorldNetworkRevisionAt u8.rootedFailure :=
  sourceGeneratedBoundaryTypedRevision initial u8.actualObstruction
    u8.rootedFailure

/-- Recovery answer-and-next is the same typed revision's canonical old-row
successor, never a second caller-supplied continuation. -/
def answerAndNext
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {elapsedBounded : BddAbove (Set.range (elapsedTime initial))}
    (u8 : SourceGeneratedNativeAccumulationBoundaryU8At
      initial elapsedBounded) :
    SourceGeneratedBoundaryRecoveryAnswerAndNextAt initial
      u8.actualObstruction u8.rootedFailure :=
  sourceGeneratedNativeAccumulationBoundaryAnswerAndNext initial
    u8.actualObstruction u8.rootedFailure

/-- Forget only the revised presentation coordinate of the canonical recovery
target. The native current is fixed by the sealed U8 occurrence. -/
def recoveryNativeCurrent
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {elapsedBounded : BddAbove (Set.range (elapsedTime initial))}
    (u8 : SourceGeneratedNativeAccumulationBoundaryU8At
      initial elapsedBounded) :
    NativeTemporalCurrent initial :=
  restrictBoundaryRevisedCurrent initial
    u8.answerAndNext.nextCurrent.visit.current

end SourceGeneratedNativeAccumulationBoundaryU8At

/-- Generate the U8 branch from the original root's exact cofinal occurrence
and its source-fixed strong-face failure. -/
private def sourceGeneratedNativeAccumulationBoundaryU8
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (rootFailureFace : BoundaryRootFailureFaceAt initial
      (boundaryObstruction initial elapsedBounded)) :
    SourceGeneratedNativeAccumulationBoundaryU8At initial elapsedBounded :=
  ⟨rootFailureFace⟩

/-! ## Public automatic inquiry engine -/

/-- Old-language answer restriction of the original cofinal occurrence.  The
role coordinate is proof-irrelevant; the unboundedness receipt is read from
the fixed inquiry decision. -/
private def boundaryOldInquiryAnswerFace
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedUnbounded : ¬ BddAbove (Set.range (elapsedTime initial))) :
    SourceNativeRootSemanticFaceAt
      (boundaryFinalLivingRoot initial)
      (boundaryOriginalCofinalVisit initial) where
  projection := .answer
  active := by
    change boundaryFinalProjectionActiveAt initial
      BoundaryFinalProjection.answer (boundaryEmitted initial .cofinal)
    exact ⟨rfl, elapsedUnbounded⟩
  classifier_eq := by
    change (boundaryFinalProjectionLaw initial).classify
      BoundaryFinalProjection.answer (boundaryEmitted initial .cofinal) = .inl _
    simp [boundaryFinalProjectionLaw, BoundaryFinalProjection.answer,
      elapsedUnbounded]
    congr

private def boundaryOldInquiryAnswerConsumer
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedUnbounded : ¬ BddAbove (Set.range (elapsedTime initial))) :
    SourceNativeInquiryAnswerConsumerAt PUnit.unit
      (boundaryInquiryEvent initial)
      (boundaryCofinalEntry initial)
      (boundaryOldInquiryAnswerFace initial elapsedUnbounded) where
  projection := .consumer
  active := by
    change boundaryFinalProjectionActiveAt initial
      BoundaryFinalProjection.consumer (boundaryEmitted initial .cofinal)
    exact ⟨rfl, elapsedUnbounded⟩
  classifier_eq := by
    change (boundaryFinalProjectionLaw initial).classify
      BoundaryFinalProjection.consumer (boundaryEmitted initial .cofinal) = .inl _
    simp [boundaryFinalProjectionLaw, BoundaryFinalProjection.consumer,
      elapsedUnbounded]
    congr
  project_heq := HEq.rfl

/-- The exact cofinal failure generates its concrete minimal-coface
realization inside the same source compiler branch. -/
private noncomputable def sourceGeneratedBoundaryInquiryU8Core
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    SourceGeneratedInquiryU8RevisionCoreAt
      (boundaryFinalLivingRoot initial) (boundaryOriginalCofinalVisit initial)
      (boundaryU7 initial) (boundaryU7Calculus initial)
      (boundaryOldTheory initial) PUnit.unit (boundaryInquiryEvent initial)
      (boundaryCofinalEntry initial)
      (boundaryOriginalLivingCofinalEntryAuthority initial)
      (boundaryObstruction initial elapsedBounded)
      (boundaryCofinalU7TheoryAudit initial
        (boundaryObstruction initial elapsedBounded))
      (boundaryExpressibilityFailure initial
        (boundaryObstruction initial elapsedBounded)) := by
  let obstruction := boundaryObstruction initial elapsedBounded
  let face := sourceGeneratedBoundaryRootFailureFace initial elapsedBounded
  have rootEntryEq : face.rootEntry = boundaryCofinalEntry initial :=
    (boundaryOpenResponsibility_subsingleton initial _).elim _ _
  let successor : CausalEntrySuccessorAt
      (boundaryFinalAuthoritativeRoot initial).toLedgerRoot
      (boundaryOriginalCofinalVisit initial) face.rootEntry :=
    CausalEntrySuccessorAt.ofNonterminal rfl
  let rooted := RootedActualExpressibilityFailureAt.ofRootFailureFace face
    (rootEntryEq.symm ▸
      (boundaryOriginalLivingCofinalEntryAuthority initial).toAuthoritativeAuthority)
    successor
  let frontier := SourceNativeInquiryCofaceFrontierAt.ofRootFailureFace
    (query := PUnit.unit) (event := boundaryInquiryEvent initial)
    (authority := boundaryOriginalLivingCofinalEntryAuthority initial)
    (u7Gate := boundaryCofinalU7TheoryAudit initial obstruction)
    face rootEntryEq successor
  exact
    { frontier := frontier
      revision := boundaryTypedRevisionSource initial obstruction rooted }

private noncomputable def boundaryInquiryCompilation
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    SourceNativeInquiryCompilationAt
      (boundaryFinalLivingRoot initial) (boundaryOriginalCofinalVisit initial)
      (boundaryU7 initial) (boundaryU7Calculus initial)
      (boundaryOldTheory initial) PUnit.unit (boundaryInquiryEvent initial)
      (boundaryCofinalEntry initial)
      (boundaryOriginalLivingCofinalEntryAuthority initial) :=
  match boundaryInquiryDecision initial with
  | .unbounded elapsedUnbounded => .answered
      (boundaryOldInquiryAnswerFace initial elapsedUnbounded)
      (boundaryOldInquiryAnswerConsumer initial elapsedUnbounded)
  | .requiresRevision elapsedBounded =>
      let obstruction := boundaryObstruction initial elapsedBounded
      .requiresU8 obstruction
        (boundaryCofinalU7TheoryAudit initial obstruction)
        (boundaryExpressibilityFailure initial obstruction)
        (sourceGeneratedBoundaryInquiryU8Core initial elapsedBounded)

private theorem boundaryInquiryCompilation_audit
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    (boundaryInquiryCompilation initial).audit =
      boundaryInquiryFrontAudit initial := by
  generalize decision_eq : boundaryInquiryDecision initial = decision
  cases decision <;>
    unfold boundaryInquiryCompilation boundaryInquiryFrontAudit <;>
    rw [decision_eq] <;> rfl

private def boundaryInquiryCompilationFaceCore
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    SourceNativeRootInquiryCompilationFaceCoreAt
      (boundaryFinalLivingRoot initial) (boundaryOriginalCofinalVisit initial)
      PUnit.unit (boundaryInquiryEvent initial) (boundaryCofinalEntry initial)
      (boundaryOriginalLivingCofinalEntryAuthority initial)
      (boundaryInquiryCompilation initial) where
  projection := .resolution
  active := ⟨rfl⟩
  classifier_eq := rfl
  project_heq := by
    change HEq
      (SourceNativeInquiryCompilationTokenAt.canonical
        (entry := boundaryCofinalEntry initial)
        (query := PUnit.unit)
        (event := boundaryInquiryEvent initial)
        (audit := boundaryInquiryFrontAudit initial)
        (boundaryInquiryTokenAnswer initial).readout)
      (SourceNativeInquiryCompilationTokenAt.canonical
        (entry := boundaryCofinalEntry initial)
        (query := PUnit.unit)
        (event := boundaryInquiryEvent initial)
        (audit := (boundaryInquiryCompilation initial).audit)
        (boundaryInquiryCompilation initial).answerReadout)
    generalize decision_eq : boundaryInquiryDecision initial = decision
    cases decision <;>
      unfold boundaryInquiryCompilation boundaryInquiryFrontAudit
        boundaryInquiryTokenAnswer <;>
      rw [decision_eq] <;> rfl

private noncomputable def boundaryInquiryState
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    RootInquiryStateAt (BN initial) (BV initial) where
  root := boundaryFinalLivingRoot initial
  visit := boundaryOriginalCofinalVisit initial
  U7 := boundaryU7 initial
  calculus := boundaryU7Calculus initial
  Query := PUnit
  entryAt := fun _ => boundaryCofinalEntry initial
  authorityAt := fun _ => boundaryOriginalLivingCofinalEntryAuthority initial
  compilationProgramAt := fun _ =>
    { compile := fun _exactOccurrence => boundaryInquiryCompilation initial }
  compilationFaceAt := fun _ => boundaryInquiryCompilationFaceCore initial
  u7RootDisposition_commutes := by
    intro _query _obstruction _audit audit_eq
    generalize decision_eq : boundaryInquiryDecision initial = decision
    cases decision with
    | unbounded elapsedUnbounded =>
        unfold boundaryInquiryCompilation at audit_eq
        rw [decision_eq] at audit_eq
        cases audit_eq
    | requiresRevision elapsedBounded =>
        unfold boundaryInquiryCompilation at audit_eq
        rw [decision_eq] at audit_eq
        cases audit_eq
        exact (sourceGeneratedBoundaryRootFailureFace initial elapsedBounded
          ).rootDispositionCommutes

private def boundaryInquiryFace
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    SourceNativeRootInquiryCompilationFaceAt (boundaryInquiryState initial) () :=
  (boundaryInquiryState initial).compilationFaceAt ()

private noncomputable def sourceGeneratedBoundaryInquiryU8Revision
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    SourceGeneratedInquiryU8RevisionAt
      (boundaryInquiryState initial) ()
      (boundaryObstruction initial elapsedBounded)
      (boundaryCofinalU7TheoryAudit initial
        (boundaryObstruction initial elapsedBounded))
      (boundaryExpressibilityFailure initial
        (boundaryObstruction initial elapsedBounded)) :=
  sourceGeneratedBoundaryInquiryU8Core initial elapsedBounded

private noncomputable def sourceGeneratedBoundaryInquiryU8Completion
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    SourceGeneratedInquiryU8CompletionAt
      (boundaryInquiryState initial) ()
      (boundaryObstruction initial elapsedBounded)
      (boundaryCofinalU7TheoryAudit initial
        (boundaryObstruction initial elapsedBounded))
      (boundaryExpressibilityFailure initial
        (boundaryObstruction initial elapsedBounded)) :=
  sourceGeneratedBoundaryInquiryU8Revision initial elapsedBounded

private noncomputable def boundaryInquiryEngineState
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    RootInquiryEngineStateAt (BN initial) (BV initial) :=
  RootInquiryEngineStateAt.create (boundaryInquiryState initial)

private noncomputable def boundaryInquiryPresentation
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    RootInquiryStatePresentation where
  N := BN initial
  V := BV initial
  state := boundaryInquiryEngineState initial

private noncomputable def boundaryInquiryProcess
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    SourceNativeInquiryEngineProcess.{0} :=
  (boundaryInquiryPresentation initial).oneShotProcess

private noncomputable def boundaryInquiryEngine
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    Engine (boundaryInquiryProcess initial) :=
  Engine.initial (boundaryInquiryProcess initial)

private def boundaryInquiryActivation
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    Engine.SourceNativeInquiryActivationAt (boundaryInquiryEngine initial) :=
  (boundaryInquiryEngine initial).uniqueInquiryActivation
    (by change PUnit; exact PUnit.unit)
    (by
      intro candidate
      change PUnit at candidate
      cases candidate
      rfl)

private def boundaryInquiryQuery
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    (boundaryInquiryEngine initial).Query :=
  (boundaryInquiryActivation initial).query

private noncomputable def sourceGeneratedBoundaryInquiryOccurrence
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    Engine.ExactRootInquiryOccurrenceAt (boundaryInquiryEngine initial)
      (boundaryInquiryQuery initial) :=
  (boundaryInquiryEngine initial).ask (boundaryInquiryActivation initial)

/-- Exact old-language branch emitted by the fixed boundary inquiry engine. -/
structure SourceGeneratedBoundaryOldInquiryAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) : Type 13 where
  private mk ::
  elapsedUnbounded : ¬ BddAbove (Set.range (elapsedTime initial))

namespace SourceGeneratedBoundaryOldInquiryAt

/-- The old answer retains the exact occurrence emitted by the fixed engine. -/
noncomputable def occurrence
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    (_generated : SourceGeneratedBoundaryOldInquiryAt initial) :
    Engine.ExactRootInquiryOccurrenceAt (boundaryInquiryEngine initial)
      (boundaryInquiryQuery initial) :=
  sourceGeneratedBoundaryInquiryOccurrence initial

end SourceGeneratedBoundaryOldInquiryAt

/-- Exact revised branch emitted by the fixed boundary inquiry engine.  The
constructor is private: boundedness, the failure face and the U8 completion
cannot be submitted independently of the one generated inquiry occurrence. -/
structure SourceGeneratedBoundaryRevisedInquiryAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) : Type 13 where
  private mk ::
  elapsedBounded : BddAbove (Set.range (elapsedTime initial))
  private completion :
    SourceGeneratedInquiryU8CompletionAt
      (boundaryInquiryState initial) ()
      (boundaryObstruction initial elapsedBounded)
      (boundaryCofinalU7TheoryAudit initial
        (boundaryObstruction initial elapsedBounded))
      (boundaryExpressibilityFailure initial
        (boundaryObstruction initial elapsedBounded))

/-- Private branch coordinate of the one fixed-source inquiry outcome. -/
private inductive BoundaryInquiryOutcomeCoordinateAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) : Type 13
  | oldAnswer
      (generated : SourceGeneratedBoundaryOldInquiryAt initial)
  | revisedAnswer
      (generated : SourceGeneratedBoundaryRevisedInquiryAt initial)

/-- The fixed source has exactly one public boundary outcome.  Its branch
coordinate is private and can only be eliminated through `fold`. -/
structure SourceGeneratedBoundaryInquiryOutcomeAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) : Type 13 where
  private mk ::
  private coordinate : BoundaryInquiryOutcomeCoordinateAt initial

namespace SourceGeneratedBoundaryInquiryOutcomeAt

/-- Consume the source-generated branch without acquiring either constructor. -/
def fold
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    (outcome : SourceGeneratedBoundaryInquiryOutcomeAt initial)
    {Result : Sort u}
    (oldAnswer : SourceGeneratedBoundaryOldInquiryAt initial -> Result)
    (revisedAnswer : SourceGeneratedBoundaryRevisedInquiryAt initial -> Result) :
    Result :=
  match outcome.coordinate with
  | .oldAnswer generated => oldAnswer generated
  | .revisedAnswer generated => revisedAnswer generated

end SourceGeneratedBoundaryInquiryOutcomeAt

/-- Run the exact inquiry occurrence once and expose only its source-generated
old or revised dependent readout. -/
noncomputable def sourceGeneratedBoundaryInquiryOutcome
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    SourceGeneratedBoundaryInquiryOutcomeAt initial := by
  generalize decision_eq : boundaryInquiryDecision initial = decision
  cases decision with
  | unbounded elapsedUnbounded =>
      exact ⟨.oldAnswer
        { elapsedUnbounded := elapsedUnbounded }⟩
  | requiresRevision elapsedBounded =>
      let completion :=
        sourceGeneratedBoundaryInquiryU8Completion initial elapsedBounded
      refine ⟨.revisedAnswer
        { elapsedBounded := elapsedBounded
          completion := completion }⟩

namespace SourceGeneratedBoundaryRevisedInquiryAt

/-- The revised package always refers to the one occurrence emitted by the
fixed engine; no occurrence value is stored beside the completion. -/
noncomputable def occurrence
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    (_generated : SourceGeneratedBoundaryRevisedInquiryAt initial) :
    Engine.ExactRootInquiryOccurrenceAt (boundaryInquiryEngine initial)
      (boundaryInquiryQuery initial) :=
  sourceGeneratedBoundaryInquiryOccurrence initial

/-- The failure face is read from the exact completion generated by the same
engine occurrence; it is never rebuilt from a submitted boundedness proof. -/
def rootFailureFace
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    (generated : SourceGeneratedBoundaryRevisedInquiryAt initial) :
    BoundaryRootFailureFaceAt initial
      (boundaryObstruction initial generated.elapsedBounded) :=
  generated.completion.revisionReceipt.face

/-- Domain U8 payload derived from the fixed engine occurrence. -/
def u8
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    (generated : SourceGeneratedBoundaryRevisedInquiryAt initial) :
    SourceGeneratedNativeAccumulationBoundaryU8At
      initial generated.elapsedBounded :=
  sourceGeneratedNativeAccumulationBoundaryU8 initial generated.elapsedBounded
    generated.rootFailureFace

end SourceGeneratedBoundaryRevisedInquiryAt

end
end ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationBoundaryDisposition
end NavierStokes
end SaturationMonoid
