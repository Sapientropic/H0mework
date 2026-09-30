import H0mework.Foundation.Cofinal.TemporalAnswer
import H0mework.Foundation.Authority.Representation
import H0mework.Foundation.Authority.EntryDisposition
import H0mework.NavierStokes.Restart.NativeActualRoot
import H0mework.NavierStokes.Restart.VelocityWeakEndpoint
import H0mework.NavierStokes.VelocityGalerkin.UniformKineticLedger
import H0mework.NavierStokes.Restart.FiniteTimeVorticityDivergence
import H0mework.NavierStokes.Restart.FiniteTimeHighFrequencyTailDivergence
import H0mework.NavierStokes.EndpointTransport.NativeHighFrequencyProjectedParabolicTrace

/-!
# Source-native finite, cofinal, and Galerkin history

The authoritative whole-restart process starts with the one-step responder from
`GeneratedWholeRestartNativeActualRoot`.  The same original source also emits its
canonical weak cofinal receipt and the subsequent Galerkin writes.  All of
them live in one source-native ledger root.

A local bounded-elapsed-time hypothesis identifies the analytic accumulation
time of that already generated cofinal receipt.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot

open Filter Set
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFiniteModalPicardBounds
open ThreeDimensionalVorticityCoefficientRawSourceCore
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ResponsibilityLifecycle
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairOccurrenceRateSettlement
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityPairDiagonalAction
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeActualRoot
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFamily
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFiniteTimeVorticityDivergence
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFiniteTimeHighFrequencyTailDivergence
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHighFrequencyEscape
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairOccurrenceWork
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPreQuotientNonlinearWork
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEnstrophyWork
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPositiveOutputWorkDualBudget
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime.GeneratedInfiniteWholeRestartEndpointMacroLineage.FullFrameBoundaryVorticityCofinalNonlinearNegativeOneEuclideanBalance
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime.GeneratedInfiniteWholeRestartEndpointMacroLineage.FullFrameBoundaryVorticityNativeHighFrequencyProjectedParabolicTrace

noncomputable section

/-! ## One source carrier for finite writes and the cofinal Galerkin continuation -/

/-- The original root owns its finite support and one source-generated
cofinal support. -/
inductive NativeTemporalSupport : Type
  | finite
  | cofinal
  deriving DecidableEq

/-- Unconditional kinetic/velocity weak endpoint data generated on one common
actual subsequence of the native run. -/
structure GeneratedWholeRestartCanonicalWeakCofinalReceiptAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) : Type where
  kineticEndpoint : WholeRestartKineticEndpointState
  velocityEndpoint : WholeRestartVelocityEndpointState
  subsequence : Nat -> Nat
  subsequence_strictMono : StrictMono subsequence
  kineticEndpoint_norm_le :
    ‖kineticEndpoint‖ ≤ ‖wholeRestartContactKineticState initial 0‖
  velocityEndpoint_norm_le :
    ‖velocityEndpoint‖ ≤ ‖wholeRestartContactVelocityState initial 0‖
  kineticWeak_tendsto :
    ∀ test : WholeRestartKineticEndpointState,
      Tendsto
        (fun index =>
          inner ℂ
            (wholeRestartContactKineticState initial (subsequence index))
            test)
        atTop (nhds (inner ℂ kineticEndpoint test))
  velocityWeak_tendsto :
    ∀ test : WholeRestartVelocityEndpointState,
      Tendsto
        (fun index =>
          inner ℂ
            (wholeRestartContactVelocityState initial (subsequence index))
            test)
        atTop (nhds (inner ℂ velocityEndpoint test))
  velocityEndpoint_transverse :
    WholeRestartVelocityEndpointTransverse velocityEndpoint
  velocityEndpoint_reality :
    WholeRestartVelocityEndpointReality velocityEndpoint

/-- Canonical source packaging of simultaneous weak compactness. -/
noncomputable def sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    GeneratedWholeRestartCanonicalWeakCofinalReceiptAt initial := by
  let endpointResult :=
    exists_wholeRestartContactKineticVelocityWeakEndpoints initial
  let kineticEndpoint := Classical.choose endpointResult
  let velocityResult := Classical.choose_spec endpointResult
  let velocityEndpoint := Classical.choose velocityResult
  let subsequenceResult := Classical.choose_spec velocityResult
  let subsequence := Classical.choose subsequenceResult
  have specifications := Classical.choose_spec subsequenceResult
  exact
    { kineticEndpoint := kineticEndpoint
      velocityEndpoint := velocityEndpoint
      subsequence := subsequence
      subsequence_strictMono := specifications.1
      kineticEndpoint_norm_le := specifications.2.1
      velocityEndpoint_norm_le := specifications.2.2.1
      kineticWeak_tendsto := specifications.2.2.2.1
      velocityWeak_tendsto := specifications.2.2.2.2.1
      velocityEndpoint_transverse := specifications.2.2.2.2.2.1
      velocityEndpoint_reality := specifications.2.2.2.2.2.2 }

/-- Inside the local bounded-time reductio, the subsequence owned by the
cofinal receipt approaches the finite accumulation time. -/
theorem sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt_elapsed_tendsto
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    Tendsto
      (fun index => elapsedTime initial
        ((sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt
          initial).subsequence index))
      atTop
      (nhds (wholeRestartVelocityAccumulationTime initial)) := by
  exact
    (tendsto_atTop_ciSup
      (elapsedTime_strictMono initial).monotone elapsedBounded).comp
      (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt
        initial).subsequence_strictMono.tendsto_atTop

/-- Source-fixed whole-vorticity responsibility at the original cofinal
current.  The law is generated before the ledger row and is carried by that
row through every native continuation. -/
structure NativeTemporalCofinalStrongFaceFailureAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) : Type where
  private mk ::
  fails :
    ∀ _elapsedBounded : BddAbove (Set.range (elapsedTime initial)),
      ∀ endpoint : ComplexVorticityHilbertState,
        ¬ Tendsto
          (fun index => (run initial index).contact.physicalState)
          atTop (nhds endpoint)
  highFrequencyTailDiverges :
    ∀ _elapsedBounded : BddAbove (Set.range (elapsedTime initial)),
      ∀ radius : Nat,
        Tendsto
          (fun index =>
            restartPhysicalHighFrequencyTailMass initial index radius)
          atTop atTop
  wholePDEEffect :
    ∀ _elapsedBounded : BddAbove (Set.range (elapsedTime initial)),
      ∃ contactIndex : Nat → Nat,
        contactIndex 0 = 0 ∧
          StrictMono contactIndex ∧
          ∀ step : Nat,
            let radius := 2 * (contactIndex step + 1)
            let interval :=
              Finset.Ico (contactIndex step) (contactIndex (step + 1))
            let trace :=
              ∑ index ∈ interval,
                receiptHighFrequencyProjectedParabolicTrace
                  (run initial index).nextContact.prefixReceipt radius
            let pairWork :=
              ∑ index ∈ interval,
                actualWholeFinitePairOccurrenceWork
                  (run initial index).nextContact.prefixReceipt
                  (wholeRestartModes radius)
            let tangentViscousCross :=
              ∑ index ∈ interval,
                2 * RCLike.re (inner ℂ
                  (puncturedEuclideanSpaceTimeState
                    (run initial index).nextContact.prefixReceipt.wholeTangent)
                  (puncturedEuclideanSpaceTimeState
                    (receiptViscousNegativeOneState
                      (run initial index).nextContact.prefixReceipt)))
            let viscousDebit :=
              ∑ index ∈ interval,
                actualWholeFiniteViscousPayment
                  (run initial index).nextContact.prefixReceipt
                  (wholeRestartModes radius)
            nu.coeff < trace ∧
              trace + nu.coeff * pairWork =
                tangentViscousCross + nu.coeff * viscousDebit ∧
              ∃ index ∈ interval,
                receiptHighFrequencyProjectedParabolicTrace
                    (run initial index).nextContact.prefixReceipt radius ≠ 0 ∧
                  ((∃ output ∈ wholeRestartModes radius,
                      ∃ first : IntegerWavevector,
                        actualWholePairOccurrenceWork
                          (run initial index).nextContact.prefixReceipt
                          output first ≠ 0) ∨
                    2 * RCLike.re (inner ℂ
                        (puncturedEuclideanSpaceTimeState
                          (run initial index).nextContact.prefixReceipt.wholeTangent)
                        (puncturedEuclideanSpaceTimeState
                          (receiptViscousNegativeOneState
                            (run initial index).nextContact.prefixReceipt))) ≠ 0 ∨
                    actualWholeFiniteViscousPayment
                        (run initial index).nextContact.prefixReceipt
                        (wholeRestartModes radius) ≠ 0)
  literalCrossPairEffect :
    ∀ _elapsedBounded : BddAbove (Set.range (elapsedTime initial)),
      ∀ lower : Nat,
        ∃ index : Nat,
          lower ≤ index ∧
          ∃ time : Icc (0 : Real) (run initial index).nextContact.time.1,
          ∃ output left right leftActual rightActual : IntegerWavevector,
            right ≠ left ∧
            complexCoordinateRealInner
              (actualWholeSymmetricVorticityPairVector
                (run initial index).nextContact.prefixReceipt
                output left time)
              (actualWholeSymmetricVorticityPairVector
                (run initial index).nextContact.prefixReceipt
                output right time) ≠ 0 ∧
            (leftActual = left ∨ leftActual = output - left) ∧
            (rightActual = right ∨ rightActual = output - right) ∧
            actualWholeContinuousPairVector
                (run initial index).nextContact.prefixReceipt
                output leftActual time ≠ 0 ∧
            actualWholeContinuousPairVector
                (run initial index).nextContact.prefixReceipt
                output rightActual time ≠ 0 ∧
            (wholeRestartNextPairOccurrence
                  initial index output leftActual ≠ 0 ∨
              wholeRestartPairOccurrenceTrace
                initial index output leftActual time ≠ 0) ∧
            (wholeRestartNextPairOccurrence
                  initial index output rightActual ≠ 0 ∨
              wholeRestartPairOccurrenceTrace
                initial index output rightActual time ≠ 0)

/-- Canonical strong-face responsibility generated by the original finite
source. -/
def nativeTemporalCofinalStrongFaceFailure
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    NativeTemporalCofinalStrongFaceFailureAt initial := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro elapsedBounded endpoint contactTendsto
    exact
      (vorticityMass_tendsto_atTop_excludes_strongContactLanding
        initial
        (tendsto_restartPhysicalVorticityMass_atTop_of_elapsedTime_bddAbove
          initial elapsedBounded)
        endpoint) contactTendsto
  · intro elapsedBounded radius
    exact
      tendsto_restartPhysicalHighFrequencyTailMass_atTop_of_elapsedTime_bddAbove
        initial elapsedBounded radius
  · intro elapsedBounded
    exact
      elapsedBounded_generatesCofinalHighFrequencyProjectedParabolicTrace
        initial elapsedBounded
  · intro elapsedBounded lower
    exact
      elapsedTime_bddAbove_generates_literalCross_actualPairIncidence
        initial elapsedBounded lower

/-- The whole ledger has one responsibility at each actual root support. -/
inductive NativeTemporalResponsibility : Type
  | finite
  | cofinal

/-- Root-owned finite and cofinal fibres are unconditional. -/
inductive NativeTemporalOpenAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    NativeTemporalSupport -> NativeTemporalResponsibility -> Type
  | finite : NativeTemporalOpenAt initial .finite .finite
  | cofinal
      (failure : NativeTemporalCofinalStrongFaceFailureAt initial) :
      NativeTemporalOpenAt initial .cofinal .cofinal

/-- Shared network of the finite root and its cofinal Galerkin continuation. -/
def nativeTemporalNetwork
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
  ObstructionAt := fun _ => PEmpty
  obstructionClaim := fun obstruction => nomatch obstruction
  SemanticChangeAt := fun _ _ _ => PEmpty
  DispositionAt := fun _ _ => PEmpty

abbrev N
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :=
  nativeTemporalNetwork initial

/-! ## One original root through finite, cofinal, and Galerkin currents -/

inductive NativeTemporalCurrent
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) : Type
  | finite (stage : Nat)
  | cofinal
  | galerkin (radius : Nat)

abbrev NativeTemporalGalerkinWriteAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (radius : Nat) :=
  GeneratedWholeRestartVelocityEndpointGalerkinStage
    nu
    (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt
      initial).velocityEndpoint
    radius

/-- The cofinal continuation emits an actual finite Galerkin PDE
trajectory from the same source-generated weak endpoint. -/
noncomputable def sourceGeneratedNativeTemporalGalerkinWrite
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (radius : Nat) :
    NativeTemporalGalerkinWriteAt initial radius :=
  generatedWholeRestartVelocityEndpointGalerkinStage
    nu
    (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt
      initial).velocityEndpoint
    (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt
      initial).velocityEndpoint_reality
    radius

/-- Endpoint data emitted by the original root at its cofinal occurrence. -/
def sourceGeneratedNativeTemporalEndpointData
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    GeneratedWholeRestartVelocityEndpointData :=
  { velocityEndpoint :=
      (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt
        initial).velocityEndpoint
    velocityEndpoint_transverse :=
      (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt
        initial).velocityEndpoint_transverse
    velocityEndpoint_reality :=
      (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt
        initial).velocityEndpoint_reality }

/-- The original root emits the complete Galerkin family from its cofinal
endpoint data. -/
noncomputable def sourceGeneratedNativeTemporalGalerkinFamilyCore
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    GeneratedWholeRestartVelocityEndpointGalerkinFamilyCore nu :=
  generatedWholeRestartVelocityEndpointGalerkinFamilyCore
    nu (sourceGeneratedNativeTemporalEndpointData initial)

/-- The original root pays the radius-uniform kinetic and viscous ledger
for its complete Galerkin family. -/
noncomputable def
    sourceGeneratedNativeTemporalUniformKineticViscousLedgerCore
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu :=
  generatedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore
    (sourceGeneratedNativeTemporalGalerkinFamilyCore initial)

@[simp] theorem sourceGeneratedNativeTemporalGalerkinFamilyCore_stage
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (radius : Nat) :
    (sourceGeneratedNativeTemporalGalerkinFamilyCore initial).stage radius =
      sourceGeneratedNativeTemporalGalerkinWrite initial radius :=
  rfl

@[simp] theorem sourceGeneratedNativeTemporalUniformLedgerCore_stage
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (radius : Nat) :
    (sourceGeneratedNativeTemporalUniformKineticViscousLedgerCore
        initial).family.stage radius =
      sourceGeneratedNativeTemporalGalerkinWrite initial radius :=
  rfl

def nativeTemporalNativeWriteAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    NativeTemporalCurrent initial -> Type
  | .finite stage =>
      GeneratedWholeRestartNativeActualOccurrenceAt initial stage
  | .cofinal => GeneratedWholeRestartCanonicalWeakCofinalReceiptAt initial
  | .galerkin radius => NativeTemporalGalerkinWriteAt initial radius

def nativeTemporalNativeTarget
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    {current : NativeTemporalCurrent initial} ->
      nativeTemporalNativeWriteAt initial current ->
        NativeTemporalCurrent initial
  | .finite stage, _ => .finite (stage + 1)
  | .cofinal, _ => .galerkin 0
  | .galerkin radius, _ => .galerkin (radius + 1)

noncomputable def nativeTemporalVocabulary
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

abbrev V
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :=
  nativeTemporalVocabulary initial

/-- Primitive events for the finite responder, its source-generated weak
cofinal occurrence, and every Galerkin write. -/
inductive NativeTemporalRootEventAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    NativeTemporalCurrent initial -> NativeTemporalSupport -> Type
  | finite
      (stage : Nat)
      (occurrence :
        GeneratedWholeRestartNativeActualOccurrenceAt initial stage) :
      NativeTemporalRootEventAt initial (.finite stage) .finite
  | cofinal
      (receipt : GeneratedWholeRestartCanonicalWeakCofinalReceiptAt initial) :
      NativeTemporalRootEventAt initial .cofinal .cofinal
  | galerkin
      (radius : Nat)
      (write : NativeTemporalGalerkinWriteAt initial radius) :
      NativeTemporalRootEventAt initial (.galerkin radius) .cofinal

def nativeTemporalEventAlgebra
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    SourceNativeEventAlgebra (N initial) (V initial) where
  EventAt := NativeTemporalRootEventAt initial
  compile := fun event =>
    match event with
    | .finite _ occurrence => .nativeWrite occurrence
    | .cofinal receipt => .nativeWrite receipt
    | .galerkin _ write => .nativeWrite write
  AffectedInventoryAt := fun {_current} {support} _event =>
    OpenResponsibilityAt (N initial) support
  affectedInventoryPresentation := fun _event =>
    ConstructivePresentation.refl _
  anchorKey := id
  incidenceKey := id
  lineageKey := id
  anchor_commutes := by
    intro current support event
    cases event <;> rfl
  incidence_commutes := by
    intro current support event
    cases event <;> rfl
  lineage_commutes := by
    intro current support event
    cases event <;> rfl

def nativeTemporalSource
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    SourceNativeSource (N initial) (V initial) where
  initial := .finite 0
  law := nativeTemporalEventAlgebra initial

def nativeTemporalEmitted
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    (current : NativeTemporalCurrent initial) ->
      (nativeTemporalSource initial).toRootSource.actual.OccurrenceAt current
  | .finite stage =>
      ⟨.finite,
        .finite stage
          (generatedWholeRestartNativeActualOccurrence initial stage)⟩
  | .cofinal =>
      ⟨.cofinal,
        .cofinal
          (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial)⟩
  | .galerkin radius =>
      ⟨.cofinal,
        .galerkin radius
          (sourceGeneratedNativeTemporalGalerkinWrite initial radius)⟩

structure NativeTemporalIncidenceTransitionAt
    (source target : NativeTemporalSupport) : Type where
  support_eq : source = target

structure NativeTemporalExactTransitionAt
    (source target : NativeTemporalSupport) : Type where
  support_eq : source = target

/-- The exact finite responsibility carried by every native restart write. -/
def nativeTemporalFiniteEntry
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    OpenResponsibilityAt (N initial) .finite :=
  ⟨.finite, .finite⟩

private theorem nativeTemporalFiniteEntry_eq
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (entry : OpenResponsibilityAt (N initial) .finite) :
    nativeTemporalFiniteEntry initial = entry := by
  rcases entry with ⟨responsibility, openAt⟩
  cases openAt
  rfl

/-- The exact boundary responsibility written at the original
cofinal occurrence. -/
def nativeTemporalCofinalEntry
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    OpenResponsibilityAt (N initial) .cofinal :=
  ⟨.cofinal,
    .cofinal (nativeTemporalCofinalStrongFaceFailure initial)⟩

private theorem nativeTemporalCofinalEntry_eq
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (entry : OpenResponsibilityAt (N initial) .cofinal) :
    nativeTemporalCofinalEntry initial = entry := by
  rcases entry with ⟨responsibility, openAt⟩
  cases openAt
  rfl

/-- Read the source-fixed strong-face responsibility from an exact cofinal
ledger entry. -/
def nativeTemporalCofinalEntryStrongFaceFailure
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (entry : OpenResponsibilityAt (N initial) .cofinal) :
    NativeTemporalCofinalStrongFaceFailureAt initial := by
  rcases entry with ⟨responsibility, openAt⟩
  cases openAt with
  | cofinal failure => exact failure

/-- Primitive row event emitted by the original cofinal occurrence and by
each subsequent Galerkin PDE write for the same live responsibility. -/
inductive NativeTemporalCofinalRowEventAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    {current : NativeTemporalCurrent initial} ->
      (occurrence :
        (nativeTemporalSource initial).toRootSource.actual.OccurrenceAt
          current) ->
      {targetSupport : NativeTemporalSupport} ->
      (sourceEntry : OpenResponsibilityAt (N initial)
        ((nativeTemporalSource initial).toRootSource.account.supportOf
          occurrence)) ->
      (targetEntry : OpenResponsibilityAt (N initial) targetSupport) -> Type
  | finite
      (stage : Nat)
      (occurrence : GeneratedWholeRestartNativeActualOccurrenceAt initial stage) :
      NativeTemporalCofinalRowEventAt initial
        (⟨.finite, .finite stage occurrence⟩ :
          (nativeTemporalSource initial).toRootSource.actual.OccurrenceAt
            (.finite stage : NativeTemporalCurrent initial))
        (nativeTemporalFiniteEntry initial)
        (nativeTemporalFiniteEntry initial)
  | generated
      (receipt : GeneratedWholeRestartCanonicalWeakCofinalReceiptAt initial) :
      NativeTemporalCofinalRowEventAt initial
        (⟨.cofinal, .cofinal receipt⟩ :
          (nativeTemporalSource initial).toRootSource.actual.OccurrenceAt
            (.cofinal : NativeTemporalCurrent initial))
        (nativeTemporalCofinalEntry initial)
        (nativeTemporalCofinalEntry initial)
  | galerkin
      (radius : Nat)
      (write : NativeTemporalGalerkinWriteAt initial radius) :
      NativeTemporalCofinalRowEventAt initial
        (⟨.cofinal, .galerkin radius write⟩ :
          (nativeTemporalSource initial).toRootSource.actual.OccurrenceAt
            (.galerkin radius : NativeTemporalCurrent initial))
        (nativeTemporalCofinalEntry initial)
        (nativeTemporalCofinalEntry initial)

def nativeTemporalWriteRowSource
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    LedgerWriteRowSourceAt (nativeTemporalSource initial) (by
      intro _ occurrence targetSupport _ _
      exact NativeTemporalExactTransitionAt occurrence.1 targetSupport) :=
  { IncidenceOccurrenceAt := NativeTemporalCofinalRowEventAt initial
    compileEvolution := fun event => by
      cases event <;> exact .carried rfl HEq.rfl
    compileExact := fun event => by
      cases event <;> exact ⟨rfl⟩ }

/-- Every finite native restart occurrence generates the exact live row it
carries.  The folded ledger remains the identity, but the row is now causal
authority rather than an unselected compatibility remainder. -/
def nativeTemporalFiniteWritePatch
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (stage : Nat)
    (occurrence : GeneratedWholeRestartNativeActualOccurrenceAt initial stage) :
    FiniteGeneratedLedgerWritePatchAt
      (nativeTemporalWriteRowSource initial)
      (⟨.finite, .finite stage occurrence⟩ :
        (nativeTemporalSource initial).toRootSource.actual.OccurrenceAt
          (.finite stage : NativeTemporalCurrent initial))
      ⟨.finite⟩ :=
  .identityRemainder
    { size := 1
      sourceEntryAt := fun _ => nativeTemporalFiniteEntry initial
      targetEntryAt := fun _ => nativeTemporalFiniteEntry initial
      rowAt := fun _ =>
        (nativeTemporalWriteRowSource initial).generate
          (.finite stage occurrence) }
    { destinationIndex := fun entry =>
        some ⟨⟨0, Nat.zero_lt_succ 0⟩,
          nativeTemporalFiniteEntry_eq initial entry⟩
      originIndex := fun entry =>
        some ⟨⟨0, Nat.zero_lt_succ 0⟩,
          nativeTemporalFiniteEntry_eq initial entry⟩ }

/-- The original cofinal event writes its unique live responsibility into
the exact current patch. -/
def nativeTemporalCofinalWritePatch
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (receipt : GeneratedWholeRestartCanonicalWeakCofinalReceiptAt initial) :
    FiniteGeneratedLedgerWritePatchAt
      (nativeTemporalWriteRowSource initial)
      (⟨.cofinal, .cofinal receipt⟩ :
        (nativeTemporalSource initial).toRootSource.actual.OccurrenceAt
          (.cofinal : NativeTemporalCurrent initial))
      ⟨.cofinal⟩ :=
  .identityRemainder
    { size := 1
      sourceEntryAt := fun _ => nativeTemporalCofinalEntry initial
      targetEntryAt := fun _ => nativeTemporalCofinalEntry initial
      rowAt := fun _ =>
        (nativeTemporalWriteRowSource initial).generate
          (.generated receipt) }
    { destinationIndex := fun entry =>
        some ⟨⟨0, Nat.zero_lt_succ 0⟩,
          nativeTemporalCofinalEntry_eq initial entry⟩
      originIndex := fun entry =>
        some ⟨⟨0, Nat.zero_lt_succ 0⟩,
          nativeTemporalCofinalEntry_eq initial entry⟩ }

/-- Every actual Galerkin write renews the same exact strong-face ledger row;
the compatibility fold is not used as standing authority. -/
def nativeTemporalGalerkinWritePatch
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (radius : Nat)
    (write : NativeTemporalGalerkinWriteAt initial radius) :
    FiniteGeneratedLedgerWritePatchAt
      (nativeTemporalWriteRowSource initial)
      (⟨.cofinal, .galerkin radius write⟩ :
        (nativeTemporalSource initial).toRootSource.actual.OccurrenceAt
          (.galerkin radius : NativeTemporalCurrent initial))
      ⟨.cofinal⟩ :=
  .identityRemainder
    { size := 1
      sourceEntryAt := fun _ => nativeTemporalCofinalEntry initial
      targetEntryAt := fun _ => nativeTemporalCofinalEntry initial
      rowAt := fun _ =>
        (nativeTemporalWriteRowSource initial).generate
          (.galerkin radius write) }
    { destinationIndex := fun entry =>
        some ⟨⟨0, Nat.zero_lt_succ 0⟩,
          nativeTemporalCofinalEntry_eq initial entry⟩
      originIndex := fun entry =>
        some ⟨⟨0, Nat.zero_lt_succ 0⟩,
          nativeTemporalCofinalEntry_eq initial entry⟩ }

def nativeTemporalTerminalRowSource
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    LedgerTerminalRowSourceAt (nativeTemporalSource initial) :=
  LedgerTerminalRowSourceAt.empty _

def nativeTemporalGeneratedLedgerEvolution
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {current : NativeTemporalCurrent initial}
    (occurrence :
      (nativeTemporalSource initial).toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerEvolutionAt (nativeTemporalSource initial) occurrence := by
  rcases occurrence with ⟨support, event⟩
  change NativeTemporalRootEventAt initial current support at event
  cases event with
  | finite stage finiteOccurrence =>
      exact .nativeWrite finiteOccurrence rfl
        (nativeTemporalEmitted initial (.finite (stage + 1)))
        (nativeTemporalFiniteWritePatch initial stage
          finiteOccurrence).toLedgerWriteEvolution
  | cofinal receipt =>
      exact .nativeWrite receipt rfl
        (nativeTemporalEmitted initial (.galerkin 0))
        (nativeTemporalCofinalWritePatch initial receipt).toLedgerWriteEvolution
  | galerkin radius write =>
      exact .nativeWrite write rfl
        (nativeTemporalEmitted initial (.galerkin (radius + 1)))
        (nativeTemporalGalerkinWritePatch initial radius write).toLedgerWriteEvolution

def nativeTemporalLedgerCompiler
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    SourceNativeLedgerCompiler (nativeTemporalSource initial) where
  IncidenceTransitionAt := fun _ sourceIncidence targetIncidence =>
    NativeTemporalIncidenceTransitionAt sourceIncidence targetIncidence
  ExactTransitionAt := by
    intro _ occurrence targetSupport _ _
    exact NativeTemporalExactTransitionAt occurrence.1 targetSupport
  exact_incidence := by
    intro current occurrence targetSupport sourceEntry targetEntry exact
    exact ⟨exact.support_eq⟩
  exact_lineage := fun _ => rfl
  writeRowSource := nativeTemporalWriteRowSource initial
  terminalRowSource := nativeTemporalTerminalRowSource initial
  compile := nativeTemporalGeneratedLedgerEvolution initial
  compilePatch := by
    intro current occurrence
    rcases occurrence with ⟨support, event⟩
    change NativeTemporalRootEventAt initial current support at event
    cases event with
    | finite stage finiteOccurrence =>
        exact
          ⟨nativeTemporalFiniteWritePatch initial stage finiteOccurrence,
            rfl⟩
    | cofinal receipt =>
        exact
          ⟨nativeTemporalCofinalWritePatch initial receipt,
            rfl⟩
    | galerkin radius write =>
        exact
          ⟨nativeTemporalGalerkinWritePatch initial radius write,
            rfl⟩

def nativeTemporalLedgerSource
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    SourceNativeLedgerSource (N initial) (V initial) where
  source := nativeTemporalSource initial
  ledgerCompiler := nativeTemporalLedgerCompiler initial

/-- The original finite responder, true-cofinal event, and Galerkin PDE
writes are one source and one ledger root. -/
def nativeTemporalRoot
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    SourceNativeLedgerRootClosure (N initial) (V initial) where
  source := nativeTemporalLedgerSource initial
  emitted := nativeTemporalEmitted initial
  compiler_commutes := by
    intro current
    cases current <;> rfl

/-! ## Source-fixed temporal cofaces -/

private theorem nativeTemporalCofinalStrongFaceFailureAt_subsingleton
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    Subsingleton (NativeTemporalCofinalStrongFaceFailureAt initial) := by
  constructor
  rintro ⟨leftFailure, leftTail, leftPDE, leftPair⟩
    ⟨rightFailure, rightTail, rightPDE, rightPair⟩
  congr

private theorem nativeTemporalOpenAt_subsingleton
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (support : NativeTemporalSupport)
    (responsibility : NativeTemporalResponsibility) :
    Subsingleton (NativeTemporalOpenAt initial support responsibility) := by
  constructor
  intro left right
  cases left with
  | finite => cases right; rfl
  | cofinal leftFailure =>
      cases right with
      | cofinal rightFailure =>
          congr
          exact
            (nativeTemporalCofinalStrongFaceFailureAt_subsingleton
              initial).elim leftFailure rightFailure

private theorem nativeTemporalOpenResponsibilityAt_subsingleton
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (support : NativeTemporalSupport) :
    Subsingleton (OpenResponsibilityAt (N initial) support) := by
  constructor
  rintro ⟨left, leftOpen⟩ ⟨right, rightOpen⟩
  cases leftOpen with
  | finite => cases rightOpen; rfl
  | cofinal leftFailure =>
      cases rightOpen with
      | cofinal rightFailure =>
          congr
          exact
            (nativeTemporalCofinalStrongFaceFailureAt_subsingleton
              initial).elim leftFailure rightFailure

/-- The original temporal ledger has one exact live row at each support, so
its source-fixed restructuring law is the identity law. -/
private def nativeTemporalRestructuringLaw
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    SourceNativeLedgerRestructuringLaw (nativeTemporalSource initial) :=
  identityOnlyWorldLedgerRestructuringLaw
    (nativeTemporalSource initial) .finite
    (nativeTemporalOpenAt_subsingleton initial)

private def nativeTemporalRestructuringCertification
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {current : NativeTemporalCurrent initial}
    (occurrence :
      (nativeTemporalSource initial).toRootSource.actual.OccurrenceAt
        current) :
    SourceNativeLedgerRestructuringCertificationAt
      (nativeTemporalRestructuringLaw initial)
      ((nativeTemporalLedgerCompiler initial).compile occurrence) := by
  rcases occurrence with ⟨support, event⟩
  change NativeTemporalRootEventAt initial current support at event
  cases event <;>
    exact ExactLedgerRestructuringCertificationAt.ofInjective
      (fun left right _ =>
        (nativeTemporalOpenResponsibilityAt_subsingleton
          initial _).elim left right)
      (fun left right _ =>
        (nativeTemporalOpenResponsibilityAt_subsingleton
          initial _).elim left right)

/-- Restructuring authority is attached to the existing temporal compiler;
it does not create another emitter or another ledger root. -/
private def nativeTemporalRestructuringCompiler
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    SourceNativeRestructuringLedgerCompiler
      (nativeTemporalSource initial) where
  ledgerCompiler := nativeTemporalLedgerCompiler initial
  restructuringLaw := nativeTemporalRestructuringLaw initial
  certifyRestructuring := nativeTemporalRestructuringCertification initial

private def nativeTemporalRestructuringSource
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    SourceNativeRestructuringLedgerSource (N initial) (V initial) where
  source := nativeTemporalSource initial
  compiler := nativeTemporalRestructuringCompiler initial

/-- The base temporal root exposes its canonical whole-ledger readout.
Operational and U8 inventories install this coordinate injectively when they
extend the same source-owned projection law. -/
private def nativeTemporalProjectionLaw
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    SourceNativeProjectionLaw
      (nativeTemporalRestructuringSource initial).toLedgerSource where
  Projection := PUnit
  ActiveAt := fun _ {_current} _ => PUnit
  InactiveAt := fun _ {_current} _ => PEmpty
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun _ {_current} occurrence _ =>
    SourceNativeLedgerEvolutionAt (nativeTemporalSource initial) occurrence
  project := fun _ {_current} occurrence _ =>
    (nativeTemporalLedgerCompiler initial).compile occurrence

private def nativeTemporalAuthoritySource
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    SourceNativeAuthoritySource (N initial) (V initial) where
  restructuringSource := nativeTemporalRestructuringSource initial
  eventInventoryAdmission :=
    .reflOfNoFaithfulTerminal (nativeTemporalRestructuringSource initial)
      (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := .rootSemantic (N initial)
  projectionLaw := nativeTemporalProjectionLaw initial

/-- Authoritative projection inventory of the original temporal root.  Its
ledger-root erasure is definitionally the existing `nativeTemporalRoot`. -/
def nativeTemporalAuthoritativeRoot
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    SourceNativeAuthoritativeRootClosure (N initial) (V initial) where
  source := nativeTemporalAuthoritySource initial
  emitted := nativeTemporalEmitted initial
  compiler_commutes := by
    intro current
    cases current <;> rfl

@[simp] theorem nativeTemporalAuthoritativeRoot_toLedgerRoot
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    (nativeTemporalAuthoritativeRoot initial).toLedgerRoot =
      nativeTemporalRoot initial :=
  rfl

private theorem nativeTemporalFaithfulTerminalAt_isEmpty
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (current : NativeTemporalCurrent initial) :
    IsEmpty ((V initial).FaithfulTerminalAt current) := by
  refine ⟨?_⟩
  intro terminal
  exact nomatch terminal

/-- Living-root view of the same authoritative source.  Its vocabulary has
no local terminal constructor, so every temporal visit is answered by the
existing whole-ledger compiler. -/
def nativeTemporalLivingRoot
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    SourceNativeLivingRootClosure (N initial) (V initial) :=
  (nativeTemporalAuthoritativeRoot initial).toLivingWithoutFaithfulTerminal
    (nativeTemporalFaithfulTerminalAt_isEmpty initial)

@[simp] theorem nativeTemporalLivingRoot_toAuthoritativeRoot
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    (nativeTemporalLivingRoot initial).toAuthoritativeRoot =
      nativeTemporalAuthoritativeRoot initial :=
  rfl

def nativeTemporalProductiveHistory
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    ProductiveFiniteRootHistoryAt (nativeTemporalRoot initial) where
  currentAt := fun stage => .finite stage
  initial_eq := rfl
  next_eq := fun _stage => rfl

/-- The finite effect row is selected by the same source patch that folds the
world ledger; it is not an identity-remainder readout. -/
def nativeTemporalFiniteSourceEntryRow
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (stage : Nat) :
    SourceNativeFiniteLedgerPatchGeneratedEntryAt
      (nativeTemporalSource initial)
      (nativeTemporalLedgerCompiler initial).ExactTransitionAt
      (nativeTemporalWriteRowSource initial)
      (nativeTemporalTerminalRowSource initial)
      ((nativeTemporalLedgerCompiler initial).compile
        (nativeTemporalEmitted initial (.finite stage)))
      ((nativeTemporalLedgerCompiler initial).compilePatch
        (nativeTemporalEmitted initial (.finite stage)))
      (nativeTemporalFiniteEntry initial) :=
  (sourceNativeFiniteLedgerPatchGeneratedEntry?
    (nativeTemporalSource initial)
    (nativeTemporalLedgerCompiler initial).ExactTransitionAt
    (nativeTemporalWriteRowSource initial)
    (nativeTemporalTerminalRowSource initial)
    ((nativeTemporalLedgerCompiler initial).compile
      (nativeTemporalEmitted initial (.finite stage)))
    ((nativeTemporalLedgerCompiler initial).compilePatch
      (nativeTemporalEmitted initial (.finite stage)))
    (nativeTemporalFiniteEntry initial)).get (by rfl)

/-- Exact true-cofinal current selected by the original source law. -/
def nativeTemporalCofinalVisit
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    SourceNativeCofinalVisitAt (nativeTemporalRoot initial) :=
  (nativeTemporalProductiveHistory initial).generatedCofinalVisit?
      (fun _emitted_eq _index => rfl) |>.get (by rfl)

/-- The boundary visit carries the original root's canonical weak cofinal
receipt; it is not selected from an ambient inhabited event family. -/
@[simp] theorem nativeTemporalCofinalVisit_event
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    (nativeTemporalCofinalVisit initial).event =
      sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial :=
  rfl

/-- Original-root cofinal authority retaining the complete admitted source,
projection inventory and law epoch. -/
def nativeTemporalCofinalVisitAuthority
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    SourceNativeAuthoritativeTemporalEvolutionAt
      (nativeTemporalAuthoritativeRoot initial)
      (.cofinal (nativeTemporalCofinalVisit initial)) :=
  (nativeTemporalAuthoritativeRoot initial).authoritativeEvolutionAt
    (.cofinal (nativeTemporalCofinalVisit initial))

/-- The living compiler's source-generated next current at the original
cofinal visit. -/
def nativeTemporalCofinalNextCurrent
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    SourceNativeAuthoritativeRootCurrentAt (N initial) :=
  (nativeTemporalLivingRoot initial).generatedNextCurrentAt
    (.cofinal (nativeTemporalCofinalVisit initial))

def nativeTemporalCofinalWrite
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    SourceNativeLedgerEvolutionAt
      (nativeTemporalSource initial)
      (nativeTemporalEmitted initial .cofinal) :=
  .nativeWrite
    (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial) rfl
    (nativeTemporalEmitted initial (.galerkin 0))
    (nativeTemporalCofinalWritePatch initial
      (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt
        initial)).toLedgerWriteEvolution

theorem nativeTemporalCofinalAuthority_generates_write
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    (nativeTemporalCofinalVisitAuthority initial).toLedgerReadout.wholeLedgerWriteBack =
      nativeTemporalCofinalWrite initial := by
  rfl

theorem nativeTemporalCofinalVisit_answer_eq
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    (nativeTemporalRoot initial).generatedLedgerAt .cofinal =
      nativeTemporalCofinalWrite initial := by
  rfl

theorem nativeTemporalCofinalNextCurrent_eq
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    (nativeTemporalCofinalNextCurrent initial).visit.current =
      (.galerkin 0 : NativeTemporalCurrent initial) := by
  rfl

/-- The original cofinal compiler generates the exact live responsibility
row used by every downstream boundary consumer. -/
def nativeTemporalCofinalEntryRow
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    (nativeTemporalCofinalVisitAuthority initial).toLedgerReadout.GeneratedEntryRowAt
      (nativeTemporalCofinalEntry initial) :=
  ((nativeTemporalCofinalVisitAuthority initial).toLedgerReadout.canonicalGeneratedEntryRow?
      (nativeTemporalCofinalEntry initial)).get (by rfl)

/-- The exact cofinal whole write carries the complete strong-face
responsibility into the first Galerkin current. -/
theorem nativeTemporalCofinalWrite_targetEntry_eq
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    (((nativeTemporalCofinalWritePatch initial
      (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial)).toLedgerWriteEvolution).destination
          (nativeTemporalCofinalEntry initial)).1 =
      nativeTemporalCofinalEntry initial := by
  rfl

theorem nativeTemporalCofinalWrite_targetFailure_eq
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    nativeTemporalCofinalEntryStrongFaceFailure initial
      (((nativeTemporalCofinalWritePatch initial
        (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial)).toLedgerWriteEvolution).destination
            (nativeTemporalCofinalEntry initial)).1 =
      nativeTemporalCofinalStrongFaceFailure initial := by
  rw [nativeTemporalCofinalWrite_targetEntry_eq]
  exact
    (nativeTemporalCofinalStrongFaceFailureAt_subsingleton initial).elim
      _ _

theorem nativeTemporalCofinalWrite_target_strongFaceFails
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    ∀ _elapsedBounded : BddAbove (Set.range (elapsedTime initial)),
      ∀ endpoint : ComplexVorticityHilbertState,
        ¬ Tendsto
          (fun index => (run initial index).contact.physicalState)
          atTop (nhds endpoint) := by
  exact
    (nativeTemporalCofinalEntryStrongFaceFailure initial
      (((nativeTemporalCofinalWritePatch initial
        (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial)).toLedgerWriteEvolution).destination
          (nativeTemporalCofinalEntry initial)).1).fails

/-- The same exact cofinal whole-ledger destination carries the source-fixed
high-frequency failure law.  A bounded analytic fibre only instantiates this
law; it does not create the entry, occurrence, or successor. -/
theorem nativeTemporalCofinalWrite_target_highFrequencyTailDiverges
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    ∀ _elapsedBounded : BddAbove (Set.range (elapsedTime initial)),
      ∀ radius : Nat,
        Tendsto
          (fun index =>
            restartPhysicalHighFrequencyTailMass initial index radius)
          atTop atTop := by
  exact
    (nativeTemporalCofinalEntryStrongFaceFailure initial
      (((nativeTemporalCofinalWritePatch initial
        (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial)).toLedgerWriteEvolution).destination
          (nativeTemporalCofinalEntry initial)).1).highFrequencyTailDiverges

/-- After any finite number of actual restart transitions, both nonzero pair
coordinates at the exact cofinal whole-ledger destination remain on the
physical pair carrier or occur in that carrier's unique accumulated path
trace.  The bounded fibre only instantiates the source-fixed coordinate. -/
theorem
    nativeTemporalCofinalWrite_target_literalCrossPairEffect_survives_finitePath
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    ∀ _elapsedBounded : BddAbove (Set.range (elapsedTime initial)),
      ∀ lower : Nat,
        ∃ index : Nat,
          lower ≤ index ∧
          ∃ time : Icc (0 : Real) (run initial index).nextContact.time.1,
          ∃ output left right leftActual rightActual : IntegerWavevector,
            right ≠ left ∧
            complexCoordinateRealInner
              (actualWholeSymmetricVorticityPairVector
                (run initial index).nextContact.prefixReceipt
                output left time)
              (actualWholeSymmetricVorticityPairVector
                (run initial index).nextContact.prefixReceipt
                output right time) ≠ 0 ∧
            (leftActual = left ∨ leftActual = output - left) ∧
            (rightActual = right ∨ rightActual = output - right) ∧
            actualWholeContinuousPairVector
                (run initial index).nextContact.prefixReceipt
                output leftActual time ≠ 0 ∧
            actualWholeContinuousPairVector
                (run initial index).nextContact.prefixReceipt
                output rightActual time ≠ 0 ∧
            ∀ steps : Nat,
              (wholeRestartSplicedPairOccurrenceTable
                    initial index time steps output leftActual ≠ 0 ∨
                ((generatedWholeRestartSplicedPairOccurrenceEffectiveProcess
                    initial index time).pathTrace 0 steps)
                  0 output leftActual ≠ 0) ∧
              (wholeRestartSplicedPairOccurrenceTable
                    initial index time steps output rightActual ≠ 0 ∨
                ((generatedWholeRestartSplicedPairOccurrenceEffectiveProcess
                    initial index time).pathTrace 0 steps)
                  0 output rightActual ≠ 0) := by
  intro elapsedBounded lower
  rcases
      (nativeTemporalCofinalEntryStrongFaceFailure initial
        (((nativeTemporalCofinalWritePatch initial
          (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt
            initial)).toLedgerWriteEvolution).destination
              (nativeTemporalCofinalEntry initial)).1).literalCrossPairEffect
        elapsedBounded lower with
    ⟨index, lowerLe, time, output, left, right, leftActual, rightActual,
      rightNeLeft, interferenceNonzero, leftActualAt, rightActualAt,
      leftActualNonzero, rightActualNonzero, _leftWrite, _rightWrite⟩
  refine
    ⟨index, lowerLe, time, output, left, right, leftActual, rightActual,
      rightNeLeft, interferenceNonzero, leftActualAt, rightActualAt,
      leftActualNonzero, rightActualNonzero,
      ?_⟩
  intro steps
  exact
    ⟨actualWholeContinuousPairVector_ne_zero_future_or_pathTrace
        initial index output leftActual time steps leftActualNonzero,
      actualWholeContinuousPairVector_ne_zero_future_or_pathTrace
        initial index output rightActual time steps rightActualNonzero⟩

/-- The same exact cofinal admission retaining the complete living source,
including its terminal handoff law. -/
def nativeTemporalLivingCofinalEntryAuthority
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt
      (nativeTemporalLivingRoot initial)
      (.cofinal (nativeTemporalCofinalVisit initial))
      (nativeTemporalCofinalEntry initial) :=
  SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromCofinalRow
    (nativeTemporalLivingRoot initial)
    (nativeTemporalCofinalVisit initial)
    (nativeTemporalCofinalEntry initial)
    (nativeTemporalCofinalEntryRow initial)

/-- Every Galerkin current emits its actual trajectory and the next radius. -/
def nativeTemporalGalerkinWrite
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (radius : Nat) :
    SourceNativeLedgerEvolutionAt
      (nativeTemporalSource initial)
      (nativeTemporalEmitted initial (.galerkin radius)) :=
  .nativeWrite (sourceGeneratedNativeTemporalGalerkinWrite initial radius) rfl
    (nativeTemporalEmitted initial (.galerkin (radius + 1)))
    (nativeTemporalGalerkinWritePatch initial radius
      (sourceGeneratedNativeTemporalGalerkinWrite initial radius)).toLedgerWriteEvolution

theorem nativeTemporalRoot_generated_galerkinWrite
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (radius : Nat) :
    (nativeTemporalRoot initial).generatedLedgerAt (.galerkin radius) =
      nativeTemporalGalerkinWrite initial radius := by
  rfl

/-- Source-generated post-cofinal history at each Galerkin radius. -/
def nativeTemporalGalerkinHistory
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    (radius : Nat) →
      SourceNativePostCofinalReachableAt
        (nativeTemporalRoot initial) (.galerkin radius)
  | 0 =>
      .step
        (.cofinal (nativeTemporalCofinalVisit initial))
        (by rfl)
  | radius + 1 => .step (nativeTemporalGalerkinHistory initial radius) (by rfl)

/-- Source-generated post-cofinal visit at each Galerkin radius.  The
recursion advances only by the existing root compiler. -/
def nativeTemporalGalerkinVisit
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (radius : Nat) :
    SourceNativeTemporalVisitAt (nativeTemporalRoot initial) :=
  ⟨.galerkin radius, .postCofinal
    (nativeTemporalGalerkinHistory initial radius)⟩

@[simp] theorem nativeTemporalGalerkinVisit_current
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (radius : Nat) :
    (nativeTemporalGalerkinVisit initial radius).current =
      (.galerkin radius : NativeTemporalCurrent initial) :=
  rfl

/-- The exact cofinal admission is carried through successive source-owned
Galerkin whole-ledger writes on the same temporal history. -/
def nativeTemporalGalerkinEntryAuthority
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    (radius : Nat) →
      SourceNativeLivingTemporalCausalEntryAuthorityAt
        (nativeTemporalLivingRoot initial)
        (nativeTemporalGalerkinVisit initial radius)
        (nativeTemporalCofinalEntry initial)
  | 0 =>
      by
        let next_eq :
            ((nativeTemporalLivingRoot initial).toAuthoritativeRoot.toRoot
              |>.evolutionAt (nativeTemporalCofinalVisit initial).current
              ).nextCurrent? = some (.galerkin 0) := by
          rfl
        let authority :=
          (nativeTemporalLivingCofinalEntryAuthority initial).next
            next_eq
        have entry_eq :
            ((nativeTemporalLivingRoot initial).toAuthoritativeRoot.toLedgerRoot
              |>.canonicalTargetEntryAtNext next_eq
                (nativeTemporalCofinalEntry initial)) =
              nativeTemporalCofinalEntry initial :=
          (nativeTemporalCofinalEntry_eq initial _).symm
        cases entry_eq
        exact authority
  | radius + 1 =>
      by
        let next_eq :
            ((nativeTemporalLivingRoot initial).toAuthoritativeRoot.toRoot
              |>.evolutionAt (.galerkin radius)).nextCurrent? =
                some (.galerkin (radius + 1)) := by
          rfl
        let authority :=
          (nativeTemporalGalerkinEntryAuthority initial radius).next
            next_eq
        have entry_eq :
            ((nativeTemporalLivingRoot initial).toAuthoritativeRoot.toLedgerRoot
              |>.canonicalTargetEntryAtNext next_eq
                (nativeTemporalCofinalEntry initial)) =
              nativeTemporalCofinalEntry initial :=
          (nativeTemporalCofinalEntry_eq initial _).symm
        cases entry_eq
        exact authority

/-- The cofinal compiler answers the exact strong-face responsibility and
generates the first Galerkin current in one causal token. -/
noncomputable def nativeTemporalCofinalCausalAnswerAndNext
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    SourceNativeLivingCausalEntryAnswerAndNextAt
      (nativeTemporalLivingRoot initial)
      (.cofinal (nativeTemporalCofinalVisit initial))
      (nativeTemporalCofinalEntry initial)
      (nativeTemporalLivingCofinalEntryAuthority initial) :=
  (nativeTemporalLivingRoot initial).generatedCausalEntryAnswerAndNextAt
    (.cofinal (nativeTemporalCofinalVisit initial))
    (nativeTemporalCofinalEntry initial)
    (nativeTemporalLivingCofinalEntryAuthority initial)

@[simp] theorem nativeTemporalCofinalCausalAnswer_payload_eq_targetReadout
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    (nativeTemporalCofinalCausalAnswerAndNext initial).answer =
      (nativeTemporalGalerkinEntryAuthority initial 0).toLedgerReadout := by
  rfl

/-- Independent physical consumer of every Galerkin write: its trajectory
solves the exact finite Galerkin vorticity equation on `[0,1]`. -/
theorem sourceGeneratedNativeTemporalGalerkinWrite_physical
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (radius : Nat) :
    ∀ time ∈ Set.Icc (0 : Real) 1,
      HasDerivAt
          (sourceGeneratedNativeTemporalGalerkinWrite initial radius).trajectory
          (finiteStateVorticityGenerator
            (wholeRestartModes radius) nu.coeff
            ((sourceGeneratedNativeTemporalGalerkinWrite
              initial radius).trajectory time))
          time ∧
        (∀ wave, wave ∉ wholeRestartModes radius →
          (sourceGeneratedNativeTemporalGalerkinWrite
            initial radius).trajectory time wave = 0) ∧
        (∀ wave,
          complexWavevector wave ⬝ᵥ
            (sourceGeneratedNativeTemporalGalerkinWrite
              initial radius).trajectory time wave = 0) ∧
        FiniteStateFourierReality
          ((sourceGeneratedNativeTemporalGalerkinWrite
            initial radius).trajectory time) :=
  (sourceGeneratedNativeTemporalGalerkinWrite initial radius).physical

/-- Every finite Fourier observer of the old actual contact sequence becomes
the exact initial row of the Galerkin write on the same cofinal subsequence. -/
private theorem sourceGeneratedNativeTemporalGalerkinWrite_initial_row_tendsto
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (radius : Nat)
    (wave : IntegerWavevector)
    (waveMem : wave ∈ wholeRestartModes radius) :
    Tendsto
      (fun index =>
        (run initial
          ((sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt
            initial).subsequence index)).contact.physicalState wave)
      atTop
      (nhds
        ((sourceGeneratedNativeTemporalGalerkinWrite
          initial radius).trajectory 0 wave)) := by
  let receipt :=
    sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial
  have waveNe : wave ≠ 0 := fun waveZero =>
    zero_not_mem_puncturedIntegerWaveFrequencyCube radius
      (waveZero ▸ waveMem)
  let nonzeroWave : NonzeroIntegerWavevector := ⟨wave, waveNe⟩
  have velocityRowTendsto :
      Tendsto
        (fun index coordinate =>
          wholeRestartContactVelocityState initial
            (receipt.subsequence index) nonzeroWave coordinate)
        atTop
        (nhds (fun coordinate =>
          receipt.velocityEndpoint nonzeroWave coordinate)) := by
    rw [tendsto_pi_nhds]
    intro coordinate
    exact velocityWeakTendsto_coordinate
      (fun index => wholeRestartContactVelocityState initial
        (receipt.subsequence index))
      receipt.velocityEndpoint receipt.velocityWeak_tendsto
      nonzeroWave coordinate
  have curlContinuous : Continuous (fourierCurlCoefficient wave) := by
    unfold fourierCurlCoefficient
    fun_prop
  have curlTendsto :=
    (curlContinuous.tendsto
      (fun coordinate => receipt.velocityEndpoint nonzeroWave coordinate)).comp
      velocityRowTendsto
  convert curlTendsto using 1
  · funext index
    change
      (run initial (receipt.subsequence index)).contact.physicalState wave =
        fourierCurlCoefficient wave
          (biotSavartVelocityCoefficient wave
            ((run initial
              (receipt.subsequence index)).contact.physicalState wave))
    exact
      (fourierCurlCoefficient_biotSavartVelocityCoefficient_of_transverse
        wave
        ((run initial
          (receipt.subsequence index)).contact.physicalState wave)
        waveNe
        ((run initial
          (receipt.subsequence index)).contact.transverse wave)).symm
  · apply congrArg nhds
    rw [(sourceGeneratedNativeTemporalGalerkinWrite
      initial radius).initial,
      wholeRestartVelocityEndpointFiniteVorticityInitialState_apply,
      if_pos waveMem,
      wholeRestartVelocityEndpointFiniteProjection_apply,
      if_pos waveMem,
      wholeRestartVelocityEndpointCoefficient_of_ne]

/-- Every registered finite-window observer commutes with the original
contact sequence and the Galerkin initial write. -/
theorem sourceGeneratedNativeTemporalGalerkinWrite_initial_observer_tendsto
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (radius : Nat) :
    Tendsto
      (fun index =>
        complexSharpSupportProjection (wholeRestartModes radius)
          (run initial
            ((sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt
              initial).subsequence index)).contact.physicalState)
      atTop
      (nhds
        ((sourceGeneratedNativeTemporalGalerkinWrite
          initial radius).trajectory 0)) := by
  let modes := wholeRestartModes radius
  let target :=
    (sourceGeneratedNativeTemporalGalerkinWrite initial radius).trajectory 0
  let finiteTarget : FiniteModeVorticityCarrier modes := fun wave =>
    target wave.1
  have restrictedTendsto :
      Tendsto
        (fun index => finiteModeRestriction modes
          (run initial
            ((sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt
              initial).subsequence index)).contact.physicalState)
        atTop
        (nhds finiteTarget) := by
    apply tendsto_pi_nhds.mpr
    intro wave
    exact sourceGeneratedNativeTemporalGalerkinWrite_initial_row_tendsto
      initial radius wave.1 wave.2
  have extendedTendsto :=
    (finiteModeExtension modes).continuous.tendsto finiteTarget
      |>.comp restrictedTendsto
  convert extendedTendsto using 1
  · funext index
    simpa only [Function.comp_apply, modes] using
      (finiteModeExtension_restriction (wholeRestartModes radius)
        (run initial
          ((sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt
            initial).subsequence index)).contact.physicalState).symm
  · apply congrArg nhds
    symm
    change finiteModeExtension modes (finiteModeRestriction modes target) =
      target
    rw [finiteModeExtension_restriction]
    apply lp.ext
    funext wave
    by_cases waveMem : wave ∈ modes
    · simp [complexSharpSupportProjection_apply, waveMem]
    · rw [complexSharpSupportProjection_apply, if_neg waveMem]
      change 0 = target wave
      rw [show target =
          wholeRestartVelocityEndpointFiniteVorticityInitialState radius
            (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt
              initial).velocityEndpoint by
        exact (sourceGeneratedNativeTemporalGalerkinWrite
          initial radius).initial]
      exact (wholeRestartVelocityEndpointFiniteVorticityInitialState_supported
        radius
        (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt
          initial).velocityEndpoint wave (by simpa [modes] using waveMem)).symm

/-! ## The conditional analytic accumulation contact -/

/-- Actual analytic contact generated by the bounded finite history.  Its time is fixed to the
supremum of that history, and convergence is derived from the native strict time advance. -/
structure GeneratedNativeAccumulationEventAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) : Type where
  time : ℝ
  time_eq : time = wholeRestartVelocityAccumulationTime initial
  elapsedBounded : BddAbove (Set.range (elapsedTime initial))
  elapsed_tendsto : Tendsto (elapsedTime initial) atTop (nhds time)

/-- The bounded generated history itself supplies the unique analytic boundary contact. -/
def generatedNativeAccumulationEvent
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    GeneratedNativeAccumulationEventAt initial where
  time := wholeRestartVelocityAccumulationTime initial
  time_eq := rfl
  elapsedBounded := elapsedBounded
  elapsed_tendsto :=
    tendsto_atTop_ciSup (elapsedTime_strictMono initial).monotone elapsedBounded

/-! The object below is only the analytic occurrence opened inside the local
`elapsedBounded` fibre.  The original root's effect-bearing cofinal authority
is generated independently by `nativeTemporalCofinalVisitAuthority`. -/

structure GeneratedNativeAccumulationConditionalOccurrenceAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) : Type where
  event : GeneratedNativeAccumulationEventAt initial

/-- Canonical analytic occurrence generated in the local bounded fibre. -/
def generatedNativeAccumulationConditionalOccurrence
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    GeneratedNativeAccumulationConditionalOccurrenceAt initial :=
  ⟨generatedNativeAccumulationEvent initial elapsedBounded⟩

/-- Public conditional contact tying the analytic limit to the already generated
finite history.  It is a readout inside the bounded fibre, not a second root
occurrence and not authority for a boundary outcome. -/
structure SourceGeneratedNativeAccumulationContactAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) : Type 2 where
  boundaryOccurrence :
    GeneratedNativeAccumulationConditionalOccurrenceAt initial
  boundaryOccurrence_eq : boundaryOccurrence =
    generatedNativeAccumulationConditionalOccurrence initial elapsedBounded

/-- Generate the accumulation contact only after the finite source process and boundedness are both
available.  The construction does not inspect any endpoint or boundary disposition. -/
def sourceGeneratedNativeAccumulationContact
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    SourceGeneratedNativeAccumulationContactAt initial elapsedBounded where
  boundaryOccurrence :=
    generatedNativeAccumulationConditionalOccurrence initial elapsedBounded
  boundaryOccurrence_eq := rfl

end

end ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
end NavierStokes
end SaturationMonoid
