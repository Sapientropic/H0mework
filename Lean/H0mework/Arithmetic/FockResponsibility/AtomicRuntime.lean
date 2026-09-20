import H0mework.Arithmetic.GoldbachDynamics.Runtime
import H0mework.Realization.Faces.ProjectionCoface
import H0mework.Arithmetic.FockDynamics.AtomicDynamics

/-!
# Atomic particle dynamics installed on the exact Goldbach runtime occurrence

The operational Goldbach runtime already owns the emitted occurrence, even
sector and canonical split.  This projection coface makes the generated
physical current and its terminal-or-decay event a named face of that same
root.  The underlying source, compiler, whole ledger, law surface and next
remain unchanged.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalArithmeticState
namespace ParticleWaveFockAtomicDynamicsRuntime

open ArithmeticGeneration
open CanonicalUnitArithmeticEffectiveFactorRepairOrbitProducer
open CanonicalUnitArithmeticExactOccurrenceOperationalFactorDecayProducer
open CanonicalUnitArithmeticOperationalGoldbachRuntime
open CanonicalUnitArithmeticRoot
open ParticleWaveFock
open ParticleWaveFockAtomicProcess

noncomputable section

abbrev BaseAuthoritySource :=
  CanonicalUnitArithmeticOperationalGoldbachRuntime.authoritySource

abbrev BaseLedgerSource := BaseAuthoritySource.restructuringSource.toLedgerSource

def scanIndex (current : Current) : Nat := current.cardinalShadow

/-- Exact occurrence-indexed physical current and source dynamics. -/
structure RootGeneratedAtomicDynamicsAt
    (current : Current)
    (occurrence :
      BaseLedgerSource.source.toRootSource.actual.OccurrenceAt current)
    (indexInRange : 1 ≤ scanIndex current) : Type where
  private mk ::
  sourceOccurrence :
    BaseLedgerSource.source.toRootSource.actual.OccurrenceAt current
  sourceOccurrence_eq : sourceOccurrence = occurrence
  operational :
    RootGeneratedOperationalGoldbachCurrentAt current occurrence indexInRange
  operational_eq : operational =
    generateOperationalGoldbachCurrent current occurrence indexInRange
  physicalCurrent : PhysicalCurrentAt (scanIndex current)
  physicalCurrent_eq : physicalCurrent =
    canonicalCurrent (scanIndex current) indexInRange
  split_eq_operational :
    physicalCurrent.current = operational.factorDecay.source
  particleState_eq_operational :
    physicalCurrent.particleState =
      splitParticleState operational.factorDecay.source
  atomicMeasurement_eq_operational :
    physicalCurrent.measurement =
      atomicJointMeasurement operational.factorDecay.source
  dynamics : GeneratedDynamicsAt physicalCurrent
  dynamics_eq : dynamics = generateDynamics physicalCurrent
  targetOccurrence : operational.factorDecay.occurrence =
    operational.targetOccurrence
  targetRoot :
    operational.targetOccurrence.root.rootOccurrence = occurrence

def generateAtomicDynamics
    (current : Current)
    (occurrence :
      BaseLedgerSource.source.toRootSource.actual.OccurrenceAt current)
    (indexInRange : 1 ≤ scanIndex current) :
    RootGeneratedAtomicDynamicsAt current occurrence indexInRange := by
  let operational := generateOperationalGoldbachCurrent
    current occurrence indexInRange
  let physicalCurrent := canonicalCurrent (scanIndex current) indexInRange
  exact
    { sourceOccurrence := occurrence
      sourceOccurrence_eq := rfl
      operational := operational
      operational_eq := rfl
      physicalCurrent := physicalCurrent
      physicalCurrent_eq := rfl
      split_eq_operational := rfl
      particleState_eq_operational := rfl
      atomicMeasurement_eq_operational := rfl
      dynamics := generateDynamics physicalCurrent
      dynamics_eq := rfl
      targetOccurrence := rfl
      targetRoot := operational.targetRoot }

/-- The existing runtime current decides applicability. -/
def atomicProjectionLaw : SourceNativeProjectionLaw BaseLedgerSource where
  Projection := PUnit
  ActiveAt := fun _ {current} _occurrence => PLift (1 ≤ scanIndex current)
  InactiveAt := fun _ {current} _occurrence => PLift (scanIndex current = 0)
  classify := by
    intro projection current occurrence
    cases current with
    | empty => exact .inr ⟨rfl⟩
    | next prior =>
        exact .inl ⟨by
          unfold scanIndex UnitHistory.cardinalShadow
          omega⟩
  PayloadAt := fun _ {current} occurrence active =>
    RootGeneratedAtomicDynamicsAt current occurrence active.down
  project := fun _ {current} occurrence active =>
    generateAtomicDynamics current occurrence active.down

def authoritySource : SourceNativeAuthoritySource N V :=
  BaseAuthoritySource.withProjectionCoface atomicProjectionLaw

def atomicInstallation : SourceNativeProjectionLaw.InstallationAt
    atomicProjectionLaw authoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface
    BaseAuthoritySource atomicProjectionLaw

def operationalInstallation : SourceNativeProjectionLaw.InstallationAt
    CanonicalUnitArithmeticOperationalGoldbachRuntime.operationalProjectionLaw
      authoritySource.projectionLaw :=
  CanonicalUnitArithmeticOperationalGoldbachRuntime.operationalInstallation.trans
    (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
      BaseAuthoritySource atomicProjectionLaw)

def particleWaveInstallation : SourceNativeProjectionLaw.InstallationAt
    ParticleWaveFockRuntime.projectionLaw authoritySource.projectionLaw :=
  CanonicalUnitArithmeticOperationalGoldbachRuntime.particleWaveInstallation.trans
    (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
      BaseAuthoritySource atomicProjectionLaw)

def authoritativeRoot : SourceNativeAuthoritativeRootClosure N V where
  source := authoritySource
  emitted := CanonicalUnitArithmeticRoot.emitted
  compiler_commutes :=
    CanonicalUnitArithmeticRoot.authoritativeRoot.compiler_commutes

def livingRoot : SourceNativeLivingRootClosure N V :=
  authoritativeRoot.toLivingWithoutFaithfulTerminal <| fun _ =>
    ⟨fun terminal => nomatch terminal⟩

def temporalVisit (depth : Nat) :
    SourceNativeTemporalVisitAt authoritativeRoot.toLedgerRoot :=
  .finite (CanonicalUnitArithmeticRoot.finiteVisit depth)

def temporalDepth?
    (current : SourceNativeLivingRootCurrentAt N) : Option Nat :=
  match current.visit.history with
  | .finite history => some (ProductiveFiniteRootHistoryAt.causalDepth history)
  | .postCofinal _ => none

theorem temporalVisit_depth (depth : Nat) :
    temporalDepth? ⟨V, livingRoot, temporalVisit depth⟩ = some depth :=
  CanonicalUnitArithmeticRoot.temporalVisit_depth depth

abbrev process : SourceNativeLivingRootProcess N where
  State := Nat
  stateAt := fun depth => ⟨V, livingRoot, temporalVisit depth⟩
  stateAt_injective := by
    intro left right equality
    have depthEquality := congrArg temporalDepth? equality
    rw [temporalVisit_depth left, temporalVisit_depth right] at depthEquality
    exact Option.some.inj depthEquality
  initial := 0
  successorAt := fun depth => ⟨depth + 1, rfl, by rfl⟩

inductive FaceAt
  | particleWave
  | operationalGoldbach
  | atomicDynamics
  deriving DecidableEq

abbrev runtimeFacade : SourceNativeLivingRuntimeFacade N where
  process := process
  FaceAt := fun _runtime => FaceAt
  componentAt := fun _runtime face =>
    match face with
    | .particleWave => ParticleWaveFockRuntime.projectionLaw
    | .operationalGoldbach =>
        CanonicalUnitArithmeticOperationalGoldbachRuntime.operationalProjectionLaw
    | .atomicDynamics => atomicProjectionLaw
  installationAt := fun _runtime face =>
    match face with
    | .particleWave => particleWaveInstallation
    | .operationalGoldbach => operationalInstallation
    | .atomicDynamics => atomicInstallation
  projectionAt := fun _runtime face =>
    match face with
    | .particleWave => PUnit.unit
    | .operationalGoldbach => PUnit.unit
    | .atomicDynamics => PUnit.unit

def runtimeSeed : LivingRuntimeState runtimeFacade.process :=
  runtimeFacade.seed

def runtimeAt (depth : Nat) : LivingRuntimeState runtimeFacade.process :=
  runtimeSeed.advance depth

theorem runtimeAt_state (depth : Nat) :
    (runtimeAt depth).state = depth := by
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      change (runtimeAt depth).state + 1 = depth + 1
      exact congrArg (fun value : Nat => value + 1) inductionHypothesis

theorem runtimeAt_current (depth : Nat) :
    (runtimeAt depth).current.visit.current =
      UnitHistory.generate (depth + 1) := by
  change (CanonicalUnitArithmeticRoot.finiteVisit
    (runtimeAt depth).state).current = _
  rw [runtimeAt_state]
  exact CanonicalUnitArithmeticOperationalGoldbachRuntime.finiteVisit_current depth

theorem runtimeAt_scanIndex (depth : Nat) :
    scanIndex (runtimeAt depth).current.visit.current = depth + 1 := by
  rw [runtimeAt_current]
  exact UnitHistory.cardinalShadow_generate (depth + 1)

def runtimeActive (depth : Nat) :
    atomicProjectionLaw.ActiveAt PUnit.unit
      (runtimeAt depth).emittedOccurrence :=
  ⟨by rw [runtimeAt_scanIndex]; omega⟩

def runtimeAtomicPayload (depth : Nat) :
    RootGeneratedAtomicDynamicsAt
      (runtimeAt depth).current.visit.current
      (runtimeAt depth).emittedOccurrence
      (runtimeActive depth).down :=
  atomicProjectionLaw.project PUnit.unit
    (runtimeAt depth).emittedOccurrence (runtimeActive depth)

theorem runtimeReadout_is_atomic (depth : Nat) :
    runtimeFacade.readoutAt (runtimeAt depth) .atomicDynamics =
      .inl ⟨runtimeActive depth, runtimeAtomicPayload depth⟩ := by
  change atomicProjectionLaw.outcomeAt PUnit.unit
      (runtimeAt depth).emittedOccurrence = _
  unfold SourceNativeProjectionLaw.outcomeAt
  generalize classifierEq :
    atomicProjectionLaw.classify PUnit.unit
      (runtimeAt depth).emittedOccurrence = classification
  cases classification with
  | inl active =>
      have activeEq : active = runtimeActive depth := by
        apply PLift.down_injective
        exact Subsingleton.elim _ _
      cases activeEq
      rfl
  | inr inactive =>
      have impossible := inactive.down
      rw [runtimeAt_scanIndex] at impossible
      omega

theorem runtimeAtomicPayload_same_occurrence (depth : Nat) :
    (runtimeAtomicPayload depth).sourceOccurrence =
        (runtimeAt depth).current.root.toAuthoritativeRoot.toLedgerRoot.emitted
          (runtimeAt depth).current.visit.current ∧
      (runtimeAtomicPayload depth).operational.sourceOccurrence =
        (runtimeAtomicPayload depth).sourceOccurrence ∧
      (runtimeAtomicPayload depth).operational.factorDecay.occurrence.root.rootOccurrence =
        (runtimeAtomicPayload depth).sourceOccurrence := by
  exact ⟨(runtimeAtomicPayload depth).sourceOccurrence_eq,
    (runtimeAtomicPayload depth).operational.sourceOccurrence_eq.trans
      (runtimeAtomicPayload depth).sourceOccurrence_eq.symm,
    (runtimeAtomicPayload depth).operational.factorDecay.occurrenceRoot.trans
      (runtimeAtomicPayload depth).sourceOccurrence_eq.symm⟩

theorem coversAt_factorizes
    (runtime : LivingRuntimeState runtimeFacade.process)
    (face : runtimeFacade.FaceAt runtime) :
    runtimeFacade.process.toAnswerNextCausalWorld.emitted
          (ULift.up runtime.state) = ULift.up runtime.tick.generated ∧
      runtime.tick.generated.occurrence =
        runtime.current.root.toAuthoritativeRoot.toLedgerRoot.emitted
          runtime.current.visit.current ∧
      HEq runtime.tick.generated.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          runtime.current.visit.current) ∧
      HEq (runtimeFacade.readoutAt runtime face)
        (runtime.tick.generated.projectionOutcome
          ((runtimeFacade.installationAt runtime face).embed
            (runtimeFacade.projectionAt runtime face))) ∧
      runtime.tick.nextCurrent =
        runtimeFacade.process.stateAt
          (runtimeFacade.process.successor runtime.state) :=
  runtimeFacade.readoutAt_factorizes runtime face

end

end ParticleWaveFockAtomicDynamicsRuntime
end CanonicalArithmeticState
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
