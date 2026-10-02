import H0mework.Versions.R2.Arithmetic.GoldbachDynamics.ExactOperationalFace
import H0mework.Versions.R2.Realization.Faces.ProjectionCoface
import H0mework.Versions.R2.Arithmetic.FockDynamics.RootRuntime

/-!
# Canonical operational Goldbach runtime

The canonical arithmetic runtime depth generates the classical-range target
index `depth + 1`.  At that exact root occurrence a source projection emits
the pointwise additive disposition together with the event-indexed
repair/emission residual process.  No caller selects an index, first failure,
factor channel, target or future runtime state.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticOperationalGoldbachRuntime

open ArithmeticGeneration
open CanonicalUnitArithmeticEffectiveAdditiveProducer
open CanonicalUnitArithmeticEffectiveFactorRepairOrbitProducer
open CanonicalUnitArithmeticExactOccurrenceAdditiveProducer
open CanonicalUnitArithmeticExactOccurrenceOperationalFactorDecayProducer
open CanonicalUnitArithmeticFullFactorEmissionProducer
open CanonicalUnitArithmeticOperationalFactorDecayProducer
open CanonicalUnitArithmeticRoot
open NoIslandNoMagic.CanonicalArithmeticState
open SourceGeneratedFiniteEventIndexedResidualProcess

noncomputable section

abbrev BaseAuthoritySource :=
  ParticleWaveFockRuntime.authoritySource

abbrev BaseLedgerSource :=
  BaseAuthoritySource.restructuringSource.toLedgerSource

def scanIndex (current : Current) : Nat :=
  current.cardinalShadow

/-- Exact operational payload at one emitted root occurrence. -/
structure RootGeneratedOperationalGoldbachCurrentAt
    (current : Current)
    (occurrence :
      BaseLedgerSource.source.toRootSource.actual.OccurrenceAt current)
    (indexInRange : 1 ≤ scanIndex current) : Type where
  private mk ::
  sourceOccurrence :
    BaseLedgerSource.source.toRootSource.actual.OccurrenceAt current
  sourceOccurrence_eq : sourceOccurrence = occurrence
  targetOccurrence : RootedAccountedUnfolding
    (ExactOccurrenceAdditivePointAt occurrence)
  targetOccurrence_eq : targetOccurrence =
    evenTargetOccurrenceAt occurrence (scanIndex current)
  additiveDisposition : EffectiveAdditiveDispositionAt (scanIndex current)
  additiveDisposition_eq : additiveDisposition =
    generatedAdditiveDisposition (scanIndex current)
  factorDecay : RootGeneratedExactOccurrenceOperationalFactorDecayAt
    occurrence (scanIndex current) indexInRange
  factorDecay_eq : factorDecay =
    CanonicalUnitArithmeticExactOccurrenceOperationalFactorDecayProducer.generate
      occurrence (scanIndex current) indexInRange
  factorDecayOccurrence : factorDecay.occurrence = targetOccurrence
  targetRoot :
    targetOccurrence.root.rootOccurrence = occurrence

def generateOperationalGoldbachCurrent
    (current : Current)
    (occurrence :
      BaseLedgerSource.source.toRootSource.actual.OccurrenceAt current)
    (indexInRange : 1 ≤ scanIndex current) :
    RootGeneratedOperationalGoldbachCurrentAt current occurrence indexInRange :=
  { sourceOccurrence := occurrence
    sourceOccurrence_eq := rfl
    targetOccurrence := evenTargetOccurrenceAt occurrence (scanIndex current)
    targetOccurrence_eq := rfl
    additiveDisposition := generatedAdditiveDisposition (scanIndex current)
    additiveDisposition_eq := rfl
    factorDecay :=
      CanonicalUnitArithmeticExactOccurrenceOperationalFactorDecayProducer.generate
        occurrence (scanIndex current) indexInRange
    factorDecay_eq := rfl
    factorDecayOccurrence := rfl
    targetRoot := evenTargetOccurrenceAt_root_is_exact
      occurrence (scanIndex current) }

/-- Runtime current owns the scan index.  The empty history is the only
inactive presentation and is unreachable from the canonical seed. -/
def operationalProjectionLaw : SourceNativeProjectionLaw BaseLedgerSource where
  Projection := PUnit
  ActiveAt := fun _ {current} _occurrence =>
    PLift (1 ≤ scanIndex current)
  InactiveAt := fun _ {current} _occurrence =>
    PLift (scanIndex current = 0)
  classify := by
    intro projection current occurrence
    cases current with
    | empty => exact .inr ⟨rfl⟩
    | next prior =>
        exact .inl ⟨by
          unfold scanIndex UnitHistory.cardinalShadow
          omega⟩
  PayloadAt := fun _ {current} occurrence active =>
    RootGeneratedOperationalGoldbachCurrentAt current occurrence active.down
  project := fun _ {current} occurrence active =>
    generateOperationalGoldbachCurrent current occurrence active.down

def authoritySource : SourceNativeAuthoritySource N V :=
  BaseAuthoritySource.withProjectionCoface operationalProjectionLaw

def operationalInstallation : SourceNativeProjectionLaw.InstallationAt
    operationalProjectionLaw authoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface
    BaseAuthoritySource operationalProjectionLaw

/-- The common particle--wave component remains installed when the
Goldbach operational face is added. -/
def particleWaveInstallation : SourceNativeProjectionLaw.InstallationAt
    ParticleWaveFockRuntime.projectionLaw authoritySource.projectionLaw :=
  ParticleWaveFockRuntime.installation.trans
    (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
      BaseAuthoritySource operationalProjectionLaw)

def authoritativeRoot : SourceNativeAuthoritativeRootClosure N V where
  source := authoritySource
  emitted := CanonicalUnitArithmeticRoot.emitted
  compiler_commutes :=
    CanonicalUnitArithmeticRoot.authoritativeRoot.compiler_commutes

def livingRoot : SourceNativeLivingRootClosure N V :=
  authoritativeRoot.toLivingWithoutFaithfulTerminal <| fun _ =>
    ⟨fun terminal => nomatch terminal⟩

def finiteVisit := CanonicalUnitArithmeticRoot.finiteVisit

def temporalVisit (depth : Nat) :
    SourceNativeTemporalVisitAt authoritativeRoot.toLedgerRoot :=
  .finite (finiteVisit depth)

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
  deriving DecidableEq

abbrev runtimeFacade : SourceNativeLivingRuntimeFacade N where
  process := process
  FaceAt := fun _runtime => FaceAt
  componentAt := fun _runtime face =>
    match face with
    | .particleWave => ParticleWaveFockRuntime.projectionLaw
    | .operationalGoldbach => operationalProjectionLaw
  installationAt := fun _runtime face =>
    match face with
    | .particleWave => particleWaveInstallation
    | .operationalGoldbach => operationalInstallation
  projectionAt := fun _runtime face =>
    match face with
    | .particleWave => PUnit.unit
    | .operationalGoldbach => PUnit.unit

def runtimeSeed : LivingRuntimeState runtimeFacade.process :=
  runtimeFacade.seed

def runtimeAt (depth : Nat) : LivingRuntimeState runtimeFacade.process :=
  runtimeSeed.advance depth

theorem finiteVisit_current (depth : Nat) :
    (finiteVisit depth).current = UnitHistory.generate (depth + 1) := by
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      change CanonicalUnitArithmeticRoot.next (finiteVisit depth).current =
        UnitHistory.generate (depth + 1 + 1)
      rw [inductionHypothesis]
      rfl

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
  change (finiteVisit (runtimeAt depth).state).current = _
  rw [runtimeAt_state, finiteVisit_current]

theorem runtimeAt_scanIndex (depth : Nat) :
    scanIndex (runtimeAt depth).current.visit.current = depth + 1 := by
  rw [runtimeAt_current]
  exact UnitHistory.cardinalShadow_generate (depth + 1)

def runtimeActive (depth : Nat) :
    operationalProjectionLaw.ActiveAt PUnit.unit
      (runtimeAt depth).emittedOccurrence :=
  ⟨by rw [runtimeAt_scanIndex]; omega⟩

def runtimeParticleWaveActive (depth : Nat) :
    ParticleWaveFockRuntime.projectionLaw.ActiveAt PUnit.unit
      (runtimeAt depth).emittedOccurrence :=
  ⟨by
    rw [show ParticleWaveFockRuntime.scanIndex
        (runtimeAt depth).current.visit.current =
          scanIndex (runtimeAt depth).current.visit.current by rfl,
      runtimeAt_scanIndex]
    omega⟩

def runtimePayload (depth : Nat) :
    RootGeneratedOperationalGoldbachCurrentAt
      (runtimeAt depth).current.visit.current
      (runtimeAt depth).emittedOccurrence
      (runtimeActive depth).down :=
  operationalProjectionLaw.project PUnit.unit
    (runtimeAt depth).emittedOccurrence (runtimeActive depth)

def runtimeParticleWavePayload (depth : Nat) :
    ParticleWaveFockRuntime.RootGeneratedParticleWaveCurrentAt
      (runtimeAt depth).current.visit.current
      (runtimeAt depth).emittedOccurrence
      (runtimeParticleWaveActive depth).down :=
  ParticleWaveFockRuntime.projectionLaw.project PUnit.unit
    (runtimeAt depth).emittedOccurrence (runtimeParticleWaveActive depth)

theorem runtimeReadout_is_particleWave (depth : Nat) :
    runtimeFacade.readoutAt (runtimeAt depth) .particleWave =
      .inl ⟨runtimeParticleWaveActive depth,
        runtimeParticleWavePayload depth⟩ := by
  change ParticleWaveFockRuntime.projectionLaw.outcomeAt PUnit.unit
      (runtimeAt depth).emittedOccurrence = _
  unfold SourceNativeProjectionLaw.outcomeAt
  generalize classifierEq :
    ParticleWaveFockRuntime.projectionLaw.classify PUnit.unit
      (runtimeAt depth).emittedOccurrence = classification
  cases classification with
  | inl active =>
      have activeEq : active = runtimeParticleWaveActive depth := by
        apply PLift.down_injective
        exact Subsingleton.elim _ _
      cases activeEq
      rfl
  | inr inactive =>
      have impossible := inactive.down
      change ParticleWaveFockRuntime.scanIndex
        (runtimeAt depth).current.visit.current = 0 at impossible
      rw [show ParticleWaveFockRuntime.scanIndex
          (runtimeAt depth).current.visit.current =
            scanIndex (runtimeAt depth).current.visit.current by rfl,
        runtimeAt_scanIndex] at impossible
      omega

theorem runtimeReadout_is_operational (depth : Nat) :
    runtimeFacade.readoutAt (runtimeAt depth) .operationalGoldbach =
      .inl ⟨runtimeActive depth, runtimePayload depth⟩ := by
  change operationalProjectionLaw.outcomeAt PUnit.unit
      (runtimeAt depth).emittedOccurrence = _
  unfold SourceNativeProjectionLaw.outcomeAt
  generalize classifierEq :
    operationalProjectionLaw.classify PUnit.unit
      (runtimeAt depth).emittedOccurrence = classification
  cases classification with
  | inl active =>
      have activeEq : active = runtimeActive depth :=
        by
          apply PLift.down_injective
          exact Subsingleton.elim _ _
      cases activeEq
      rfl
  | inr inactive =>
      have impossible := inactive.down
      rw [runtimeAt_scanIndex] at impossible
      omega

/-- The common Fock state and the Goldbach calculation are sibling reads of
the same emitted occurrence; the latter's entire target tree remains rooted
there. -/
theorem runtime_particleWave_goldbach_share_occurrence (depth : Nat) :
    (runtimeParticleWavePayload depth).sourceOccurrence =
        (runtimePayload depth).sourceOccurrence ∧
      (runtimePayload depth).targetOccurrence.root.rootOccurrence =
        (runtimeParticleWavePayload depth).sourceOccurrence := by
  constructor
  · exact (runtimeParticleWavePayload depth).sourceOccurrence_eq.trans
      (runtimePayload depth).sourceOccurrence_eq.symm
  · exact (runtimePayload depth).targetRoot.trans
      (runtimeParticleWavePayload depth).sourceOccurrence_eq.symm

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
end CanonicalUnitArithmeticOperationalGoldbachRuntime
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
