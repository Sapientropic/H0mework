import H0mework.Versions.R2.Arithmetic.FockResponsibility.OccurrenceSector
import H0mework.Versions.R2.Arithmetic.FockResponsibility.AtomicRuntime
import H0mework.Versions.R2.Arithmetic.FockResponsibility.ActualityDebt
import H0mework.Versions.V2.Arithmetic.FockUnitAction.Inventory.SourceSelected.Projection

/-!
# Occurrence responsibility installed on the exact Goldbach runtime

The existing atomic-dynamics authority already owns the canonical emitted
occurrence and its physical current.  This file installs the occurrence
factor-process face, witness-free prime-pair actuality face, its historical
pending-claim face, and the source-selected fixed-target actor.  The inherited
particle-wave, operational Goldbach, and atomic dynamics faces remain on the
same root.

None of these faces promotes a local terminal or projection residual to root
authority.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalArithmeticState
namespace ParticleWaveFockOccurrenceResponsibilityRuntime

open ArithmeticGeneration
open CanonicalUnitArithmeticOperationalGoldbachRuntime
open CanonicalUnitArithmeticRoot
open ParticleWaveFockAtomicDynamicsRuntime
open ParticleWaveFockOccurrencePhysicalProcess
open ParticleWaveFockOccurrenceResponsibility
open ParticleWaveFockPrimePairActuality
open ParticleWaveFockPrimePairActualityDebt
open PendingClaimBirth

noncomputable section

abbrev BaseAuthoritySource :=
  ParticleWaveFockAtomicDynamicsRuntime.authoritySource

abbrev BaseLedgerSource := BaseAuthoritySource.restructuringSource.toLedgerSource

def scanIndex (current : Current) : Nat := current.cardinalShadow

/-- Exact runtime occurrence together with its installed atomic face and the
source-generated initial occurrence responsibility. -/
structure RootGeneratedOccurrenceResponsibilityAt
    (current : Current)
    (occurrence :
      BaseLedgerSource.source.toRootSource.actual.OccurrenceAt current)
    (indexInRange : 1 ≤ scanIndex current) : Type where
  private mk ::
  sourceOccurrence :
    BaseLedgerSource.source.toRootSource.actual.OccurrenceAt current
  sourceOccurrence_eq : sourceOccurrence = occurrence
  atomicPayload :
    ParticleWaveFockAtomicDynamicsRuntime.RootGeneratedAtomicDynamicsAt
      current occurrence indexInRange
  atomicPayload_eq : atomicPayload =
    ParticleWaveFockAtomicDynamicsRuntime.atomicProjectionLaw.project
      PUnit.unit occurrence ⟨indexInRange⟩
  occurrenceCurrent : OccurrencePhysicalCurrentAt (scanIndex current)
  occurrenceCurrent_eq : occurrenceCurrent =
    ParticleWaveFockOccurrencePhysicalProcess.seed
      atomicPayload.physicalCurrent.current
  responsibilityState :
    ParticleWaveFockOccurrenceResponsibility.State (scanIndex current)
  responsibilityState_eq : responsibilityState =
    ParticleWaveFockOccurrenceResponsibility.initialState
      atomicPayload.physicalCurrent.current
  disposition :
    ParticleWaveFockOccurrenceResponsibility.GeneratedDispositionAt
      responsibilityState
  disposition_eq : disposition =
    ParticleWaveFockOccurrenceResponsibility.generateDisposition
      responsibilityState
  atomicOccurrence : atomicPayload.sourceOccurrence = sourceOccurrence
  operationalOccurrence :
    atomicPayload.operational.sourceOccurrence = sourceOccurrence
  targetRoot :
    atomicPayload.operational.targetOccurrence.root.rootOccurrence = occurrence

def generateOccurrenceResponsibility
    (current : Current)
    (occurrence :
      BaseLedgerSource.source.toRootSource.actual.OccurrenceAt current)
    (indexInRange : 1 ≤ scanIndex current) :
    RootGeneratedOccurrenceResponsibilityAt current occurrence indexInRange := by
  let atomicPayload :=
    ParticleWaveFockAtomicDynamicsRuntime.atomicProjectionLaw.project
      PUnit.unit occurrence ⟨indexInRange⟩
  let occurrenceCurrent :=
    ParticleWaveFockOccurrencePhysicalProcess.seed
      atomicPayload.physicalCurrent.current
  let responsibilityState :=
    ParticleWaveFockOccurrenceResponsibility.initialState
      atomicPayload.physicalCurrent.current
  exact
    { sourceOccurrence := occurrence
      sourceOccurrence_eq := rfl
      atomicPayload := atomicPayload
      atomicPayload_eq := rfl
      occurrenceCurrent := occurrenceCurrent
      occurrenceCurrent_eq := rfl
      responsibilityState := responsibilityState
      responsibilityState_eq := rfl
      disposition :=
        ParticleWaveFockOccurrenceResponsibility.generateDisposition
          responsibilityState
      disposition_eq := rfl
      atomicOccurrence := atomicPayload.sourceOccurrence_eq
      operationalOccurrence := atomicPayload.operational.sourceOccurrence_eq
      targetRoot := atomicPayload.targetRoot }

def occurrenceProjectionLaw : SourceNativeProjectionLaw BaseLedgerSource where
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
    RootGeneratedOccurrenceResponsibilityAt current occurrence active.down
  project := fun _ {current} occurrence active =>
    generateOccurrenceResponsibility current occurrence active.down

def occurrenceAuthoritySource : SourceNativeAuthoritySource N V :=
  BaseAuthoritySource.withProjectionCoface occurrenceProjectionLaw

def actualityAuthoritySource : SourceNativeAuthoritySource N V :=
  occurrenceAuthoritySource.withProjectionCoface actualityProjectionLaw

def pendingAuthoritySource : SourceNativeAuthoritySource N V :=
  actualityAuthoritySource.withProjectionCoface
    actualityPendingClaimProjectionLaw.toProjectionLaw

def authoritySource : SourceNativeAuthoritySource N V :=
  pendingAuthoritySource.withProjectionCoface GoldbachUnitSelectedActor.projectionLaw

def occurrenceToActualityInstallation : SourceNativeProjectionLaw.InstallationAt
    occurrenceAuthoritySource.projectionLaw
      actualityAuthoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    occurrenceAuthoritySource actualityProjectionLaw

def finalInheritedInstallation : SourceNativeProjectionLaw.InstallationAt
    actualityAuthoritySource.projectionLaw pendingAuthoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    actualityAuthoritySource actualityPendingClaimProjectionLaw.toProjectionLaw

def actorInheritedInstallation : SourceNativeProjectionLaw.InstallationAt
    pendingAuthoritySource.projectionLaw authoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    pendingAuthoritySource GoldbachUnitSelectedActor.projectionLaw

def actorInstallation : SourceNativeProjectionLaw.InstallationAt
    GoldbachUnitSelectedActor.projectionLaw authoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface
    pendingAuthoritySource GoldbachUnitSelectedActor.projectionLaw

def occurrenceInstallation : SourceNativeProjectionLaw.InstallationAt
    occurrenceProjectionLaw authoritySource.projectionLaw :=
  (SourceNativeProjectionLaw.InstallationAt.componentCoface
    BaseAuthoritySource occurrenceProjectionLaw).trans
      occurrenceToActualityInstallation |>.trans finalInheritedInstallation
        |>.trans actorInheritedInstallation

def actualityInstallation : SourceNativeProjectionLaw.InstallationAt
    actualityProjectionLaw authoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface
    occurrenceAuthoritySource actualityProjectionLaw |>.trans
      finalInheritedInstallation |>.trans actorInheritedInstallation

def pendingClaimInstallation : SourceNativeProjectionLaw.InstallationAt
    actualityPendingClaimProjectionLaw.toProjectionLaw
      authoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface
    actualityAuthoritySource actualityPendingClaimProjectionLaw.toProjectionLaw
      |>.trans actorInheritedInstallation

def atomicInstallation : SourceNativeProjectionLaw.InstallationAt
    ParticleWaveFockAtomicDynamicsRuntime.atomicProjectionLaw
      authoritySource.projectionLaw :=
  ParticleWaveFockAtomicDynamicsRuntime.atomicInstallation.trans
    (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
      BaseAuthoritySource occurrenceProjectionLaw) |>.trans
        occurrenceToActualityInstallation |>.trans
        finalInheritedInstallation |>.trans actorInheritedInstallation

def operationalInstallation : SourceNativeProjectionLaw.InstallationAt
    CanonicalUnitArithmeticOperationalGoldbachRuntime.operationalProjectionLaw
      authoritySource.projectionLaw :=
  ParticleWaveFockAtomicDynamicsRuntime.operationalInstallation.trans
    (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
      BaseAuthoritySource occurrenceProjectionLaw) |>.trans
        occurrenceToActualityInstallation |>.trans
        finalInheritedInstallation |>.trans actorInheritedInstallation

def particleWaveInstallation : SourceNativeProjectionLaw.InstallationAt
    ParticleWaveFockRuntime.projectionLaw authoritySource.projectionLaw :=
  ParticleWaveFockAtomicDynamicsRuntime.particleWaveInstallation.trans
    (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
      BaseAuthoritySource occurrenceProjectionLaw) |>.trans
        occurrenceToActualityInstallation |>.trans
        finalInheritedInstallation |>.trans actorInheritedInstallation

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
  | occurrenceResponsibility
  | primePairActuality
  | primePairPendingClaim
  | unitSelectedActor
  deriving DecidableEq

abbrev runtimeFacade : SourceNativeLivingRuntimeFacade N where
  process := process
  FaceAt := fun _runtime => FaceAt
  componentAt := fun _runtime face =>
    match face with
    | .particleWave => ParticleWaveFockRuntime.projectionLaw
    | .operationalGoldbach =>
        CanonicalUnitArithmeticOperationalGoldbachRuntime.operationalProjectionLaw
    | .atomicDynamics =>
        ParticleWaveFockAtomicDynamicsRuntime.atomicProjectionLaw
    | .occurrenceResponsibility => occurrenceProjectionLaw
    | .primePairActuality => actualityProjectionLaw
    | .primePairPendingClaim => actualityPendingClaimProjectionLaw.toProjectionLaw
    | .unitSelectedActor => GoldbachUnitSelectedActor.projectionLaw
  installationAt := fun _runtime face =>
    match face with
    | .particleWave => particleWaveInstallation
    | .operationalGoldbach => operationalInstallation
    | .atomicDynamics => atomicInstallation
    | .occurrenceResponsibility => occurrenceInstallation
    | .primePairActuality => actualityInstallation
    | .primePairPendingClaim => pendingClaimInstallation
    | .unitSelectedActor => actorInstallation
  projectionAt := fun _runtime face =>
    match face with
    | .particleWave => PUnit.unit
    | .operationalGoldbach => PUnit.unit
    | .atomicDynamics => PUnit.unit
    | .occurrenceResponsibility => PUnit.unit
    | .primePairActuality => PUnit.unit
    | .primePairPendingClaim => PUnit.unit
    | .unitSelectedActor => PUnit.unit

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
    occurrenceProjectionLaw.ActiveAt PUnit.unit
      (runtimeAt depth).emittedOccurrence :=
  ⟨by rw [runtimeAt_scanIndex]; omega⟩

def runtimeOccurrencePayload (depth : Nat) :
    RootGeneratedOccurrenceResponsibilityAt
      (runtimeAt depth).current.visit.current
      (runtimeAt depth).emittedOccurrence
      (runtimeActive depth).down :=
  occurrenceProjectionLaw.project PUnit.unit
    (runtimeAt depth).emittedOccurrence (runtimeActive depth)

def runtimeActualityPayload (depth : Nat) :
    RootGeneratedPrimePairActualityAt
      (runtimeAt depth).current.visit.current
      (runtimeAt depth).emittedOccurrence
      (runtimeActive depth).down :=
  actualityProjectionLaw.project PUnit.unit
    (runtimeAt depth).emittedOccurrence (runtimeActive depth)

theorem runtimeReadout_is_occurrence (depth : Nat) :
    runtimeFacade.readoutAt (runtimeAt depth) .occurrenceResponsibility =
      .inl ⟨runtimeActive depth, runtimeOccurrencePayload depth⟩ := by
  change occurrenceProjectionLaw.outcomeAt PUnit.unit
      (runtimeAt depth).emittedOccurrence = _
  unfold SourceNativeProjectionLaw.outcomeAt
  generalize classifierEq :
    occurrenceProjectionLaw.classify PUnit.unit
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
      change scanIndex (runtimeAt depth).current.visit.current = 0 at impossible
      rw [runtimeAt_scanIndex] at impossible
      omega

theorem runtimeReadout_is_primePairActuality (depth : Nat) :
    runtimeFacade.readoutAt (runtimeAt depth) .primePairActuality =
      .inl ⟨runtimeActive depth, runtimeActualityPayload depth⟩ := by
  change actualityProjectionLaw.outcomeAt PUnit.unit
      (runtimeAt depth).emittedOccurrence = _
  unfold SourceNativeProjectionLaw.outcomeAt
  generalize classifierEq :
    actualityProjectionLaw.classify PUnit.unit
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
      change scanIndex (runtimeAt depth).current.visit.current = 0 at impossible
      rw [runtimeAt_scanIndex] at impossible
      omega

theorem runtimeOccurrencePayload_same_occurrence (depth : Nat) :
    (runtimeOccurrencePayload depth).sourceOccurrence =
        (runtimeAt depth).current.root.toAuthoritativeRoot.toLedgerRoot.emitted
          (runtimeAt depth).current.visit.current ∧
      (runtimeOccurrencePayload depth).atomicPayload.sourceOccurrence =
        (runtimeOccurrencePayload depth).sourceOccurrence ∧
      (runtimeOccurrencePayload depth).atomicPayload.operational.sourceOccurrence =
        (runtimeOccurrencePayload depth).sourceOccurrence :=
  ⟨(runtimeOccurrencePayload depth).sourceOccurrence_eq,
    (runtimeOccurrencePayload depth).atomicOccurrence,
    (runtimeOccurrencePayload depth).operationalOccurrence⟩

theorem runtimeOccurrenceDisposition_source_total (depth : Nat) :
    Nonempty
      (ParticleWaveFockOccurrenceResponsibility.GeneratedDispositionAt
        (runtimeOccurrencePayload depth).responsibilityState) :=
  ⟨(runtimeOccurrencePayload depth).disposition⟩

/-- Every named face factors through the same emitted
occurrence, whole ledger, and generated next. -/
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

theorem runtimeOccurrence_keeps_occurrence_ledger_next (depth : Nat) :
    (runtimeOccurrencePayload depth).sourceOccurrence =
        (runtimeAt depth).current.root.toAuthoritativeRoot.toLedgerRoot.emitted
          (runtimeAt depth).current.visit.current ∧
      HEq (runtimeAt depth).tick.generated.wholeLedgerWriteBack
        ((runtimeAt depth).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          (runtimeAt depth).current.visit.current) ∧
      (runtimeAt depth).tick.nextCurrent =
        runtimeFacade.process.stateAt
          (runtimeFacade.process.successor (runtimeAt depth).state) := by
  have covered := coversAt_factorizes (runtimeAt depth)
    FaceAt.occurrenceResponsibility
  exact ⟨(runtimeOccurrencePayload_same_occurrence depth).1,
    covered.2.2.1, covered.2.2.2.2⟩

theorem runtimeActuality_keeps_occurrence_ledger_next (depth : Nat) :
    (runtimeActualityPayload depth).sourceOccurrence =
        (runtimeAt depth).current.root.toAuthoritativeRoot.toLedgerRoot.emitted
          (runtimeAt depth).current.visit.current ∧
      HEq (runtimeAt depth).tick.generated.wholeLedgerWriteBack
        ((runtimeAt depth).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          (runtimeAt depth).current.visit.current) ∧
      (runtimeAt depth).tick.nextCurrent =
        runtimeFacade.process.stateAt
          (runtimeFacade.process.successor (runtimeAt depth).state) := by
  have covered := coversAt_factorizes (runtimeAt depth)
    FaceAt.primePairActuality
  exact ⟨(runtimeActualityPayload depth).sourceOccurrence_eq,
    covered.2.2.1, covered.2.2.2.2⟩

def runtimeUnitSelectedActorPayload (depth : Nat) :=
  GoldbachUnitSelectedActor.projectionLaw.project PUnit.unit
    (runtimeAt depth).emittedOccurrence (runtimeActive depth)

theorem runtimeUnitSelectedActorPayload_eq_readout (depth : Nat) :
    runtimeFacade.readoutAt (runtimeAt depth) FaceAt.unitSelectedActor =
      .inl ⟨runtimeActive depth, runtimeUnitSelectedActorPayload depth⟩ := by
  change GoldbachUnitSelectedActor.projectionLaw.outcomeAt PUnit.unit
    (runtimeAt depth).emittedOccurrence = _
  unfold SourceNativeProjectionLaw.outcomeAt
  generalize classified : GoldbachUnitSelectedActor.projectionLaw.classify PUnit.unit
    (runtimeAt depth).emittedOccurrence = outcome
  cases outcome with
  | inl active =>
      have same : active = runtimeActive depth := by
        apply PLift.down_injective
        exact Subsingleton.elim _ _
      cases same
      rfl
  | inr inactive =>
      have impossible := inactive.down
      change scanIndex (runtimeAt depth).current.visit.current = 0 at impossible
      rw [runtimeAt_scanIndex] at impossible
      omega

theorem runtimeUnitSelectedActorPayload_eq_tickProjection (depth : Nat) :
    HEq ((Sum.inl ⟨runtimeActive depth, runtimeUnitSelectedActorPayload depth⟩) :
      SourceNativeProjectionFiberAt GoldbachUnitSelectedActor.projectionLaw PUnit.unit
        (runtimeAt depth).emittedOccurrence)
      ((runtimeAt depth).tick.generated.projectionOutcome
        ((runtimeFacade.installationAt (runtimeAt depth) FaceAt.unitSelectedActor).embed
          (runtimeFacade.projectionAt (runtimeAt depth) FaceAt.unitSelectedActor))) := by
  exact (heq_of_eq (runtimeUnitSelectedActorPayload_eq_readout depth).symm).trans
    (coversAt_factorizes (runtimeAt depth) FaceAt.unitSelectedActor).2.2.2.1

theorem runtimeUnitSelectedActor_keeps_occurrence_ledger_next (depth : Nat) :
    (runtimeUnitSelectedActorPayload depth).sourceOccurrence =
        (runtimeAt depth).current.root.toAuthoritativeRoot.toLedgerRoot.emitted
          (runtimeAt depth).current.visit.current ∧
      HEq (runtimeAt depth).tick.generated.wholeLedgerWriteBack
        ((runtimeAt depth).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          (runtimeAt depth).current.visit.current) ∧
      (runtimeAt depth).tick.nextCurrent =
        runtimeFacade.process.stateAt
          (runtimeFacade.process.successor (runtimeAt depth).state) := by
  have covered := coversAt_factorizes (runtimeAt depth) FaceAt.unitSelectedActor
  exact ⟨(runtimeUnitSelectedActorPayload depth).sourceOccurrence_eq,
    covered.2.2.1, covered.2.2.2.2⟩

end

end ParticleWaveFockOccurrenceResponsibilityRuntime
end CanonicalArithmeticState
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
