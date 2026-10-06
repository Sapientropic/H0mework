import H0mework.Versions.R2.Foundation.Runtime.Activation
import H0mework.Versions.AB.Chemistry.LAlaninePropagation.InstalledElectronicPropagation

/-!
# Canonical activation of the L-alanine native electronic clock

The process state is an existing exact finite root visit. Its successor is
that visit's native compiler successor, so canonical runtime/history supplies
iteration without another domain execution table or depth construction.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Propagation.Runtime

noncomputable section

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Root
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Installation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Propagation.Installation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Propagation.Producer

def electronicProcessCurrent (visit : RootVisit root.toAuthoritativeRoot.toRoot) :
    SourceNativeLivingRootCurrentAt N :=
  ⟨V, root, .finite visit⟩

def electronicRuntimeProcess : SourceNativeLivingRootProcess N where
  State := RootVisit root.toAuthoritativeRoot.toRoot
  stateAt := electronicProcessCurrent
  stateAt_injective := by
    intro left right equality
    change (⟨V, root, .finite left⟩ : SourceNativeLivingRootCurrentAt N) =
      ⟨V, root, .finite right⟩ at equality
    injection equality with _ _ visitEq
    exact SourceNativeTemporalVisitAt.finite_injective visitEq
  initial := root.toAuthoritativeRoot.toRoot.initialVisit
  successorAt := fun visit => ⟨visit.next rfl, rfl, HEq.rfl⟩

/-- The closed inventory is exactly the projection law already installed in this root. -/
def electronicRuntimeFacade : SourceNativeLivingRuntimeFacade N where
  process := electronicRuntimeProcess
  FaceAt := fun runtime =>
    runtime.current.root.toAuthoritativeRoot.source.projectionLaw.Projection
  componentAt := fun runtime _face =>
    runtime.current.root.toAuthoritativeRoot.source.projectionLaw
  installationAt := fun _runtime _face => .ofEq rfl
  projectionAt := fun _runtime face => face

def electronicRuntimeSeed : LivingRuntimeState electronicRuntimeProcess :=
  electronicRuntimeFacade.seed

def electronicRuntimeAfterCheckpoint : LivingRuntimeState electronicRuntimeProcess :=
  electronicRuntimeSeed.advance 4

def electronicRuntimeFirstNative : LivingRuntimeState electronicRuntimeProcess :=
  electronicRuntimeAfterCheckpoint.tick.next

def electronicRuntimeSecondNative : LivingRuntimeState electronicRuntimeProcess :=
  electronicRuntimeFirstNative.tick.next

def electronicRuntimeHistory (fuel : Nat) :
    SourceNativeLivingRootHistoryAt electronicRuntimeProcess fuel electronicRuntimeSeed.state :=
  electronicRuntimeSeed.run fuel

theorem electronicRuntimeAfterCheckpoint_eq_visit4 :
    electronicRuntimeAfterCheckpoint.current.visit = visit4 := by
  rfl

theorem electronicRuntimeFirstNative_current :
    electronicRuntimeFirstNative.current.visit.current =
      .nativeElectronicCurrent (1 + nativeClockStep) := by
  rfl

theorem electronicRuntimeSecondNative_current :
    electronicRuntimeSecondNative.current.visit.current =
      .nativeElectronicCurrent ((1 + nativeClockStep) + nativeClockStep) := by
  rfl

theorem nativeElectronicProjection_exact (stage : LAlanineStage)
    (active : nativeElectronicProjectionActiveAt stage) :
    baseProjectionLaw.outcomeAt .nativeElectronicEvolution (Root.emitted stage) =
      (.inl ⟨active, nativeElectronicEffectAt stage active⟩ :
        SourceNativeProjectionFiberAt baseProjectionLaw .nativeElectronicEvolution
          (Root.emitted stage)) := by
  cases stage <;> cases active <;> rfl

theorem nativeNextStage_eq_target (stage : LAlanineStage)
    (active : nativeElectronicProjectionActiveAt stage) :
    nextStage stage =
      .nativeElectronicCurrent (nativeElectronicEffectAt stage active).targetTime := by
  cases stage <;> cases active <;> rfl

/-- Specialize the compiler's branch-indexed row to its actual native-write patch. -/
def nativeCompiledSourceRow (stage : LAlanineStage) :
    (generatedPatch (Root.emitted stage)).CanonicalGeneratedSourceRowAt
      (sourceEntryAt (Root.emitted stage)) :=
  sourceRow (Root.emitted stage)

/-- Read the target actually selected by the source compiler's whole-ledger row. -/
def nativeTargetStanding (stage : LAlanineStage)
    (active : nativeElectronicProjectionActiveAt stage) :
    NativeElectronicStandingAt (nativeElectronicEffectAt stage active).targetTime :=
  let target : OpenResponsibilityAt N
      (.nativeElectronicCurrent (nativeElectronicEffectAt stage active).targetTime) :=
    (nativeNextStage_eq_target stage active) ▸ (nativeCompiledSourceRow stage).targetEntry
  target.2

theorem nativeTargetStanding_receives_effect (stage : LAlanineStage)
    (active : nativeElectronicProjectionActiveAt stage) :
    (nativeTargetStanding stage active).density =
      (nativeElectronicEffectAt stage active).targetDensity := by
  rw [NativeElectronicStandingAt.density_eq_source,
    NativeElectronicStepAt.target_eq_source]

theorem nativeTargetStanding_source (stage : LAlanineStage)
    (active : nativeElectronicProjectionActiveAt stage) :
    (nativeTargetStanding stage active).sourceMatrices =
      (nativeElectronicEffectAt stage active).sourceMatrices :=
  (nativeTargetStanding stage active).sourceMatricesExact.trans
    (nativeElectronicEffectAt stage active).sourceMatricesExact.symm

theorem nativeTargetStanding_generated (stage : LAlanineStage)
    (active : nativeElectronicProjectionActiveAt stage) :
    (nativeTargetStanding stage active).density =
      electronicAdvance (nativeElectronicEffectAt stage active).currentDensity :=
  (nativeTargetStanding_receives_effect stage active).trans
    (nativeElectronicEffectAt stage active).generated

theorem nativeTargetStanding_responds (stage : LAlanineStage)
    (active : nativeElectronicProjectionActiveAt stage) :
    (nativeTargetStanding stage active).density ≠
      (nativeElectronicEffectAt stage active).currentDensity := by
  rw [nativeTargetStanding_receives_effect]
  exact (nativeElectronicEffectAt stage active).responds

theorem nativeTargetStanding_clock (stage : LAlanineStage)
    (active : nativeElectronicProjectionActiveAt stage) :
    (nativeTargetStanding stage active).timeStamp =
      (nativeElectronicEffectAt stage active).currentTime + nativeClockStep := by
  rw [(nativeTargetStanding stage active).timeStampExact,
    (nativeElectronicEffectAt stage active).targetTimeExact,
    (nativeElectronicEffectAt stage active).durationExact]

theorem nativeRow_claim_lineage_budget (stage : LAlanineStage)
    (active : nativeElectronicProjectionActiveAt stage) :
    (sourceEntryAt (Root.emitted stage)).claim =
        (nativeCompiledSourceRow stage).targetEntry.claim ∧
      N.lineageAt stage = N.lineageAt (nextStage stage) ∧
      (sourceEntryAt (Root.emitted stage)).progressBudget = 0 ∧
      (nativeCompiledSourceRow stage).targetEntry.progressBudget = 0 := by
  cases stage <;> cases active <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem nativeRow_commutes_with_wholeLedger (stage : LAlanineStage) :
    (sourceRow (Root.emitted stage)).CommutesWithWorld :=
  (sourceRow (Root.emitted stage)).commutes_with_world

def nativeRuntimeFace (runtime : LivingRuntimeState electronicRuntimeProcess) :
    electronicRuntimeFacade.FaceAt runtime :=
  siblingInstallation.embed .nativeElectronicEvolution

theorem nativeRuntimeEffect_is_installed (runtime : LivingRuntimeState electronicRuntimeProcess)
    (active : nativeElectronicProjectionActiveAt runtime.state.current) :
    HEq (electronicRuntimeFacade.readoutAt runtime (nativeRuntimeFace runtime))
      (.inl ⟨active, nativeElectronicEffectAt runtime.state.current active⟩ :
        SourceNativeProjectionFiberAt baseProjectionLaw .nativeElectronicEvolution
          (Root.emitted runtime.state.current)) := by
  exact (siblingInstallation.outcome_heq (Root.emitted runtime.state.current)
    .nativeElectronicEvolution).trans
      (heq_of_eq (nativeElectronicProjection_exact runtime.state.current active))

theorem electronicRuntimeFace_factorizes (runtime : LivingRuntimeState electronicRuntimeProcess)
    (face : electronicRuntimeFacade.FaceAt runtime) :
    type_of% (electronicRuntimeFacade.readoutAt_factorizes runtime face) :=
  electronicRuntimeFacade.readoutAt_factorizes runtime face

/-- Temporal authority is selected from this exact tick's own patch. -/
def nativeRuntimeRow (runtime : LivingRuntimeState electronicRuntimeProcess) :
    runtime.tick.generated.GeneratedEntryRowAt
      (sourceEntryAt (Root.emitted runtime.state.current)) :=
  SourceNativeTemporalVisitGeneratedEvolutionAt.GeneratedEntryRowAt.ofSourceRow
    (sourceRow (Root.emitted runtime.state.current))

theorem nativeRuntimeNext_current (runtime : LivingRuntimeState electronicRuntimeProcess)
    (active : nativeElectronicProjectionActiveAt runtime.state.current) :
    runtime.tick.next.current.visit.current =
      .nativeElectronicCurrent (nativeElectronicEffectAt runtime.state.current active).targetTime :=
  nativeNextStage_eq_target runtime.state.current active

theorem nativeRuntimeNext_active (runtime : LivingRuntimeState electronicRuntimeProcess)
    (active : nativeElectronicProjectionActiveAt runtime.state.current) :
    Nonempty (nativeElectronicProjectionActiveAt runtime.tick.next.state.current) := by
  change Nonempty (nativeElectronicProjectionActiveAt (nextStage runtime.state.current))
  rw [nativeNextStage_eq_target runtime.state.current active]
  exact ⟨PUnit.unit⟩

structure SourceInstalledLAlanineNativeElectronicRuntimeCrown : Prop where
  previousCheckpoint : SourceInstalledLAlanine40KElectronicPropagationRootCrown
  sourceSeed : electronicRuntimeSeed = LivingRuntimeState.initial electronicRuntimeProcess
  previousActualVisit : electronicRuntimeAfterCheckpoint.current.visit = visit4
  firstNative : type_of% electronicRuntimeFirstNative_current
  secondNative : type_of% electronicRuntimeSecondNative_current
  sourceDuration : nativeClockStep = 15625000000000 / 36212777618028463
  positiveDuration : 0 < nativeClockStep
  completeFaceCoverage : ∀ runtime (face : electronicRuntimeFacade.FaceAt runtime),
    type_of% (electronicRuntimeFacade.readoutAt_factorizes runtime face)
  installedNativeEffect : ∀ runtime active, type_of% (nativeRuntimeEffect_is_installed runtime active)
  sameTemporalRow : ∀ runtime : LivingRuntimeState electronicRuntimeProcess, Nonempty
    (runtime.tick.generated.GeneratedEntryRowAt (sourceEntryAt (Root.emitted runtime.state.current)))
  sameWholeLedger : ∀ stage, (sourceRow (Root.emitted stage)).CommutesWithWorld
  actualTargetReceives : ∀ stage active, type_of% (nativeTargetStanding_receives_effect stage active)
  actualTargetGenerated : ∀ stage active, type_of% (nativeTargetStanding_generated stage active)
  actualTargetSource : ∀ stage active, type_of% (nativeTargetStanding_source stage active)
  actualTargetResponds : ∀ stage active, type_of% (nativeTargetStanding_responds stage active)
  actualTargetClock : ∀ stage active, type_of% (nativeTargetStanding_clock stage active)
  conservedRow : ∀ stage active, type_of% (nativeRow_claim_lineage_budget stage active)
  generatedNativeNext : ∀ runtime active, type_of% (nativeRuntimeNext_current runtime active)
  continuedActivity : ∀ runtime active, type_of% (nativeRuntimeNext_active runtime active)
  finiteObservation : ∀ fuel, electronicRuntimeHistory fuel =
    electronicRuntimeProcess.generateHistory fuel electronicRuntimeSeed.state

theorem sourceInstalledLAlanineNativeElectronicRuntime_crown :
    SourceInstalledLAlanineNativeElectronicRuntimeCrown where
  previousCheckpoint := sourceInstalledLAlanine40KElectronicPropagation_rootCrown
  sourceSeed := rfl
  previousActualVisit := electronicRuntimeAfterCheckpoint_eq_visit4
  firstNative := electronicRuntimeFirstNative_current
  secondNative := electronicRuntimeSecondNative_current
  sourceDuration := nativeClockStep_exact
  positiveDuration := nativeClockStep_positive
  completeFaceCoverage := electronicRuntimeFace_factorizes
  installedNativeEffect := nativeRuntimeEffect_is_installed
  sameTemporalRow := fun runtime => ⟨nativeRuntimeRow runtime⟩
  sameWholeLedger := nativeRow_commutes_with_wholeLedger
  actualTargetReceives := nativeTargetStanding_receives_effect
  actualTargetGenerated := nativeTargetStanding_generated
  actualTargetSource := nativeTargetStanding_source
  actualTargetResponds := nativeTargetStanding_responds
  actualTargetClock := nativeTargetStanding_clock
  conservedRow := nativeRow_claim_lineage_budget
  generatedNativeNext := nativeRuntimeNext_current
  continuedActivity := nativeRuntimeNext_active
  finiteObservation := fun _ => rfl

end

end LAlanine40K2025.Propagation.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
