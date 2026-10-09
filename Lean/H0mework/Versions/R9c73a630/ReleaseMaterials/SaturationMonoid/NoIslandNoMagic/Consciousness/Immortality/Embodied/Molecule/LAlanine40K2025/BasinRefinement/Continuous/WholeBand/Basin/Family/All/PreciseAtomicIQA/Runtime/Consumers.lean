import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.PreciseAtomicIQA.Runtime.Facade

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.PreciseAtomicIQA.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.UnifiedOrbitals
open SourceFiniteData
open LAlanine40K2025.BasinRefinement.SourceSignedEvaluator
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin
open scoped BigOperators
noncomputable section

theorem target_zone_parent_preserved :
    PreciseAtomicIQA.material.parent =
        PreciseAttractionZones.Runtime.readMaterial PreciseAttractionZones.Runtime.afterFirst ∧
      type_of% PreciseAttractionZones.Runtime.sourceGeneratedPhysicalPreciseAttractionZonesNext :=
  ⟨rfl,PreciseAttractionZones.Runtime.sourceGeneratedPhysicalPreciseAttractionZonesNext⟩

theorem target_self_source (runtime : LivingRuntimeState process) (a : Fin 13) :
    (readMaterial runtime).selfEnergy a = AtomicIQA.PreciseTarget.selfEnergy a := by
  rw [(material_read runtime).2]
  rfl

theorem target_pair_source (runtime : LivingRuntimeState process) (a b : Fin 13) :
    (readMaterial runtime).interaction a b = AtomicIQA.PreciseTarget.interaction a b := by
  rw [(material_read runtime).2]
  rfl

theorem target_residual_source (runtime : LivingRuntimeState process) :
    (readMaterial runtime).residualEnergy = AtomicIQA.PreciseTarget.residualEnergy := by
  rw [(material_read runtime).2]
  rfl

theorem target_repulsion_source (runtime : LivingRuntimeState process) (a b : Fin 13) :
    (readMaterial runtime).nuclearRepulsion a b =
      Nuclear.PreciseTarget.nuclearRepulsion a b := by
  rw [(material_read runtime).2]
  rfl

theorem target_iqa_original_ao (runtime : LivingRuntimeState process) :
    (∑ a : Fin 13, (readMaterial runtime).selfEnergy a) +
      (∑ p ∈ AtomicIQA.pairSet, (readMaterial runtime).interaction p.1 p.2) +
      (readMaterial runtime).residualEnergy =
      (∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℝ) *
        (UnifiedOrbitals.kinetic i j +
          UnifiedOrbitals.Attraction.Precise.aoIntegral i j)) +
      (∑ p ∈ AtomicIQA.pairSet,
        (readMaterial runtime).nuclearRepulsion p.1 p.2) +
      pairCoulombEnergy.re := by
  rw [(material_read runtime).2]
  exact PreciseAtomicIQA.total_original_ao

theorem target_iqa_independent (runtime : LivingRuntimeState process) :
    |((∑ a : Fin 13, (readMaterial runtime).selfEnergy a) +
        (∑ p ∈ AtomicIQA.pairSet,
          (readMaterial runtime).interaction p.1 p.2) +
        (readMaterial runtime).residualEnergy) -
      ((∑ z : Option (Fin 13), OneBody.zoneKinetic z) +
        (readMaterial runtime).parent.parent.independentWeighted +
        Nuclear.PreciseTarget.totalRepulsion + pairCoulombEnergy.re)| ≤
      (1/10^9 : ℝ) := by
  rw [(material_read runtime).2]
  exact PreciseAtomicIQA.total_independent_nuclear_ledger

theorem response (runtime : LivingRuntimeState process) :
    Reentry.Runtime.reentryResponse runtime.state.current = Frame.Runtime.parentResult := by
  have keeps : ∀ {state : process.State}, SourceNativeRuntimeReachableAt process state →
      Reentry.Runtime.reentryResponse state.current = Frame.Runtime.parentResult := by
    intro state reachable
    induction reachable with
    | initial => rfl
    | step prior kept => exact kept
  exact keeps runtime.reachable

theorem read_commutes_with_physicalOccurrence (runtime : LivingRuntimeState process) :
    Frame.Runtime.parentResult.nuclear.target =
        Reentry.Runtime.reentryFrame runtime.tick.next.state.current ∧
    Frame.Runtime.parentResult.realized =
        (Reentry.Runtime.reentryResponse runtime.state.current).realized ∧
    Frame.Runtime.parentResult.clock =
        Reentry.Runtime.reentryPhysicalTime runtime.tick.next.state.current ∧
    Frame.Runtime.parentResult.nuclear.targetLedger =
        Reentry.Runtime.reentryCurrentLedger runtime.tick.next.state.current := by
  change Frame.Runtime.parentResult.nuclear.target =
      (Reentry.Runtime.reentryResponse runtime.state.current).nuclear.target ∧
    Frame.Runtime.parentResult.realized =
      (Reentry.Runtime.reentryResponse runtime.state.current).realized ∧
    Frame.Runtime.parentResult.clock =
      (Reentry.Runtime.reentryResponse runtime.state.current).clock ∧
    Frame.Runtime.parentResult.nuclear.targetLedger =
      (Reentry.Runtime.reentryResponse runtime.state.current).nuclear.targetLedger
  rw [response]
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem wholeLedger_same_occurrence (runtime : LivingRuntimeState process) :
    runtime.tick.generated.wholeLedgerWriteBack =
      Reentry.Runtime.reentryLivingRoot.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        runtime.state.current := rfl

theorem row_identity (runtime : LivingRuntimeState process) :
    (Reentry.Runtime.reentryOccurrenceEntry
      (Reentry.Runtime.reentryEmitted runtime.state.current)).1 =
        .bondDensityIncidenceAdjudication ∧
    (Reentry.Runtime.reentryOccurrenceEntry
      (Reentry.Runtime.reentryEmitted runtime.state.current)).claim =
        .registeredExperimentalGeometryModelBondTopology ∧
    (Reentry.Runtime.reentryOccurrenceEntry
      (Reentry.Runtime.reentryEmitted runtime.state.current)).progressBudget = 0 ∧
    LAlanine40K2025.Root.N.lineageAt Reentry.Runtime.reentrySupport =
      LAlanine40K2025.Source.key :=
  ⟨rfl,rfl,rfl,rfl⟩

theorem clock_preserved (runtime : LivingRuntimeState process) :
    Reentry.Runtime.reentryPhysicalTime runtime.tick.next.state.current =
      3 * Propagation.Producer.nativeClockStep := by
  change (Reentry.Runtime.reentryResponse runtime.state.current).clock = _
  rw [response]
  exact Frame.Runtime.parent_clock

structure PhysicalPreciseAtomicIQAClosure : Prop where
  source : PreciseAtomicIQA.Closure
  parent : type_of% target_zone_parent_preserved
  selfSource : type_of% target_self_source
  pairSource : type_of% target_pair_source
  residualSource : type_of% target_residual_source
  repulsionSource : type_of% target_repulsion_source
  fullTargetAO : type_of% target_iqa_original_ao
  independent : type_of% target_iqa_independent
  physicalOccurrence : type_of% read_commutes_with_physicalOccurrence
  wholeLedger : type_of% wholeLedger_same_occurrence
  identity : type_of% row_identity
  clock : type_of% clock_preserved
  inherited : type_of% all_original_faces
  factorization : type_of% face_factorizes
  generatedNext : type_of% generated_same_next
  originalVisit : afterFirst.current.visit =
    Reentry.Runtime.generatedReentryAction.target.targetVisit
  allFaces : Nonempty (Face ≃ Fin 184)

theorem sourceGeneratedPhysicalPreciseAtomicIQANext : PhysicalPreciseAtomicIQAClosure :=
  ⟨(certificate_read afterFirst).2,target_zone_parent_preserved,
    target_self_source,target_pair_source,target_residual_source,
    target_repulsion_source,target_iqa_original_ao,target_iqa_independent,
    read_commutes_with_physicalOccurrence,wholeLedger_same_occurrence,
    row_identity,clock_preserved,all_original_faces,face_factorizes,
    generated_same_next,rfl,⟨faceEquiv⟩⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.PreciseAtomicIQA.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
