import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.AtomicIQA.Runtime.Facade

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.AtomicIQA.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SaturationMonoid.PhysicsCore ProofFreeRicherAnholonomicSource StageNineHolonomicField
open LAlanine40K2025.UnifiedOrbitals LAlanine40K2025.UnifiedAction
open LAlanine40K2025.UnifiedOrbitals.Frame
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb
open SourceGaussianModel SourceFiniteData ContinuousGradient GlobalSource WholeBandBasin Set Filter MeasureTheory Function WholeBandAttractor Metric
open scoped Topology BigOperators
noncomputable section

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
    Frame.Runtime.parentResult.nuclear.target = Reentry.Runtime.reentryFrame runtime.tick.next.state.current ∧
    Frame.Runtime.parentResult.realized = (Reentry.Runtime.reentryResponse runtime.state.current).realized ∧
    Frame.Runtime.parentResult.clock = Reentry.Runtime.reentryPhysicalTime runtime.tick.next.state.current ∧
    Frame.Runtime.parentResult.nuclear.targetLedger = Reentry.Runtime.reentryCurrentLedger runtime.tick.next.state.current := by
  change Frame.Runtime.parentResult.nuclear.target =
      (Reentry.Runtime.reentryResponse runtime.state.current).nuclear.target ∧
    Frame.Runtime.parentResult.realized = (Reentry.Runtime.reentryResponse runtime.state.current).realized ∧
    Frame.Runtime.parentResult.clock = (Reentry.Runtime.reentryResponse runtime.state.current).clock ∧
    Frame.Runtime.parentResult.nuclear.targetLedger =
      (Reentry.Runtime.reentryResponse runtime.state.current).nuclear.targetLedger
  rw [response]
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem wholeLedger_same_occurrence (runtime : LivingRuntimeState process) :
    runtime.tick.generated.wholeLedgerWriteBack =
      Reentry.Runtime.reentryLivingRoot.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.state.current := rfl

theorem row_identity (runtime : LivingRuntimeState process) :
    (Reentry.Runtime.reentryOccurrenceEntry (Reentry.Runtime.reentryEmitted runtime.state.current)).1 =
      .bondDensityIncidenceAdjudication ∧
    (Reentry.Runtime.reentryOccurrenceEntry (Reentry.Runtime.reentryEmitted runtime.state.current)).claim =
      .registeredExperimentalGeometryModelBondTopology ∧
    (Reentry.Runtime.reentryOccurrenceEntry (Reentry.Runtime.reentryEmitted runtime.state.current)).progressBudget = 0 ∧
    LAlanine40K2025.Root.N.lineageAt Reentry.Runtime.reentrySupport = LAlanine40K2025.Source.key :=
  ⟨rfl,rfl,rfl,rfl⟩

theorem complete_parent_preserved :
    AtomicIQA.material.parent = KineticLedger.Runtime.readMaterial KineticLedger.Runtime.afterFirst ∧
      type_of% KineticLedger.Runtime.sourceGeneratedPhysicalKineticLedgerNext :=
  ⟨rfl,KineticLedger.Runtime.sourceGeneratedPhysicalKineticLedgerNext⟩

theorem clock_preserved (runtime : LivingRuntimeState process) :
    Reentry.Runtime.reentryPhysicalTime runtime.tick.next.state.current =
      3 * Propagation.Producer.nativeClockStep := by
  change (Reentry.Runtime.reentryResponse runtime.state.current).clock = _
  rw [response]
  exact Frame.Runtime.parent_clock

/-- The runtime material's IQA decomposition reproduces the original-AO
    total energy (one-body `D`-contracted, repulsion, and pair Coulomb). -/
theorem actual_atomic_iqa_total (runtime : LivingRuntimeState process) :
    (∑ a : Fin 13, (readMaterial runtime).selfEnergy a) +
      (∑ p ∈ pairSet, (readMaterial runtime).interaction p.1 p.2) +
        (readMaterial runtime).residualEnergy =
      ∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℝ) *
        (UnifiedOrbitals.kinetic i j + Nuclear.aoAttraction i j) +
        Nuclear.totalRepulsion + pairCoulombEnergy.re := by
  rw [(material_read runtime).2]
  exact atomic_iqa_original_ao

/-- The runtime material's shared-pair (QTAIM bond-order) table totals
    48 = 2×24 electrons. -/
theorem actual_shared_pairs_total (runtime : LivingRuntimeState process) :
    (∑ ij : Option (Fin 13) × Option (Fin 13),
      (readMaterial runtime).sharedPairs ij) = 48 := by
  rw [(material_read runtime).2]
  exact shared_pairs_total

/-- The runtime material's exchange-hole population per atom/zone reproduces
    the zone population up to the D3 charge residual. -/
theorem actual_zone_population_projected (runtime : LivingRuntimeState process)
    (i : Option (Fin 13)) :
    OneBody.zonePopulation i = (readMaterial runtime).projectedPopulation i +
      ∫ x in region i, Hartree.densityResidual x := by
  rw [(material_read runtime).2]
  exact zone_population_projected i

/-- The exchange contribution to every pair interaction is nonpositive:
    the Fermi hole only lowers the inter-atomic energy. -/
theorem actual_exchange_interaction_nonpositive (runtime : LivingRuntimeState process)
    (a b : Fin 13) :
    -((readMaterial runtime).exchangeCell (some a, some b) +
      (readMaterial runtime).exchangeCell (some b, some a)) ≤ 0 := by
  rw [(material_read runtime).2]
  exact exchange_interaction_nonpositive a b

/-- Every critical point sits nearer its own nucleus than any other nucleus:
    the source basin assignment is nucleus→basin coherent. -/
theorem actual_attractor_nearest_nucleus (_runtime : LivingRuntimeState process)
    (i j : Fin 13) (different : i ≠ j) :
    dist (sourceSeed i).criticalPoint (Nuclear.nuclearPosition i) <
      dist (sourceSeed i).criticalPoint (Nuclear.nuclearPosition j) :=
  attractor_nearest_nucleus i j different

/-- The full `U` kinetic form equals the zone kinetic sum plus the
    `N/2·Σ‖C_kψ‖²` connection term: the linear-connection terms cancel by
    `∫∂_a ρ`-type antisymmetry against D3 symmetry of the density matrix. -/
theorem actual_full_U_kinetic_shift (runtime : LivingRuntimeState process) (uTime : ℝ) :
    (∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℂ) *
        spatialCovariantForm uTime i j) =
      (((∑ z : Option (Fin 13), (readMaterial runtime).parent.zoneKinetic z) +
        (1/2) * (∑ z : Option (Fin 13), OneBody.zonePopulation z) *
          ∑ axis : Fin 3,
            ‖connectionVector (spatialSlice uTime 0) axis.succ‖^2 : ℝ) : ℂ) := by
  rw [(material_read runtime).2]
  exact full_U_kinetic_shift uTime

structure PhysicalAtomicIQAClosure : Prop where
  source : AtomicIQA.Closure
  parent : type_of% complete_parent_preserved
  atomicIqaTotal : type_of% actual_atomic_iqa_total
  sharedPairsTotal : type_of% actual_shared_pairs_total
  zonePopulationProjected : type_of% actual_zone_population_projected
  exchangeNonpositive : type_of% actual_exchange_interaction_nonpositive
  attractorNearest : type_of% actual_attractor_nearest_nucleus
  fullUKineticShift : type_of% actual_full_U_kinetic_shift
  physicalOccurrence : type_of% read_commutes_with_physicalOccurrence
  wholeLedger : type_of% wholeLedger_same_occurrence
  identity : type_of% row_identity
  clock : type_of% clock_preserved
  inherited : type_of% all_original_faces
  factorization : type_of% face_factorizes
  generatedNext : type_of% generated_same_next
  originalVisit : afterFirst.current.visit = Reentry.Runtime.generatedReentryAction.target.targetVisit
  allFaces : Nonempty (Face ≃ Fin 160)

theorem sourceGeneratedPhysicalAtomicIQANext : PhysicalAtomicIQAClosure :=
  ⟨(certificate_read afterFirst).2,complete_parent_preserved,
    actual_atomic_iqa_total,actual_shared_pairs_total,
    actual_zone_population_projected,actual_exchange_interaction_nonpositive,
    actual_attractor_nearest_nucleus,actual_full_U_kinetic_shift,
    read_commutes_with_physicalOccurrence,wholeLedger_same_occurrence,
    row_identity,clock_preserved,all_original_faces,face_factorizes,
    generated_same_next,rfl,⟨faceEquiv⟩⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.AtomicIQA.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
