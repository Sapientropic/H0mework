import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.Nuclear.Runtime.Facade

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.Nuclear.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.UnifiedOrbitals
open SourceGaussianModel SourceFiniteData ContinuousGradient GlobalSource WholeBandBasin Set Filter MeasureTheory Function WholeBandAttractor Metric
open scoped Topology
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
    Nuclear.material.parent = OneBody.Runtime.readMaterial OneBody.Runtime.afterFirst ∧
      type_of% OneBody.Runtime.sourceGeneratedPhysicalOneBodyZoneNext :=
  ⟨rfl,OneBody.Runtime.sourceGeneratedPhysicalOneBodyZoneNext⟩

theorem clock_preserved (runtime : LivingRuntimeState process) :
    Reentry.Runtime.reentryPhysicalTime runtime.tick.next.state.current =
      3 * Propagation.Producer.nativeClockStep := by
  change (Reentry.Runtime.reentryResponse runtime.state.current).clock = _
  rw [response]
  exact Frame.Runtime.parent_clock

theorem actual_nuclear_frame_same (runtime : LivingRuntimeState process) :
    Frame.Runtime.parentResult.nuclear =
      (Reentry.Runtime.reentryResponse runtime.state.current).nuclear := by
  rw [response]

theorem actual_zone_attraction_sum (runtime : LivingRuntimeState process)
    (a : Fin 13) :
    (∑ z : Option (Fin 13), (readMaterial runtime).zoneAttraction z a) =
      nuclearAttraction a := by
  rw [(material_read runtime).2]
  rw [show Nuclear.material.zoneAttraction = zoneAttraction from rfl]
  exact zone_attraction_sum a

theorem actual_attraction_original_ao (runtime : LivingRuntimeState process) :
    (∑ z : Option (Fin 13), ∑ a : Fin 13,
        (readMaterial runtime).zoneAttraction z a) =
      ∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℝ) * aoAttraction i j := by
  rw [(material_read runtime).2]
  rw [show Nuclear.material.zoneAttraction = zoneAttraction from rfl]
  rw [Finset.sum_comm,Finset.sum_congr rfl (fun a _ => zone_attraction_sum a)]
  exact total_attraction_original_ao

theorem actual_nuclear_pairs_account (runtime : LivingRuntimeState process) :
    ∀ row ∈ (Reentry.Runtime.reentryCurrentLedger
        runtime.tick.next.state.current).nuclearPairs.toList,
      ∃ a b : Fin 13, a < b ∧
        row[0]! = (a.val : ℤ) ∧ row[1]! = (b.val : ℤ) ∧
        row[2]! = (((nuclearChargeNat a * nuclearChargeNat b : ℕ)) : ℤ) ∧
        |nuclearRepulsion a b - (row[4]! : ℝ) / 10^9| ≤ (1 : ℝ) / 10^9 := by
  intro row hrow
  have led := (read_commutes_with_physicalOccurrence runtime).2.2.2
  rw [← nuclear_same_frame_readout] at led
  rw [← led] at hrow
  exact nuclearPairs_same_account row hrow

theorem actual_zone_one_body_total (runtime : LivingRuntimeState process) :
    (∑ z : Option (Fin 13), (readMaterial runtime).zoneOneBody z) +
        (readMaterial runtime).repulsion =
      ∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℝ) *
        (UnifiedOrbitals.kinetic i j + aoAttraction i j) + totalRepulsion := by
  rw [(material_read runtime).2]
  rw [show Nuclear.material.zoneOneBody = zoneOneBody from rfl,
    show Nuclear.material.repulsion = totalRepulsion from rfl]
  exact one_body_nuclear_total

theorem actual_partition_neutral (runtime : LivingRuntimeState process) :
    |∑ z : Option (Fin 13), (readMaterial runtime).parent.zonePopulation z -
        ∑ a : Fin 13, (readMaterial runtime).nuclearCharge a| ≤ (1/10^9 : ℝ) := by
  rw [(material_read runtime).2]
  rw [show Nuclear.material.parent.zonePopulation = OneBody.zonePopulation from rfl,
    show Nuclear.material.nuclearCharge = nuclearCharge from rfl]
  exact partition_charge_neutral

theorem actual_full_U_kinetic (runtime : LivingRuntimeState process) (uTime : ℝ) :
    (∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℂ) *
        UnifiedAction.spatialCovariantForm uTime i j) =
      (((∑ z : Option (Fin 13),
            (readMaterial runtime).parent.zoneKinetic z)) : ℂ) +
        ∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℂ) *
          ((1/2 : ℂ) * ∑ axis : Fin 3,
            ((UnifiedOrbitals.firstDerivative axis j i : ℂ) *
                UnifiedAction.connectionPair (UnifiedAction.spatialSlice uTime 0) axis.succ +
              (UnifiedOrbitals.firstDerivative axis i j : ℂ) *
                star (UnifiedAction.connectionPair (UnifiedAction.spatialSlice uTime 0) axis.succ) +
              (UnifiedOrbitals.overlap i j : ℂ) *
                UnifiedAction.connectionSquare (UnifiedAction.spatialSlice uTime 0) axis.succ)) := by
  rw [(material_read runtime).2]
  rw [show Nuclear.material.parent.zoneKinetic = OneBody.zoneKinetic from rfl]
  exact full_U_kinetic_zone_join uTime

structure PhysicalNuclearZoneClosure : Prop where
  source : Nuclear.Closure
  parent : type_of% complete_parent_preserved
  nuclearFrameSame : type_of% actual_nuclear_frame_same
  zoneAttractionSum : type_of% actual_zone_attraction_sum
  attractionAO : type_of% actual_attraction_original_ao
  pairsAccount : type_of% actual_nuclear_pairs_account
  zoneOneBodyTotal : type_of% actual_zone_one_body_total
  partitionNeutral : type_of% actual_partition_neutral
  fullU : type_of% actual_full_U_kinetic
  physicalOccurrence : type_of% read_commutes_with_physicalOccurrence
  wholeLedger : type_of% wholeLedger_same_occurrence
  identity : type_of% row_identity
  clock : type_of% clock_preserved
  inherited : type_of% all_original_faces
  factorization : type_of% face_factorizes
  generatedNext : type_of% generated_same_next
  originalVisit : afterFirst.current.visit = Reentry.Runtime.generatedReentryAction.target.targetVisit
  allFaces : Nonempty (Face ≃ Fin 156)

theorem sourceGeneratedPhysicalNuclearZoneNext : PhysicalNuclearZoneClosure :=
  ⟨(certificate_read afterFirst).2,complete_parent_preserved,
    actual_nuclear_frame_same,actual_zone_attraction_sum,
    actual_attraction_original_ao,actual_nuclear_pairs_account,
    actual_zone_one_body_total,actual_partition_neutral,actual_full_U_kinetic,
    read_commutes_with_physicalOccurrence,wholeLedger_same_occurrence,
    row_identity,clock_preserved,all_original_faces,face_factorizes,
    generated_same_next,rfl,⟨faceEquiv⟩⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.Nuclear.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
