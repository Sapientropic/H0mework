import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Runtime.ParentConsumers

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor
open BasinRefinement SourceFiniteData SourceGaussianModel ContinuousGradient MeasureTheory
open SaturationMonoid.PhysicsCore ProofFreeRicherAnholonomicSource UnifiedAction YangMills.FullPairing
open scoped Matrix ComplexOrder
noncomputable section

theorem actual_projected_density (runtime : LivingRuntimeState process) (x : Point) :
    (readMaterial runtime).projected x =
      2 * ‖Coulomb.occupiedVector x‖^2 := by
  rw [(material_read runtime).2]
  exact (certificate_read runtime).2.occupation x

theorem actual_source_D3_decomposition (runtime : LivingRuntimeState process) (x : Point) :
    sourceDensity x = (readMaterial runtime).projected x +
      (readMaterial runtime).residual x := by
  rw [(material_read runtime).2]
  exact (certificate_read runtime).2.sourceD3 x

theorem actual_projected_electron_count (runtime : LivingRuntimeState process) :
    (∫ x : Point, (readMaterial runtime).projected x) = 48 := by
  rw [(material_read runtime).2]
  exact (certificate_read runtime).2.electronCount

theorem actual_D3_total_charge_residual (runtime : LivingRuntimeState process) :
    |∫ x : Point, (readMaterial runtime).residual x| ≤ (1 / 10^9 : ℝ) := by
  rw [(material_read runtime).2]
  exact (certificate_read runtime).2.residualBound

theorem actual_Hartree_exchange_parent (runtime : LivingRuntimeState process) :
    (readMaterial runtime).parent.parent.parent.energy =
      (readMaterial runtime).parent.direct - (readMaterial runtime).parent.exchange := by
  rw [(material_read runtime).2]
  exact Hartree.parent_energy

theorem actual_pair_energy_original_ao (runtime : LivingRuntimeState process) :
    (readMaterial runtime).parent.parent.parent.energy = Coulomb.sourceRepulsionSum := by
  rw [(material_read runtime).2]
  exact Coulomb.material_energy_source

structure PhysicalProjectedChargeClosure : Prop where
  source : Charge.Closure
  parent : type_of% complete_parent_preserved
  projected : type_of% actual_projected_density
  sourceD3 : type_of% actual_source_D3_decomposition
  electronCount : type_of% actual_projected_electron_count
  residualBound : type_of% actual_D3_total_charge_residual
  hartreeExchange : type_of% actual_Hartree_exchange_parent
  originalAO : type_of% actual_pair_energy_original_ao
  physicalOccurrence : type_of% read_commutes_with_physicalOccurrence
  wholeLedger : type_of% wholeLedger_same_occurrence
  identity : type_of% row_identity
  clock : type_of% clock_preserved
  inherited : type_of% all_original_faces
  factorization : type_of% face_factorizes
  generatedNext : type_of% generated_same_next
  originalVisit : afterFirst.current.visit = Reentry.Runtime.generatedReentryAction.target.targetVisit
  allFaces : Nonempty (Face ≃ Fin 92)

theorem sourceGeneratedPhysicalProjectedChargeNext : PhysicalProjectedChargeClosure :=
  ⟨(certificate_read afterFirst).2,complete_parent_preserved,
    actual_projected_density,actual_source_D3_decomposition,
    actual_projected_electron_count,actual_D3_total_charge_residual,
    actual_Hartree_exchange_parent,actual_pair_energy_original_ao,
    read_commutes_with_physicalOccurrence,wholeLedger_same_occurrence,row_identity,
    clock_preserved,all_original_faces,face_factorizes,generated_same_next,
    rfl,⟨faceEquiv⟩⟩

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
