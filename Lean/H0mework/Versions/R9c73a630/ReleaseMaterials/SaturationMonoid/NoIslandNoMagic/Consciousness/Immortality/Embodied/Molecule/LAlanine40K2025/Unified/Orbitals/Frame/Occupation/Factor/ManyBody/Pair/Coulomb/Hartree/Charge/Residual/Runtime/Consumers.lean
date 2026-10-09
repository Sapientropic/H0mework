import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Runtime.ParentConsumers

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor
open BasinRefinement SourceFiniteData SourceGaussianModel ContinuousGradient MeasureTheory
open SaturationMonoid.PhysicsCore ProofFreeRicherAnholonomicSource UnifiedAction YangMills.FullPairing
open scoped Matrix ComplexOrder BigOperators
noncomputable section

theorem actual_source_coefficient (runtime : LivingRuntimeState process) (i k : Basis) :
    (readMaterial runtime).coefficient i k =
      Frame.normalizedDensityMatrix i k - 2 * (projector24 i k).re := by
  rw [(material_read runtime).2]
  exact (certificate_read runtime).2.coefficient i k

theorem actual_spatial_residual (runtime : LivingRuntimeState process) (x : Point) :
    (readMaterial runtime).parent.residual x =
      ∑ i : Basis, ∑ k : Basis,
        (readMaterial runtime).coefficient i k *
          Frame.normalizedOrbital i x * Frame.normalizedOrbital k x := by
  rw [(material_read runtime).2]
  exact (certificate_read runtime).2.spatialResidual x

theorem actual_source_D3_from_matrix (runtime : LivingRuntimeState process) (x : Point) :
    sourceDensity x = (readMaterial runtime).parent.projected x +
      ∑ i : Basis, ∑ k : Basis,
        (readMaterial runtime).coefficient i k *
          Frame.normalizedOrbital i x * Frame.normalizedOrbital k x := by
  rw [(material_read runtime).2]
  exact (certificate_read runtime).2.originalD3 x

theorem actual_projected_charge (runtime : LivingRuntimeState process) :
    (∫ x : Point, (readMaterial runtime).parent.projected x) = 48 := by
  rw [(material_read runtime).2]
  exact (certificate_read runtime).2.parent.electronCount

theorem actual_total_residual_bound (runtime : LivingRuntimeState process) :
    |∫ x : Point, (readMaterial runtime).parent.residual x| ≤ (1 / 10^9 : ℝ) := by
  rw [(material_read runtime).2]
  exact (certificate_read runtime).2.parent.residualBound

structure PhysicalSpatialResidualClosure : Prop where
  source : Residual.Closure
  parent : type_of% complete_parent_preserved
  coefficient : type_of% actual_source_coefficient
  spatialResidual : type_of% actual_spatial_residual
  originalD3 : type_of% actual_source_D3_from_matrix
  electronCount : type_of% actual_projected_charge
  residualBound : type_of% actual_total_residual_bound
  physicalOccurrence : type_of% read_commutes_with_physicalOccurrence
  wholeLedger : type_of% wholeLedger_same_occurrence
  identity : type_of% row_identity
  clock : type_of% clock_preserved
  inherited : type_of% all_original_faces
  factorization : type_of% face_factorizes
  generatedNext : type_of% generated_same_next
  originalVisit : afterFirst.current.visit = Reentry.Runtime.generatedReentryAction.target.targetVisit
  allFaces : Nonempty (Face ≃ Fin 94)

theorem sourceGeneratedPhysicalSpatialResidualNext : PhysicalSpatialResidualClosure :=
  ⟨(certificate_read afterFirst).2,complete_parent_preserved,
    actual_source_coefficient,actual_spatial_residual,actual_source_D3_from_matrix,
    actual_projected_charge,actual_total_residual_bound,
    read_commutes_with_physicalOccurrence,wholeLedger_same_occurrence,row_identity,
    clock_preserved,all_original_faces,face_factorizes,generated_same_next,
    rfl,⟨faceEquiv⟩⟩

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
