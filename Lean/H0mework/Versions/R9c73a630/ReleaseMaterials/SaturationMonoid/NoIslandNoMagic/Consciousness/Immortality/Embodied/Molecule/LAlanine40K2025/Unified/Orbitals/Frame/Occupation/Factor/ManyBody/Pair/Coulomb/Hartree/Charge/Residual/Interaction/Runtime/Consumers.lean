import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.Runtime.ParentConsumers

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor
open BasinRefinement SourceFiniteData SourceGaussianModel ContinuousGradient SourceCoulomb MeasureTheory
open SaturationMonoid.PhysicsCore ProofFreeRicherAnholonomicSource UnifiedAction YangMills.FullPairing
open scoped Matrix ComplexOrder
noncomputable section

theorem actual_D3_hartree_integral (runtime : LivingRuntimeState process) :
    (readMaterial runtime).d3Hartree =
      (1 / 2 : ℝ) * ∫ z : Point × Point,
        sourceDensity z.1 * sourceDensity z.2 * kernel (z.2-z.1) := by
  rw [(material_read runtime).2]
  exact (certificate_read runtime).2.originalIntegral

theorem actual_occupied_hartree_integral (runtime : LivingRuntimeState process) :
    (readMaterial runtime).occupiedHartree =
      (readMaterial runtime).parent.parent.parent.direct.re := by
  rw [(material_read runtime).2]
  exact (certificate_read runtime).2.occupiedIntegral

theorem actual_D3_four_center (runtime : LivingRuntimeState process) :
    (readMaterial runtime).d3Hartree =
      (1 / 2 : ℝ) * Interaction.fourCenter Interaction.d3Matrix Interaction.d3Matrix := by
  rw [(material_read runtime).2]
  exact (certificate_read runtime).2.originalFourCenter

theorem actual_energy_residual (runtime : LivingRuntimeState process) :
    (readMaterial runtime).d3Hartree - (readMaterial runtime).occupiedHartree =
      (1 / 2 : ℝ) * ((readMaterial runtime).leftResidual +
        (readMaterial runtime).rightResidual) := by
  rw [(material_read runtime).2]
  exact (certificate_read runtime).2.residual

theorem actual_source_coefficient (runtime : LivingRuntimeState process) (i k : Basis) :
    (readMaterial runtime).parent.coefficient i k =
      Frame.normalizedDensityMatrix i k - 2 * (projector24 i k).re := by
  rw [(material_read runtime).2]
  exact Residual.actual_coefficient i k

structure PhysicalHartreeResidualClosure : Prop where
  source : Interaction.Closure
  parent : type_of% complete_parent_preserved
  d3Integral : type_of% actual_D3_hartree_integral
  occupationIntegral : type_of% actual_occupied_hartree_integral
  fourCenter : type_of% actual_D3_four_center
  energyResidual : type_of% actual_energy_residual
  sourceCoefficient : type_of% actual_source_coefficient
  physicalOccurrence : type_of% read_commutes_with_physicalOccurrence
  wholeLedger : type_of% wholeLedger_same_occurrence
  identity : type_of% row_identity
  clock : type_of% clock_preserved
  inherited : type_of% all_original_faces
  factorization : type_of% face_factorizes
  generatedNext : type_of% generated_same_next
  originalVisit : afterFirst.current.visit = Reentry.Runtime.generatedReentryAction.target.targetVisit
  allFaces : Nonempty (Face ≃ Fin 96)

theorem sourceGeneratedPhysicalHartreeResidualNext : PhysicalHartreeResidualClosure :=
  ⟨(certificate_read afterFirst).2,complete_parent_preserved,
    actual_D3_hartree_integral,actual_occupied_hartree_integral,
    actual_D3_four_center,actual_energy_residual,actual_source_coefficient,
    read_commutes_with_physicalOccurrence,wholeLedger_same_occurrence,row_identity,
    clock_preserved,all_original_faces,face_factorizes,generated_same_next,
    rfl,⟨faceEquiv⟩⟩

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
