import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.Runtime.ParentConsumers

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.UnifiedOrbitals.Frame
open BasinRefinement SourceFiniteData SourceGaussianModel ContinuousGradient SourceCoulomb MeasureTheory
open SaturationMonoid.PhysicsCore ProofFreeRicherAnholonomicSource UnifiedAction YangMills.FullPairing
open scoped BigOperators
noncomputable section

theorem actual_AO_density (runtime : LivingRuntimeState process) (x : Point) :
    AO.densityFrom (readMaterial runtime).densityAO x = sourceDensity x := by
  rw [(material_read runtime).2]
  exact (certificate_read runtime).2.density x

theorem actual_J_source (runtime : LivingRuntimeState process) (i j : Basis) :
    (readMaterial runtime).jPotential i j =
      ∑ k : Basis, ∑ l : Basis,
        (readMaterial runtime).densityAO k l * UnifiedOrbitals.electronRepulsion i j k l := by
  rw [(material_read runtime).2]
  exact (certificate_read runtime).2.potential i j

theorem actual_J_symmetric (runtime : LivingRuntimeState process) (i j : Basis) :
    (readMaterial runtime).jPotential i j =
      (readMaterial runtime).jPotential j i := by
  rw [(material_read runtime).2]
  exact (certificate_read runtime).2.symmetry i j

theorem actual_D3_hartree_from_J (runtime : LivingRuntimeState process) :
    (readMaterial runtime).hartree = (1 / 2 : ℝ) *
      ∑ i : Basis, ∑ j : Basis,
        (readMaterial runtime).densityAO i j * (readMaterial runtime).jPotential i j := by
  rw [(material_read runtime).2]
  exact (certificate_read runtime).2.energy

theorem target_report_rows (runtime : LivingRuntimeState process) :
    (Reentry.Runtime.reentryCurrentLedger runtime.tick.next.state.current).rowToIntegralExact ∧
    ((Reentry.Runtime.reentryCurrentLedger runtime.tick.next.state.current).aoPairBlocks.toList.map
      Array.size).sum = 4851 := by
  have ledger := (read_commutes_with_physicalOccurrence runtime).2.2.2
  rw [← ledger]
  exact ⟨Reentry.Producer.nuclearTargetEnergyRows_exact,
    Reentry.Producer.nuclearTargetEnergyCensus.1⟩

structure PhysicalAOJClosure : Prop where
  source : AO.Closure
  parent : type_of% complete_parent_preserved
  density : type_of% actual_AO_density
  potential : type_of% actual_J_source
  symmetry : type_of% actual_J_symmetric
  energy : type_of% actual_D3_hartree_from_J
  reportRows : type_of% target_report_rows
  physicalOccurrence : type_of% read_commutes_with_physicalOccurrence
  wholeLedger : type_of% wholeLedger_same_occurrence
  identity : type_of% row_identity
  clock : type_of% clock_preserved
  inherited : type_of% all_original_faces
  factorization : type_of% face_factorizes
  generatedNext : type_of% generated_same_next
  originalVisit : afterFirst.current.visit = Reentry.Runtime.generatedReentryAction.target.targetVisit
  allFaces : Nonempty (Face ≃ Fin 102)

theorem sourceGeneratedPhysicalAOJNext : PhysicalAOJClosure :=
  ⟨(certificate_read afterFirst).2,complete_parent_preserved,
    actual_AO_density,actual_J_source,actual_J_symmetric,actual_D3_hartree_from_J,
    target_report_rows,read_commutes_with_physicalOccurrence,wholeLedger_same_occurrence,
    row_identity,clock_preserved,all_original_faces,face_factorizes,generated_same_next,
    rfl,⟨faceEquiv⟩⟩

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
