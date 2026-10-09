import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Runtime.ParentConsumers

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement.SourceFiniteData
noncomputable section

theorem actual_heat_quartet (runtime : LivingRuntimeState process)
    (i j k l : Basis) :
    (readMaterial runtime).heatQuartet i j k l =
      electronRepulsion i j k l := by
  rw [(material_read runtime).2]
  exact (certificate_read runtime).2.quartet i j k l

theorem actual_heat_target_J (runtime : LivingRuntimeState process)
    (i j : Basis) :
    (readMaterial runtime).heatTargetJ i j =
      (readMaterial runtime).parent.targetJ i j := by
  rw [(material_read runtime).2]
  exact (certificate_read runtime).2.targetJ i j

theorem actual_heat_hartree (runtime : LivingRuntimeState process) :
    (readMaterial runtime).heatHartree = Interaction.d3HartreeEnergy := by
  rw [(material_read runtime).2]
  exact (certificate_read runtime).2.hartree

theorem target_report_rows (runtime : LivingRuntimeState process) :
    (Reentry.Runtime.reentryCurrentLedger runtime.tick.next.state.current).rowToIntegralExact ∧
    ((Reentry.Runtime.reentryCurrentLedger runtime.tick.next.state.current).aoPairBlocks.toList.map
      Array.size).sum = 4851 := by
  have ledger := (read_commutes_with_physicalOccurrence runtime).2.2.2
  rw [← ledger]
  exact ⟨Reentry.Producer.nuclearTargetEnergyRows_exact,
    Reentry.Producer.nuclearTargetEnergyCensus.1⟩

structure PhysicalLaplaceClosure : Prop where
  source : Laplace.Closure
  parent : type_of% complete_parent_preserved
  quartet : type_of% actual_heat_quartet
  potential : type_of% actual_heat_target_J
  energy : type_of% actual_heat_hartree
  reportRows : type_of% target_report_rows
  physicalOccurrence : type_of% read_commutes_with_physicalOccurrence
  wholeLedger : type_of% wholeLedger_same_occurrence
  identity : type_of% row_identity
  clock : type_of% clock_preserved
  inherited : type_of% all_original_faces
  factorization : type_of% face_factorizes
  generatedNext : type_of% generated_same_next
  originalVisit : afterFirst.current.visit = Reentry.Runtime.generatedReentryAction.target.targetVisit
  allFaces : Nonempty (Face ≃ Fin 110)

theorem sourceGeneratedPhysicalLaplaceNext : PhysicalLaplaceClosure :=
  ⟨(certificate_read afterFirst).2,complete_parent_preserved,
    actual_heat_quartet,actual_heat_target_J,actual_heat_hartree,
    target_report_rows,read_commutes_with_physicalOccurrence,
    wholeLedger_same_occurrence,row_identity,clock_preserved,
    all_original_faces,face_factorizes,generated_same_next,rfl,⟨faceEquiv⟩⟩

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
