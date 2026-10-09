import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.Runtime.ParentConsumers

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement.SourceFiniteData
noncomputable section

theorem actual_upper_J (runtime : LivingRuntimeState process) (i j : Basis) :
    (readMaterial runtime).parent.parent.jPotential i j =
      (readMaterial runtime).upperJ i j := by
  rw [(material_read runtime).2]
  exact (certificate_read runtime).2.potential i j

theorem actual_upper_J_from_primitives (runtime : LivingRuntimeState process)
    (i j : Basis) :
    (readMaterial runtime).upperJ i j =
      (readMaterial runtime).parent.primitiveJ i j := by
  rw [(material_read runtime).2]
  exact (UpperTriangle.sourceJ_eq_upper i j).symm.trans
    (GaussianPair.source_J_from_primitives i j)

theorem actual_upper_hartree (runtime : LivingRuntimeState process) :
    (readMaterial runtime).parent.parent.hartree =
      (readMaterial runtime).upperHartree := by
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

theorem upper_addresses_match_target_census (runtime : LivingRuntimeState process) :
    UpperTriangle.sourceUpperPairs.card =
      ((Reentry.Runtime.reentryCurrentLedger runtime.tick.next.state.current).aoPairBlocks.toList.map
        Array.size).sum := by
  rw [UpperTriangle.source_upper_pair_count,(target_report_rows runtime).2]

structure PhysicalUpperTriangleClosure : Prop where
  source : UpperTriangle.Closure
  parent : type_of% complete_parent_preserved
  potential : type_of% actual_upper_J
  primitivePotential : type_of% actual_upper_J_from_primitives
  energy : type_of% actual_upper_hartree
  reportRows : type_of% target_report_rows
  addressCensus : type_of% upper_addresses_match_target_census
  physicalOccurrence : type_of% read_commutes_with_physicalOccurrence
  wholeLedger : type_of% wholeLedger_same_occurrence
  identity : type_of% row_identity
  clock : type_of% clock_preserved
  inherited : type_of% all_original_faces
  factorization : type_of% face_factorizes
  generatedNext : type_of% generated_same_next
  originalVisit : afterFirst.current.visit = Reentry.Runtime.generatedReentryAction.target.targetVisit
  allFaces : Nonempty (Face ≃ Fin 106)

theorem sourceGeneratedPhysicalUpperTriangleNext : PhysicalUpperTriangleClosure :=
  ⟨(certificate_read afterFirst).2,complete_parent_preserved,
    actual_upper_J,actual_upper_J_from_primitives,actual_upper_hartree,
    target_report_rows,upper_addresses_match_target_census,
    read_commutes_with_physicalOccurrence,
    wholeLedger_same_occurrence,row_identity,clock_preserved,
    all_original_faces,face_factorizes,generated_same_next,rfl,⟨faceEquiv⟩⟩

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
