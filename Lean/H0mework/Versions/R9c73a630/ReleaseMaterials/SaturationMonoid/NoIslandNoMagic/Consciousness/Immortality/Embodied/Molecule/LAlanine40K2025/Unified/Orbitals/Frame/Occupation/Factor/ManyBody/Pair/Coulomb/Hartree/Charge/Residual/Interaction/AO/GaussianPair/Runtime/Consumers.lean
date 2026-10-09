import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair.Runtime.ParentConsumers

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.UnifiedOrbitals
open LAlanine40K2025.UnifiedOrbitals.Frame
open BasinRefinement SourceFiniteData SourceGaussianModel ContinuousGradient SourceCoulomb MeasureTheory
open SaturationMonoid.PhysicsCore ProofFreeRicherAnholonomicSource UnifiedAction YangMills.FullPairing
open scoped BigOperators
noncomputable section

theorem actual_pair_field (runtime : LivingRuntimeState process)
    (i j : Basis) (x : Point) :
    ao i x * ao j x = (readMaterial runtime).pairField i j x := by
  rw [(material_read runtime).2]
  exact (certificate_read runtime).2.pairField i j x

theorem actual_primitive_quartet (runtime : LivingRuntimeState process)
    (i j k l : Basis) :
    (readMaterial runtime).primitiveQuartet i j k l =
      UnifiedOrbitals.electronRepulsion i j k l := by
  rw [(material_read runtime).2]
  exact (certificate_read runtime).2.quartet i j k l

theorem actual_primitive_integrable (runtime : LivingRuntimeState process)
    (i j k l : Basis) (left right nextLeft nextRight : Term)
    (hleft : left ∈ sourceTerms i) (hright : right ∈ sourceTerms j)
    (hnextLeft : nextLeft ∈ sourceTerms k) (hnextRight : nextRight ∈ sourceTerms l) :
    Integrable (fun z : Point × Point =>
      pairShape left right z.1 * pairShape nextLeft nextRight z.2 *
        kernel (z.2 - z.1)) :=
  (certificate_read runtime).2.integrability i j k l left right nextLeft nextRight
    hleft hright hnextLeft hnextRight

theorem actual_J_from_primitives (runtime : LivingRuntimeState process) (i j : Basis) :
    (readMaterial runtime).parent.jPotential i j =
      (readMaterial runtime).primitiveJ i j := by
  rw [(material_read runtime).2]
  exact (certificate_read runtime).2.potential i j

theorem actual_hartree_from_primitives (runtime : LivingRuntimeState process) :
    (readMaterial runtime).parent.hartree = (1 / 2 : ℝ) *
      ∑ i : Basis, ∑ j : Basis,
        (readMaterial runtime).parent.densityAO i j *
          (readMaterial runtime).primitiveJ i j := by
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

structure PhysicalGaussianPairClosure : Prop where
  source : GaussianPair.Closure
  parent : type_of% complete_parent_preserved
  pairField : type_of% actual_pair_field
  quartet : type_of% actual_primitive_quartet
  integrability : type_of% actual_primitive_integrable
  potential : type_of% actual_J_from_primitives
  energy : type_of% actual_hartree_from_primitives
  reportRows : type_of% target_report_rows
  physicalOccurrence : type_of% read_commutes_with_physicalOccurrence
  wholeLedger : type_of% wholeLedger_same_occurrence
  identity : type_of% row_identity
  clock : type_of% clock_preserved
  inherited : type_of% all_original_faces
  factorization : type_of% face_factorizes
  generatedNext : type_of% generated_same_next
  originalVisit : afterFirst.current.visit = Reentry.Runtime.generatedReentryAction.target.targetVisit
  allFaces : Nonempty (Face ≃ Fin 104)

theorem sourceGeneratedPhysicalGaussianPairNext : PhysicalGaussianPairClosure :=
  ⟨(certificate_read afterFirst).2,complete_parent_preserved,
    actual_pair_field,actual_primitive_quartet,actual_primitive_integrable,
    actual_J_from_primitives,actual_hartree_from_primitives,target_report_rows,
    read_commutes_with_physicalOccurrence,wholeLedger_same_occurrence,row_identity,
    clock_preserved,all_original_faces,face_factorizes,generated_same_next,
    rfl,⟨faceEquiv⟩⟩

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
