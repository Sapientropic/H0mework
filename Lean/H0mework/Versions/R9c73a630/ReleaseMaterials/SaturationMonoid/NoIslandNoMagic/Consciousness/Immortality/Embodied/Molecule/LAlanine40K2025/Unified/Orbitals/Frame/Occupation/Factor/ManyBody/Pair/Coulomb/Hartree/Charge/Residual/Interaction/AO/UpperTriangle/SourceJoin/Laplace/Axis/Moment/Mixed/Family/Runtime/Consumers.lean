import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Mixed.Family.Runtime.ParentConsumers

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Mixed.Family.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement.SourceFiniteData
noncomputable section

theorem actual_s_basis_count (runtime : LivingRuntimeState process) :
    (readMaterial runtime).sBases.card = 32 := by
  rw [(material_read runtime).2]
  exact Family.s_basis_count

theorem actual_p_s_quartet (runtime : LivingRuntimeState process)
    (i j : Basis)
    (hi : i ∈ (readMaterial runtime).sBases)
    (hj : j ∈ (readMaterial runtime).sBases) :
    electronRepulsion 3 2 i j = (readMaterial runtime).analyticQuartet i j := by
  rw [(material_read runtime).2] at hi hj ⊢
  exact Family.quartet_exact i j hi hj

theorem actual_p_s_target_J (runtime : LivingRuntimeState process)
    (i j : Basis)
    (hi : i ∈ (readMaterial runtime).sBases)
    (hj : j ∈ (readMaterial runtime).sBases) :
    SourceJoin.material.targetJ i j =
      (SourceJoin.sourceCoefficientAt (196 : Fin 4851) : ℝ) *
        (readMaterial runtime).analyticQuartet i j +
        (readMaterial runtime).targetRest i j := by
  rw [(material_read runtime).2] at hi hj ⊢
  exact Family.target_J_s_class i j hi hj

theorem target_report_rows (runtime : LivingRuntimeState process) :
    (Reentry.Runtime.reentryCurrentLedger runtime.tick.next.state.current).rowToIntegralExact ∧
    ((Reentry.Runtime.reentryCurrentLedger runtime.tick.next.state.current).aoPairBlocks.toList.map
      Array.size).sum = 4851 := by
  have ledger := (read_commutes_with_physicalOccurrence runtime).2.2.2
  rw [← ledger]
  exact ⟨Reentry.Producer.nuclearTargetEnergyRows_exact,
    Reentry.Producer.nuclearTargetEnergyCensus.1⟩

structure PhysicalFamilyClosure : Prop where
  source : Family.Closure
  parent : type_of% complete_parent_preserved
  sCount : type_of% actual_s_basis_count
  quartet : type_of% actual_p_s_quartet
  potential : type_of% actual_p_s_target_J
  reportRows : type_of% target_report_rows
  physicalOccurrence : type_of% read_commutes_with_physicalOccurrence
  wholeLedger : type_of% wholeLedger_same_occurrence
  identity : type_of% row_identity
  clock : type_of% clock_preserved
  inherited : type_of% all_original_faces
  factorization : type_of% face_factorizes
  generatedNext : type_of% generated_same_next
  originalVisit : afterFirst.current.visit = Reentry.Runtime.generatedReentryAction.target.targetVisit
  allFaces : Nonempty (Face ≃ Fin 120)

theorem sourceGeneratedPhysicalFamilyNext : PhysicalFamilyClosure :=
  ⟨(certificate_read afterFirst).2,complete_parent_preserved,
    actual_s_basis_count,actual_p_s_quartet,actual_p_s_target_J,
    target_report_rows,read_commutes_with_physicalOccurrence,
    wholeLedger_same_occurrence,row_identity,clock_preserved,
    all_original_faces,face_factorizes,generated_same_next,rfl,⟨faceEquiv⟩⟩

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Mixed.Family.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
