import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Mixed.Runtime.ParentConsumers

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Mixed.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.UnifiedOrbitals
noncomputable section

theorem actual_cross_quartet (runtime : LivingRuntimeState process) :
    (readMaterial runtime).crossQuartet =
      (readMaterial runtime).analyticCrossQuartet := by
  rw [(material_read runtime).2]
  exact Mixed.cross_quartet_exact

theorem actual_target_J1414_cross (runtime : LivingRuntimeState process) :
    SourceJoin.material.targetJ 14 14 =
      (SourceJoin.sourceCoefficientAt (196 : Fin 4851) : ℝ) *
        (readMaterial runtime).analyticCrossQuartet +
        (readMaterial runtime).targetJ1414Rest := by
  rw [(material_read runtime).2]
  exact Mixed.target_J1414_cross_component

theorem target_report_rows (runtime : LivingRuntimeState process) :
    (Reentry.Runtime.reentryCurrentLedger runtime.tick.next.state.current).rowToIntegralExact ∧
    ((Reentry.Runtime.reentryCurrentLedger runtime.tick.next.state.current).aoPairBlocks.toList.map
      Array.size).sum = 4851 := by
  have ledger := (read_commutes_with_physicalOccurrence runtime).2.2.2
  rw [← ledger]
  exact ⟨Reentry.Producer.nuclearTargetEnergyRows_exact,
    Reentry.Producer.nuclearTargetEnergyCensus.1⟩

structure PhysicalMixedClosure : Prop where
  source : Mixed.Closure
  parent : type_of% complete_parent_preserved
  quartet : type_of% actual_cross_quartet
  potential : type_of% actual_target_J1414_cross
  sourceCensus : type_of% Moment.original_p0_s_cross_census
  reportRows : type_of% target_report_rows
  physicalOccurrence : type_of% read_commutes_with_physicalOccurrence
  wholeLedger : type_of% wholeLedger_same_occurrence
  identity : type_of% row_identity
  clock : type_of% clock_preserved
  inherited : type_of% all_original_faces
  factorization : type_of% face_factorizes
  generatedNext : type_of% generated_same_next
  originalVisit : afterFirst.current.visit = Reentry.Runtime.generatedReentryAction.target.targetVisit
  allFaces : Nonempty (Face ≃ Fin 118)

theorem sourceGeneratedPhysicalMixedNext : PhysicalMixedClosure :=
  ⟨(certificate_read afterFirst).2,complete_parent_preserved,
    actual_cross_quartet,actual_target_J1414_cross,
    Moment.original_p0_s_cross_census,target_report_rows,
    read_commutes_with_physicalOccurrence,
    wholeLedger_same_occurrence,row_identity,clock_preserved,
    all_original_faces,face_factorizes,generated_same_next,rfl,⟨faceEquiv⟩⟩

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Mixed.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
