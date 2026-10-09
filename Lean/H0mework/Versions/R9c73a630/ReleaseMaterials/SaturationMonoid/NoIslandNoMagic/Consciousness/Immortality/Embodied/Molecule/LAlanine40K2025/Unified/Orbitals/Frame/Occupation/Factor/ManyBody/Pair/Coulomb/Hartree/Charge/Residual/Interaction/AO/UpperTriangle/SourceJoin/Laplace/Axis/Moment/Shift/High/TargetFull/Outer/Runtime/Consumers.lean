import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetFull.Outer.Runtime.ParentConsumers

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetFull.Outer.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement.SourceFiniteData
noncomputable section

theorem actual_compact_interval (runtime : LivingRuntimeState process) :
    (readMaterial runtime).integrationInterval = Set.Ioo (0 : ℝ) 1 := by
  rw [(material_read runtime).2]
  exact Outer.interval_identity

theorem actual_full_quartets (runtime : LivingRuntimeState process)
    (sourceLeft sourceRight targetLeft targetRight : Basis) :
    electronRepulsion sourceLeft sourceRight targetLeft targetRight =
      (readMaterial runtime).analyticQuartet sourceLeft sourceRight
        targetLeft targetRight := by
  rw [(material_read runtime).2]
  exact Outer.quartet_exact sourceLeft sourceRight
    targetLeft targetRight

theorem actual_target_full_J (runtime : LivingRuntimeState process)
    (i j : Basis) :
    SourceJoin.material.targetJ i j =
      (readMaterial runtime).combinedTargetJ i j := by
  rw [(material_read runtime).2]
  exact Outer.target_J_all i j

theorem actual_parent_full_same_source (runtime : LivingRuntimeState process)
    (i j : Basis) :
    (readMaterial runtime).parent.combinedTargetJ i j =
      (readMaterial runtime).combinedTargetJ i j := by
  rw [(material_read runtime).2]
  exact Outer.installed_parent_same_source i j

theorem target_report_rows (runtime : LivingRuntimeState process) :
    (Reentry.Runtime.reentryCurrentLedger runtime.tick.next.state.current).rowToIntegralExact ∧
    ((Reentry.Runtime.reentryCurrentLedger runtime.tick.next.state.current).aoPairBlocks.toList.map
      Array.size).sum = 4851 := by
  have ledger := (read_commutes_with_physicalOccurrence runtime).2.2.2
  rw [← ledger]
  exact ⟨Reentry.Producer.nuclearTargetEnergyRows_exact,
    Reentry.Producer.nuclearTargetEnergyCensus.1⟩

structure PhysicalOuterClosure : Prop where
  source : Outer.Closure
  parent : type_of% complete_parent_preserved
  compactInterval : type_of% actual_compact_interval
  quartets : type_of% actual_full_quartets
  potential : type_of% actual_target_full_J
  parentSameSource : type_of% actual_parent_full_same_source
  reportRows : type_of% target_report_rows
  physicalOccurrence : type_of% read_commutes_with_physicalOccurrence
  wholeLedger : type_of% wholeLedger_same_occurrence
  identity : type_of% row_identity
  clock : type_of% clock_preserved
  inherited : type_of% all_original_faces
  factorization : type_of% face_factorizes
  generatedNext : type_of% generated_same_next
  originalVisit : afterFirst.current.visit = Reentry.Runtime.generatedReentryAction.target.targetVisit
  allFaces : Nonempty (Face ≃ Fin 138)

theorem sourceGeneratedPhysicalOuterNext : PhysicalOuterClosure :=
  ⟨(certificate_read afterFirst).2,complete_parent_preserved,
    actual_compact_interval,actual_full_quartets,actual_target_full_J,
    actual_parent_full_same_source,
    target_report_rows,read_commutes_with_physicalOccurrence,
    wholeLedger_same_occurrence,row_identity,clock_preserved,
    all_original_faces,face_factorizes,generated_same_next,rfl,⟨faceEquiv⟩⟩

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetFull.Outer.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
