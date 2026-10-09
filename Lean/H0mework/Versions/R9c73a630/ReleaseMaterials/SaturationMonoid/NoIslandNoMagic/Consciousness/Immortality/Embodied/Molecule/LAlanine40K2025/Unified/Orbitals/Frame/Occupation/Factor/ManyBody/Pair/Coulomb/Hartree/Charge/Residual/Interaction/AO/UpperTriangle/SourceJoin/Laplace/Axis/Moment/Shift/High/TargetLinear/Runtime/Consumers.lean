import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetLinear.Runtime.ParentConsumers

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetLinear.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement.SourceFiniteData
noncomputable section

theorem actual_s_basis_count (runtime : LivingRuntimeState process) :
    (readMaterial runtime).sBases.card = 32 := by
  rw [(material_read runtime).2]
  exact TargetLinear.s_basis_count

theorem actual_linear_basis_count (runtime : LivingRuntimeState process) :
    (readMaterial runtime).linearBases.card = 86 := by
  rw [(material_read runtime).2]
  exact TargetLinear.linear_basis_count

theorem actual_analytic_target_count (runtime : LivingRuntimeState process) :
    (readMaterial runtime).analyticTargets.card = 4480 := by
  rw [(material_read runtime).2]
  exact TargetLinear.analytic_target_count

theorem actual_linear_quartets (runtime : LivingRuntimeState process)
    (sourceLeft sourceRight targetLinear targetS : Basis)
    (hlinear : targetLinear ∈ (readMaterial runtime).linearBases)
    (hs : targetS ∈ (readMaterial runtime).sBases) :
    electronRepulsion sourceLeft sourceRight targetLinear targetS =
      (readMaterial runtime).analyticQuartet sourceLeft sourceRight
        targetLinear targetS := by
  rw [(material_read runtime).2] at hlinear hs ⊢
  exact TargetLinear.quartet_exact sourceLeft sourceRight
    targetLinear targetS hlinear hs

theorem actual_target_linear_J (runtime : LivingRuntimeState process)
    (i j : Basis) :
    SourceJoin.material.targetJ i j =
      (readMaterial runtime).combinedTargetJ i j := by
  rw [(material_read runtime).2]
  exact TargetLinear.target_J_all i j

theorem actual_parent_high_same_source (runtime : LivingRuntimeState process)
    (i j : Basis)
    (hi : i ∈ (readMaterial runtime).sBases)
    (hj : j ∈ (readMaterial runtime).sBases) :
    (readMaterial runtime).parent.combinedTargetJ i j =
      (readMaterial runtime).combinedTargetJ i j := by
  rw [(material_read runtime).2] at hi hj ⊢
  exact TargetLinear.parent_same_source i j hi hj

theorem target_report_rows (runtime : LivingRuntimeState process) :
    (Reentry.Runtime.reentryCurrentLedger runtime.tick.next.state.current).rowToIntegralExact ∧
    ((Reentry.Runtime.reentryCurrentLedger runtime.tick.next.state.current).aoPairBlocks.toList.map
      Array.size).sum = 4851 := by
  have ledger := (read_commutes_with_physicalOccurrence runtime).2.2.2
  rw [← ledger]
  exact ⟨Reentry.Producer.nuclearTargetEnergyRows_exact,
    Reentry.Producer.nuclearTargetEnergyCensus.1⟩

structure PhysicalTargetLinearClosure : Prop where
  source : TargetLinear.Closure
  parent : type_of% complete_parent_preserved
  sCount : type_of% actual_s_basis_count
  linearCount : type_of% actual_linear_basis_count
  targetCount : type_of% actual_analytic_target_count
  quartets : type_of% actual_linear_quartets
  potential : type_of% actual_target_linear_J
  parentSameSource : type_of% actual_parent_high_same_source
  reportRows : type_of% target_report_rows
  physicalOccurrence : type_of% read_commutes_with_physicalOccurrence
  wholeLedger : type_of% wholeLedger_same_occurrence
  identity : type_of% row_identity
  clock : type_of% clock_preserved
  inherited : type_of% all_original_faces
  factorization : type_of% face_factorizes
  generatedNext : type_of% generated_same_next
  originalVisit : afterFirst.current.visit = Reentry.Runtime.generatedReentryAction.target.targetVisit
  allFaces : Nonempty (Face ≃ Fin 134)

theorem sourceGeneratedPhysicalTargetLinearNext : PhysicalTargetLinearClosure :=
  ⟨(certificate_read afterFirst).2,complete_parent_preserved,
    actual_s_basis_count,actual_linear_basis_count,actual_analytic_target_count,
    actual_linear_quartets,actual_target_linear_J,
    actual_parent_high_same_source,
    target_report_rows,read_commutes_with_physicalOccurrence,
    wholeLedger_same_occurrence,row_identity,clock_preserved,
    all_original_faces,face_factorizes,generated_same_next,rfl,⟨faceEquiv⟩⟩

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetLinear.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
