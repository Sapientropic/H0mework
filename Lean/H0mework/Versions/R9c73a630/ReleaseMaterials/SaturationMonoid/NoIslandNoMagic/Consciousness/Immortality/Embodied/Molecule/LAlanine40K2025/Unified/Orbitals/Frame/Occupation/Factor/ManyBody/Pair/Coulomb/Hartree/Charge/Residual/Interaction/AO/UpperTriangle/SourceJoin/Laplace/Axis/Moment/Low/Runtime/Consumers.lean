import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Low.Runtime.ParentConsumers

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Low.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement.SourceFiniteData
noncomputable section

theorem actual_s_basis_count (runtime : LivingRuntimeState process) :
    (readMaterial runtime).sBases.card = 32 := by
  rw [(material_read runtime).2]
  exact Low.s_basis_count

theorem actual_low_address_count (runtime : LivingRuntimeState process) :
    (readMaterial runtime).lowAddresses.card = 11 := by
  rw [(material_read runtime).2]
  exact Low.low_address_count

theorem actual_low_quartets (runtime : LivingRuntimeState process)
    (slot : Fin 11) (i j : Basis)
    (hi : i ∈ (readMaterial runtime).sBases)
    (hj : j ∈ (readMaterial runtime).sBases) :
    electronRepulsion (Low.lowBasis slot) 2 i j =
      (readMaterial runtime).analyticQuartet slot i j := by
  rw [(material_read runtime).2] at hi hj ⊢
  exact Low.quartet_exact slot i j hi hj

theorem actual_low_target_J (runtime : LivingRuntimeState process)
    (i j : Basis)
    (hi : i ∈ (readMaterial runtime).sBases)
    (hj : j ∈ (readMaterial runtime).sBases) :
    SourceJoin.material.targetJ i j =
      (readMaterial runtime).combinedTargetJ i j := by
  rw [(material_read runtime).2] at hi hj ⊢
  exact Low.target_J_low_class i j hi hj

theorem actual_parent_p3d_same_source (runtime : LivingRuntimeState process)
    (i j : Basis)
    (hi : i ∈ (readMaterial runtime).sBases)
    (hj : j ∈ (readMaterial runtime).sBases) :
    (readMaterial runtime).parent.combinedTargetJ i j =
      (readMaterial runtime).combinedTargetJ i j := by
  rw [(material_read runtime).2] at hi hj ⊢
  exact Low.prior_p3d_same_source i j hi hj

theorem target_report_rows (runtime : LivingRuntimeState process) :
    (Reentry.Runtime.reentryCurrentLedger runtime.tick.next.state.current).rowToIntegralExact ∧
    ((Reentry.Runtime.reentryCurrentLedger runtime.tick.next.state.current).aoPairBlocks.toList.map
      Array.size).sum = 4851 := by
  have ledger := (read_commutes_with_physicalOccurrence runtime).2.2.2
  rw [← ledger]
  exact ⟨Reentry.Producer.nuclearTargetEnergyRows_exact,
    Reentry.Producer.nuclearTargetEnergyCensus.1⟩

structure PhysicalLowClosure : Prop where
  source : Low.Closure
  parent : type_of% complete_parent_preserved
  sCount : type_of% actual_s_basis_count
  lowCount : type_of% actual_low_address_count
  quartets : type_of% actual_low_quartets
  potential : type_of% actual_low_target_J
  parentSameSource : type_of% actual_parent_p3d_same_source
  reportRows : type_of% target_report_rows
  physicalOccurrence : type_of% read_commutes_with_physicalOccurrence
  wholeLedger : type_of% wholeLedger_same_occurrence
  identity : type_of% row_identity
  clock : type_of% clock_preserved
  inherited : type_of% all_original_faces
  factorization : type_of% face_factorizes
  generatedNext : type_of% generated_same_next
  originalVisit : afterFirst.current.visit = Reentry.Runtime.generatedReentryAction.target.targetVisit
  allFaces : Nonempty (Face ≃ Fin 126)

theorem sourceGeneratedPhysicalLowNext : PhysicalLowClosure :=
  ⟨(certificate_read afterFirst).2,complete_parent_preserved,
    actual_s_basis_count,actual_low_address_count,
    actual_low_quartets,actual_low_target_J,actual_parent_p3d_same_source,
    target_report_rows,read_commutes_with_physicalOccurrence,
    wholeLedger_same_occurrence,row_identity,clock_preserved,
    all_original_faces,face_factorizes,generated_same_next,rfl,⟨faceEquiv⟩⟩

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Low.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
