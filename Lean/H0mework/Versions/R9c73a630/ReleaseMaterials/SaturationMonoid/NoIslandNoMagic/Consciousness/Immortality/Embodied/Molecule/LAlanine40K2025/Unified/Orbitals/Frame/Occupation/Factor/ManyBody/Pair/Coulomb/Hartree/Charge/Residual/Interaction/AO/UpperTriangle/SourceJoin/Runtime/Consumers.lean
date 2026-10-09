import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Runtime.ParentConsumers

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement.SourceFiniteData
noncomputable section

theorem actual_target_row (runtime : LivingRuntimeState process)
    (address : Fin 4851) : SourceJoin.targetRowCertified address.val :=
  (certificate_read runtime).2.rows address

theorem target_row_same_runtime (runtime : LivingRuntimeState process)
    (address : Fin 4851) :
    SourceJoin.targetAORow address.val =
      ((((Reentry.Runtime.reentryCurrentLedger runtime.tick.next.state.current).aoPairBlocks)[address.val / 64]!)[address.val % 64]!) := by
  have ledger := (read_commutes_with_physicalOccurrence runtime).2.2.2
  rw [← ledger]
  rfl

theorem actual_target_pair_equiv (runtime : LivingRuntimeState process) :
    Nonempty (Fin 4851 ≃ UpperTriangle.sourceUpperPairs) :=
  (certificate_read runtime).2.addressEquiv

theorem actual_target_coefficient_bound (runtime : LivingRuntimeState process)
    (address : Fin 4851) :
    |(readMaterial runtime).sourceCoefficient address -
      (readMaterial runtime).reportCoefficient address| <
        (1 : ℚ) / 10^12 := by
  rw [(material_read runtime).2]
  exact (certificate_read runtime).2.reportBound address

theorem actual_target_J (runtime : LivingRuntimeState process) (i j : Basis) :
    (readMaterial runtime).targetJ i j =
      (readMaterial runtime).parent.upperJ i j := by
  rw [(material_read runtime).2]
  exact (certificate_read runtime).2.potential i j

theorem actual_target_J_report_bound (runtime : LivingRuntimeState process)
    (i j : Basis) :
    |(readMaterial runtime).targetJ i j -
      (readMaterial runtime).reportWeightedJ i j| ≤
        (readMaterial runtime).quartetErrorWeight i j := by
  rw [(material_read runtime).2]
  exact (certificate_read runtime).2.potentialReportBound i j

theorem target_report_rows (runtime : LivingRuntimeState process) :
    (Reentry.Runtime.reentryCurrentLedger runtime.tick.next.state.current).rowToIntegralExact ∧
    ((Reentry.Runtime.reentryCurrentLedger runtime.tick.next.state.current).aoPairBlocks.toList.map
      Array.size).sum = 4851 := by
  have ledger := (read_commutes_with_physicalOccurrence runtime).2.2.2
  rw [← ledger]
  exact ⟨Reentry.Producer.nuclearTargetEnergyRows_exact,
    Reentry.Producer.nuclearTargetEnergyCensus.1⟩

structure PhysicalSourceJoinClosure : Prop where
  source : SourceJoin.Closure
  parent : type_of% complete_parent_preserved
  rows : type_of% actual_target_row
  rowSameRuntime : type_of% target_row_same_runtime
  addressEquiv : type_of% actual_target_pair_equiv
  coefficientBound : type_of% actual_target_coefficient_bound
  potential : type_of% actual_target_J
  potentialReportBound : type_of% actual_target_J_report_bound
  reportRows : type_of% target_report_rows
  physicalOccurrence : type_of% read_commutes_with_physicalOccurrence
  wholeLedger : type_of% wholeLedger_same_occurrence
  identity : type_of% row_identity
  clock : type_of% clock_preserved
  inherited : type_of% all_original_faces
  factorization : type_of% face_factorizes
  generatedNext : type_of% generated_same_next
  originalVisit : afterFirst.current.visit = Reentry.Runtime.generatedReentryAction.target.targetVisit
  allFaces : Nonempty (Face ≃ Fin 108)

theorem sourceGeneratedPhysicalSourceJoinNext : PhysicalSourceJoinClosure :=
  ⟨(certificate_read afterFirst).2,complete_parent_preserved,
    actual_target_row,target_row_same_runtime,actual_target_pair_equiv,
    actual_target_coefficient_bound,actual_target_J,
    actual_target_J_report_bound,
    target_report_rows,read_commutes_with_physicalOccurrence,
    wholeLedger_same_occurrence,row_identity,clock_preserved,
    all_original_faces,face_factorizes,generated_same_next,rfl,⟨faceEquiv⟩⟩

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
