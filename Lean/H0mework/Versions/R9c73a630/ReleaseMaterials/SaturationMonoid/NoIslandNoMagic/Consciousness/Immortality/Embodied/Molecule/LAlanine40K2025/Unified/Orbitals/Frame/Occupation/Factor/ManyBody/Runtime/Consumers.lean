import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Runtime.ParentConsumers

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor
open BasinRefinement SourceFiniteData
open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
noncomputable section

theorem actual_slater_pairing (runtime : LivingRuntimeState process) :
    (readMaterial runtime).dual (readMaterial runtime).state = 1 := by
  rw [(material_read runtime).2]
  exact (certificate_read runtime).2.paired

theorem actual_slater_nonzero (runtime : LivingRuntimeState process) :
    (readMaterial runtime).state ≠ 0 := by
  rw [(material_read runtime).2]
  exact (certificate_read runtime).2.nonzero

theorem actual_U_spatial_slater (runtime : LivingRuntimeState process) (time : ℝ) :
    (readMaterial runtime).spatialState time ≠ 0 := by
  rw [(material_read runtime).2]
  exact (certificate_read runtime).2.spatialNonzero time

theorem actual_U_spatial_source (runtime : LivingRuntimeState process) (time : ℝ) :
    (readMaterial runtime).spatialState time =
      exteriorPower.ιMulti ℂ 48
        (fun k => ManyBody.preparedSpinWave time (ManyBody.orbitalFamily k)) := by
  rw [(material_read runtime).2]
  exact (certificate_read runtime).2.spatialSource time

theorem actual_slater_exchange (runtime : LivingRuntimeState process)
    (σ : Equiv.Perm (Fin 48)) :
    exteriorPower.ιMulti ℂ 48 (ManyBody.orbitalFamily ∘ σ) =
      Equiv.Perm.sign σ • (readMaterial runtime).state := by
  rw [(material_read runtime).2]
  exact (certificate_read runtime).2.exchange σ

theorem actual_one_body (runtime : LivingRuntimeState process) (x y : SpinBasis) :
    (readMaterial runtime).oneBody x y =
      (readMaterial runtime).parent.parent.spinProjector x y := by
  rw [(material_read runtime).2]
  exact (certificate_read runtime).2.oneBody x y

theorem actual_U_gamma_from_state (runtime : LivingRuntimeState process) :
    ‖(readMaterial runtime).parent.originalGamma -
      (readMaterial runtime).spinSummed‖ < (1 / 10^5 : ℝ) := by
  rw [(material_read runtime).2]
  exact (certificate_read runtime).2.gammaError

theorem actual_occupied_count (runtime : LivingRuntimeState process) :
    (readMaterial runtime).parent.occupiedCount = 24 := by
  rw [(material_read runtime).2]
  exact (certificate_read runtime).2.parent.count

structure PhysicalSlaterOneBodyClosure : Prop where
  source : ManyBody.Closure
  parent : type_of% complete_parent_preserved
  paired : type_of% actual_slater_pairing
  nonzero : type_of% actual_slater_nonzero
  spatialNonzero : type_of% actual_U_spatial_slater
  spatialSource : type_of% actual_U_spatial_source
  exchange : type_of% actual_slater_exchange
  oneBody : type_of% actual_one_body
  originalGamma : type_of% actual_U_gamma_from_state
  count : type_of% actual_occupied_count
  physicalOccurrence : type_of% read_commutes_with_physicalOccurrence
  wholeLedger : type_of% wholeLedger_same_occurrence
  identity : type_of% row_identity
  clock : type_of% clock_preserved
  inherited : type_of% all_original_faces
  factorization : type_of% face_factorizes
  generatedNext : type_of% generated_same_next
  originalVisit : afterFirst.current.visit = Reentry.Runtime.generatedReentryAction.target.targetVisit
  allFaces : Nonempty (Face ≃ Fin 82)

theorem sourceGeneratedPhysicalSlaterNext : PhysicalSlaterOneBodyClosure :=
  ⟨(certificate_read afterFirst).2,complete_parent_preserved,actual_slater_pairing,
    actual_slater_nonzero,actual_U_spatial_slater,actual_U_spatial_source,
    actual_slater_exchange,actual_one_body,
    actual_U_gamma_from_state,actual_occupied_count,read_commutes_with_physicalOccurrence,
    wholeLedger_same_occurrence,row_identity,clock_preserved,all_original_faces,
    face_factorizes,generated_same_next,rfl,⟨faceEquiv⟩⟩

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
