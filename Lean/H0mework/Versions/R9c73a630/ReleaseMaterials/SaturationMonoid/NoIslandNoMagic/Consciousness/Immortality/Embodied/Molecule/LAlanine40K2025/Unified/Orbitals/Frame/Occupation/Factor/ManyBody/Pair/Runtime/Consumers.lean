import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Runtime.ParentConsumers

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor
open BasinRefinement SourceFiniteData
open scoped Matrix ComplexOrder
noncomputable section

theorem actual_same_fermion_state (runtime : LivingRuntimeState process) :
    (readMaterial runtime).parent.state = ManyBody.slaterState := by
  rw [(material_read runtime).2]
  exact (certificate_read runtime).2.sourceState

theorem actual_two_body_wick (runtime : LivingRuntimeState process)
    (x₁ x₂ y₁ y₂ : SpinBasis) :
    (readMaterial runtime).twoBody x₁ x₂ y₁ y₂ =
      (readMaterial runtime).parent.oneBody x₁ y₁ *
        (readMaterial runtime).parent.oneBody x₂ y₂ -
      (readMaterial runtime).parent.oneBody x₁ y₂ *
        (readMaterial runtime).parent.oneBody x₂ y₁ := by
  rw [(material_read runtime).2]
  exact (certificate_read runtime).2.oneBody x₁ x₂ y₁ y₂

theorem actual_source_two_body (runtime : LivingRuntimeState process)
    (x₁ x₂ y₁ y₂ : SpinBasis) :
    (readMaterial runtime).twoBody x₁ x₂ y₁ y₂ =
      spinProjector x₁ y₁ * spinProjector x₂ y₂ -
        spinProjector x₁ y₂ * spinProjector x₂ y₁ := by
  rw [(material_read runtime).2]
  exact (certificate_read runtime).2.projector x₁ x₂ y₁ y₂

theorem actual_spin_summed_two_body (runtime : LivingRuntimeState process)
    (i j k l : Basis) :
    (readMaterial runtime).spinSummed i j k l =
      (4 : ℂ) * projector24 i k * projector24 j l -
        (2 : ℂ) * projector24 i l * projector24 j k := by
  rw [(material_read runtime).2]
  exact (certificate_read runtime).2.spinSum i j k l

theorem actual_pair_exchange (runtime : LivingRuntimeState process)
    (x₁ x₂ y₁ y₂ : SpinBasis) :
    (readMaterial runtime).twoBody x₂ x₁ y₁ y₂ =
      -(readMaterial runtime).twoBody x₁ x₂ y₁ y₂ := by
  rw [(material_read runtime).2]
  exact (certificate_read runtime).2.exchange x₁ x₂ y₁ y₂

theorem actual_pair_diagonal_zero (runtime : LivingRuntimeState process)
    (x y₁ y₂ : SpinBasis) :
    (readMaterial runtime).twoBody x x y₁ y₂ = 0 := by
  rw [(material_read runtime).2]
  exact (certificate_read runtime).2.diagonal x y₁ y₂

structure PhysicalTwoBodyClosure : Prop where
  source : Pair.Closure
  parent : type_of% complete_parent_preserved
  state : type_of% actual_same_fermion_state
  wick : type_of% actual_two_body_wick
  sourcePair : type_of% actual_source_two_body
  spinSum : type_of% actual_spin_summed_two_body
  exchange : type_of% actual_pair_exchange
  diagonal : type_of% actual_pair_diagonal_zero
  physicalOccurrence : type_of% read_commutes_with_physicalOccurrence
  wholeLedger : type_of% wholeLedger_same_occurrence
  identity : type_of% row_identity
  clock : type_of% clock_preserved
  inherited : type_of% all_original_faces
  factorization : type_of% face_factorizes
  generatedNext : type_of% generated_same_next
  originalVisit : afterFirst.current.visit = Reentry.Runtime.generatedReentryAction.target.targetVisit
  allFaces : Nonempty (Face ≃ Fin 84)

theorem sourceGeneratedPhysicalTwoBodyNext : PhysicalTwoBodyClosure :=
  ⟨(certificate_read afterFirst).2,complete_parent_preserved,actual_same_fermion_state,
    actual_two_body_wick,actual_source_two_body,actual_spin_summed_two_body,
    actual_pair_exchange,actual_pair_diagonal_zero,read_commutes_with_physicalOccurrence,
    wholeLedger_same_occurrence,row_identity,clock_preserved,all_original_faces,
    face_factorizes,generated_same_next,rfl,⟨faceEquiv⟩⟩

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
