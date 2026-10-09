import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Positive.Runtime.ParentConsumers

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Positive.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor
open BasinRefinement SourceFiniteData SourceGaussianModel SourceCoulomb MeasureTheory
open SaturationMonoid.PhysicsCore ProofFreeRicherAnholonomicSource UnifiedAction YangMills.FullPairing
open scoped Matrix ComplexOrder BigOperators
noncomputable section

theorem actual_density_real_nonnegative (runtime : LivingRuntimeState process)
    (z : Point × Point) :
    (readMaterial runtime).parent.pairDensity z =
      ((readMaterial runtime).density z : ℂ) ∧
    0 ≤ (readMaterial runtime).density z := by
  rw [(material_read runtime).2]
  exact ⟨(certificate_read runtime).2.densityCast z,
    (certificate_read runtime).2.densityPositive z⟩

theorem actual_integrand_real_nonnegative (runtime : LivingRuntimeState process)
    (z : Point × Point) :
    (readMaterial runtime).parent.pairIntegrand z =
      ((readMaterial runtime).integrand z : ℂ) ∧
    0 ≤ (readMaterial runtime).integrand z := by
  rw [(material_read runtime).2]
  exact ⟨(certificate_read runtime).2.integrandCast z,
    (certificate_read runtime).2.integrandPositive z⟩

theorem actual_real_integrable (runtime : LivingRuntimeState process) :
    Integrable (readMaterial runtime).integrand := by
  rw [(material_read runtime).2]
  exact (certificate_read runtime).2.integrable

theorem actual_energy_real_nonnegative (runtime : LivingRuntimeState process) :
    (readMaterial runtime).parent.energy.im = 0 ∧
      0 ≤ (readMaterial runtime).energy := by
  rw [(material_read runtime).2]
  exact (certificate_read runtime).2.energyPositive

theorem actual_energy_original_ao (runtime : LivingRuntimeState process) :
    (readMaterial runtime).parent.energy = Coulomb.sourceRepulsionSum := by
  rw [(material_read runtime).2]
  exact Coulomb.material_energy_source

theorem actual_energy_direct_exchange (runtime : LivingRuntimeState process) :
    (readMaterial runtime).parent.energy =
      (readMaterial runtime).parent.direct - (readMaterial runtime).parent.exchange := by
  rw [(material_read runtime).2]
  exact Coulomb.material_direct_exchange

structure PhysicalPositiveCoulombClosure : Prop where
  source : Positive.Closure
  parent : type_of% complete_parent_preserved
  density : type_of% actual_density_real_nonnegative
  integrand : type_of% actual_integrand_real_nonnegative
  integrable : type_of% actual_real_integrable
  energy : type_of% actual_energy_real_nonnegative
  originalAO : type_of% actual_energy_original_ao
  directExchange : type_of% actual_energy_direct_exchange
  physicalOccurrence : type_of% read_commutes_with_physicalOccurrence
  wholeLedger : type_of% wholeLedger_same_occurrence
  identity : type_of% row_identity
  clock : type_of% clock_preserved
  inherited : type_of% all_original_faces
  factorization : type_of% face_factorizes
  generatedNext : type_of% generated_same_next
  originalVisit : afterFirst.current.visit = Reentry.Runtime.generatedReentryAction.target.targetVisit
  allFaces : Nonempty (Face ≃ Fin 88)

theorem sourceGeneratedPhysicalPositiveCoulombNext : PhysicalPositiveCoulombClosure :=
  ⟨(certificate_read afterFirst).2,complete_parent_preserved,
    actual_density_real_nonnegative,actual_integrand_real_nonnegative,
    actual_real_integrable,actual_energy_real_nonnegative,
    actual_energy_original_ao,actual_energy_direct_exchange,
    read_commutes_with_physicalOccurrence,wholeLedger_same_occurrence,row_identity,
    clock_preserved,all_original_faces,face_factorizes,generated_same_next,
    rfl,⟨faceEquiv⟩⟩

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Positive.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
