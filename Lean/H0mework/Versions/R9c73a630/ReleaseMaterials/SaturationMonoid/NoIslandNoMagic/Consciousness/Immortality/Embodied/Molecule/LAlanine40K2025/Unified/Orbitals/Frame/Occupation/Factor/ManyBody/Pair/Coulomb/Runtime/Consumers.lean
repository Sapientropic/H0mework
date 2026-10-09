import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Runtime.ParentConsumers

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor
open BasinRefinement SourceFiniteData SourceGaussianModel SourceCoulomb MeasureTheory
open SaturationMonoid.PhysicsCore ProofFreeRicherAnholonomicSource UnifiedAction YangMills.FullPairing
open scoped Matrix ComplexOrder BigOperators
noncomputable section

theorem actual_density_from_pair (runtime : LivingRuntimeState process)
    (z : Point × Point) : (readMaterial runtime).pairDensity z =
      ∑ i : Basis, ∑ j : Basis, ∑ k : Basis, ∑ l : Basis,
        (readMaterial runtime).parent.spinSummed i j k l *
          (Frame.normalizedOrbital i z.1 * Frame.normalizedOrbital k z.1 *
            (Frame.normalizedOrbital j z.2 * Frame.normalizedOrbital l z.2) : ℝ) := by
  rw [(material_read runtime).2]
  exact (certificate_read runtime).2.densitySource z

theorem actual_density_full_U (runtime : LivingRuntimeState process)
    (time : ℝ) (z : Point × Point) : (readMaterial runtime).pairDensity z =
      ∑ i : Basis, ∑ j : Basis, ∑ k : Basis, ∑ l : Basis,
        (readMaterial runtime).parent.spinSummed i j k l *
          inner ℂ (Frame.normalizedSection i time z.1) (Frame.normalizedSection k time z.1) *
          inner ℂ (Frame.normalizedSection j time z.2) (Frame.normalizedSection l time z.2) := by
  rw [(material_read runtime).2]
  exact (certificate_read runtime).2.densityU time z

theorem actual_pair_integrable (runtime : LivingRuntimeState process) :
    Integrable (readMaterial runtime).pairIntegrand := by
  rw [(material_read runtime).2]
  exact (certificate_read runtime).2.integrable

theorem actual_pair_energy_integral (runtime : LivingRuntimeState process) :
    (readMaterial runtime).energy =
      (1 / 2 : ℂ) * ∫ z : Point × Point, (readMaterial runtime).pairIntegrand z := by
  rw [(material_read runtime).2]
  rfl

theorem actual_pair_energy_source (runtime : LivingRuntimeState process) :
    (readMaterial runtime).energy = Coulomb.sourceRepulsionSum := by
  rw [(material_read runtime).2]
  exact (certificate_read runtime).2.sourceSum

theorem actual_pair_energy_original_ao (runtime : LivingRuntimeState process) :
    (readMaterial runtime).energy = (1 / 2 : ℂ) *
      ∑ a : Basis, ∑ b : Basis, ∑ c : Basis, ∑ d : Basis,
        ManyBody.spinSummedTwoBody a b c d *
          ((∑ i : Basis, ∑ j : Basis, ∑ k : Basis, ∑ l : Basis,
            (Frame.normalizedSourceFrame i a * Frame.normalizedSourceFrame j c *
              Frame.normalizedSourceFrame k b * Frame.normalizedSourceFrame l d) *
                electronRepulsion i j k l) : ℝ) := by
  rw [(material_read runtime).2]
  exact (certificate_read runtime).2.originalAO

theorem actual_pair_direct_exchange (runtime : LivingRuntimeState process) :
    (readMaterial runtime).energy =
      (readMaterial runtime).direct - (readMaterial runtime).exchange := by
  rw [(material_read runtime).2]
  exact (certificate_read runtime).2.directExchange

structure PhysicalCoulombPairClosure : Prop where
  source : Coulomb.Closure
  parent : type_of% complete_parent_preserved
  density : type_of% actual_density_from_pair
  densityU : type_of% actual_density_full_U
  integrable : type_of% actual_pair_integrable
  integral : type_of% actual_pair_energy_integral
  originalAO : type_of% actual_pair_energy_original_ao
  directExchange : type_of% actual_pair_direct_exchange
  physicalOccurrence : type_of% read_commutes_with_physicalOccurrence
  wholeLedger : type_of% wholeLedger_same_occurrence
  identity : type_of% row_identity
  clock : type_of% clock_preserved
  inherited : type_of% all_original_faces
  factorization : type_of% face_factorizes
  generatedNext : type_of% generated_same_next
  originalVisit : afterFirst.current.visit = Reentry.Runtime.generatedReentryAction.target.targetVisit
  allFaces : Nonempty (Face ≃ Fin 86)

theorem sourceGeneratedPhysicalCoulombNext : PhysicalCoulombPairClosure :=
  ⟨(certificate_read afterFirst).2,complete_parent_preserved,actual_density_from_pair,
    actual_density_full_U,actual_pair_integrable,actual_pair_energy_integral,
    actual_pair_energy_original_ao,actual_pair_direct_exchange,
    read_commutes_with_physicalOccurrence,wholeLedger_same_occurrence,row_identity,
    clock_preserved,all_original_faces,face_factorizes,generated_same_next,
    rfl,⟨faceEquiv⟩⟩

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
