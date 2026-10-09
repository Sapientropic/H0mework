import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Runtime.ParentConsumers

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor
open BasinRefinement SourceFiniteData SourceGaussianModel SourceCoulomb MeasureTheory
open SaturationMonoid.PhysicsCore ProofFreeRicherAnholonomicSource UnifiedAction YangMills.FullPairing
open scoped Matrix ComplexOrder
noncomputable section

theorem actual_direct_integral (runtime : LivingRuntimeState process) :
    (readMaterial runtime).direct =
      ∫ z : Point × Point, (readMaterial runtime).directIntegrand z := by
  rw [(material_read runtime).2]
  exact (certificate_read runtime).2.directIntegral

theorem actual_exchange_integral (runtime : LivingRuntimeState process) :
    (readMaterial runtime).exchange =
      ∫ z : Point × Point, (readMaterial runtime).exchangeIntegrand z := by
  rw [(material_read runtime).2]
  exact (certificate_read runtime).2.exchangeIntegral

theorem actual_direct_density_kernel (runtime : LivingRuntimeState process)
    (z : Point × Point) :
    (readMaterial runtime).directIntegrand z =
      (2 * ‖Coulomb.occupiedVector z.1‖^2 *
        ‖Coulomb.occupiedVector z.2‖^2 * SourceCoulomb.kernel (z.2-z.1) : ℝ) := by
  rw [(material_read runtime).2]
  exact (certificate_read runtime).2.directCast z

theorem actual_exchange_density_kernel (runtime : LivingRuntimeState process)
    (z : Point × Point) :
    (readMaterial runtime).exchangeIntegrand z =
      (‖inner ℂ (Coulomb.occupiedVector z.2) (Coulomb.occupiedVector z.1)‖^2 *
        SourceCoulomb.kernel (z.2-z.1) : ℝ) := by
  rw [(material_read runtime).2]
  exact (certificate_read runtime).2.exchangeCast z

theorem actual_energy_positive_bound (runtime : LivingRuntimeState process) :
    (readMaterial runtime).direct.im = 0 ∧
    (readMaterial runtime).exchange.im = 0 ∧
    0 ≤ (readMaterial runtime).exchange.re ∧
    2 * (readMaterial runtime).exchange.re ≤ (readMaterial runtime).direct.re := by
  rw [(material_read runtime).2]
  exact ⟨(certificate_read runtime).2.directPositive.1,
    (certificate_read runtime).2.exchangePositive.1,
    (certificate_read runtime).2.exchangePositive.2,
    (certificate_read runtime).2.exchangeBound⟩

theorem actual_pair_energy_split (runtime : LivingRuntimeState process) :
    (readMaterial runtime).parent.parent.energy =
      (readMaterial runtime).direct - (readMaterial runtime).exchange := by
  rw [(material_read runtime).2]
  exact (certificate_read runtime).2.energy

theorem actual_pair_energy_original_ao (runtime : LivingRuntimeState process) :
    (readMaterial runtime).parent.parent.energy = Coulomb.sourceRepulsionSum := by
  rw [(material_read runtime).2]
  exact Coulomb.material_energy_source

structure PhysicalHartreeExchangeClosure : Prop where
  source : Hartree.Closure
  parent : type_of% complete_parent_preserved
  directIntegral : type_of% actual_direct_integral
  exchangeIntegral : type_of% actual_exchange_integral
  directDensity : type_of% actual_direct_density_kernel
  exchangeDensity : type_of% actual_exchange_density_kernel
  energyBound : type_of% actual_energy_positive_bound
  pairSplit : type_of% actual_pair_energy_split
  originalAO : type_of% actual_pair_energy_original_ao
  physicalOccurrence : type_of% read_commutes_with_physicalOccurrence
  wholeLedger : type_of% wholeLedger_same_occurrence
  identity : type_of% row_identity
  clock : type_of% clock_preserved
  inherited : type_of% all_original_faces
  factorization : type_of% face_factorizes
  generatedNext : type_of% generated_same_next
  originalVisit : afterFirst.current.visit = Reentry.Runtime.generatedReentryAction.target.targetVisit
  allFaces : Nonempty (Face ≃ Fin 90)

theorem sourceGeneratedPhysicalHartreeExchangeNext : PhysicalHartreeExchangeClosure :=
  ⟨(certificate_read afterFirst).2,complete_parent_preserved,
    actual_direct_integral,actual_exchange_integral,actual_direct_density_kernel,
    actual_exchange_density_kernel,actual_energy_positive_bound,actual_pair_energy_split,
    actual_pair_energy_original_ao,read_commutes_with_physicalOccurrence,
    wholeLedger_same_occurrence,row_identity,clock_preserved,all_original_faces,
    face_factorizes,generated_same_next,rfl,⟨faceEquiv⟩⟩

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
