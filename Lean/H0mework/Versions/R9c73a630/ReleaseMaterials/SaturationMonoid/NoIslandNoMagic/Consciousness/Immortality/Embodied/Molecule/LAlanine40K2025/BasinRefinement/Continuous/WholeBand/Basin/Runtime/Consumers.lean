import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Runtime.ParentConsumers

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceGaussianModel SourceFiniteData ContinuousGradient GlobalSource Set Filter MeasureTheory
open scoped Topology
noncomputable section

theorem actual_basin (runtime : LivingRuntimeState process) (x : Point) :
    type_of% (face_factorizes runtime (.component .material)) ∧
    (x ∈ (readMaterial runtime).calculation.basin ↔
      Tendsto ((readMaterial runtime).calculation.flow x) atTop (𝓝 (readMaterial runtime).calculation.criticalPoint)) :=
  ⟨face_factorizes runtime (.component .material),(certificate_read runtime).2.actual_basin x⟩

theorem actual_invariance (runtime : LivingRuntimeState process) (x : Point) (t : ℝ) :
    (readMaterial runtime).calculation.flow x t ∈ (readMaterial runtime).calculation.basin ↔
      x ∈ (readMaterial runtime).calculation.basin := (certificate_read runtime).2.two_sided x t

theorem actual_cover (runtime : LivingRuntimeState process) :
    (readMaterial runtime).calculation.basin = ⋃ n : ℕ, (readMaterial runtime).calculation.patches n ∧
    Monotone (readMaterial runtime).calculation.patches ∧
    IsOpen (readMaterial runtime).calculation.basin ∧ 0 < volume (readMaterial runtime).calculation.basin :=
  ⟨(certificate_read runtime).2.generated_cover,(certificate_read runtime).2.increasing,
    (certificate_read runtime).2.open_basin,(certificate_read runtime).2.positive_volume⟩

theorem actual_density_integral (runtime : LivingRuntimeState process) :
    Tendsto (fun n : ℕ => ∫ x in (readMaterial runtime).calculation.patches n,
      (readMaterial runtime).calculation.density x) atTop (𝓝 (readMaterial runtime).calculation.densityIntegral) :=
  (certificate_read runtime).2.density_limit

theorem actual_hartree_integral (runtime : LivingRuntimeState process) :
    Tendsto (fun n : ℕ => ∫ z in ((readMaterial runtime).calculation.patches n ×ˢ (readMaterial runtime).calculation.patches n),
      (readMaterial runtime).calculation.density z.1 * (readMaterial runtime).calculation.density z.2 *
        SourceCoulomb.kernel (z.2-z.1)) atTop (𝓝 (readMaterial runtime).calculation.hartreeIntegral) :=
  (certificate_read runtime).2.hartree_limit

structure PhysicalBasinClosure : Prop where
  source : BasinClosure
  parent : type_of% complete_parent_preserved
  actual_basin : type_of% actual_basin
  actual_invariance : type_of% actual_invariance
  actual_cover : type_of% actual_cover
  actual_density_integral : type_of% actual_density_integral
  actual_hartree_integral : type_of% actual_hartree_integral
  physicalOccurrence : type_of% read_commutes_with_physicalOccurrence
  wholeLedger : type_of% wholeLedger_same_occurrence
  identity : type_of% row_identity
  clock : type_of% clock_preserved
  inherited : type_of% all_original_faces
  factorization : type_of% face_factorizes
  generatedNext : type_of% generated_same_next
  originalVisit : afterFirst.current.visit = Reentry.Runtime.generatedReentryAction.target.targetVisit

theorem sourceGeneratedPhysicalBasinNext : PhysicalBasinClosure :=
  ⟨(certificate_read afterFirst).2,complete_parent_preserved,actual_basin,actual_invariance,actual_cover,
    actual_density_integral,actual_hartree_integral,read_commutes_with_physicalOccurrence,wholeLedger_same_occurrence,
    row_identity,clock_preserved,all_original_faces,face_factorizes,generated_same_next,rfl⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
