import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.IQA.Slater.Runtime.ParentConsumers

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandIQA.Slater.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.UnifiedOrbitals
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetFull
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb
open SourceGaussianModel GlobalSource WholeBandBasin Set MeasureTheory Filter
open scoped Topology
noncomputable section

theorem actual_basin_source (runtime : LivingRuntimeState process) :
    (readMaterial runtime).basin.basin = WholeBandBasin.basin := by
  rw [(material_read runtime).2]
  exact Slater.basin_same_source

theorem actual_full_parent_J (runtime : LivingRuntimeState process)
    (i j : SourceFiniteData.Basis) :
    SourceJoin.material.targetJ i j =
      (readMaterial runtime).parent.combinedTargetJ i j := by
  rw [(material_read runtime).2]
  exact Outer.target_J_all i j

theorem actual_pair_energy_three_regions (runtime : LivingRuntimeState process) :
    (readMaterial runtime).intra+2*(readMaterial runtime).cross+
      (readMaterial runtime).exterior = pairCoulombEnergy.re := by
  rw [(material_read runtime).2]
  exact Slater.material_pair_energy

theorem actual_source_repulsion (runtime : LivingRuntimeState process) :
    (((readMaterial runtime).intra+2*(readMaterial runtime).cross+
      (readMaterial runtime).exterior : ℝ) : ℂ) = sourceRepulsionSum := by
  rw [(material_read runtime).2]
  have real : (pairCoulombEnergy.re : ℂ)=pairCoulombEnergy := by
    apply Complex.ext
    · simp
    · simp [pair_energy_real_nonnegative.1]
  calc
    _ = (pairCoulombEnergy.re : ℂ) := by
      rw [Slater.material_pair_energy]
    _ = pairCoulombEnergy := real
    _ = sourceRepulsionSum := pair_coulomb_energy_source

theorem actual_regional_nonnegative (runtime : LivingRuntimeState process) :
    0 ≤ (readMaterial runtime).intra ∧
    0 ≤ (readMaterial runtime).cross ∧
    0 ≤ (readMaterial runtime).exterior := by
  rw [(material_read runtime).2]
  have h := Slater.four_region_nonnegative
  exact ⟨h.1,h.2.1,h.2.2.2⟩

theorem actual_intra_patch_limit (runtime : LivingRuntimeState process) :
    Tendsto (fun n : ℕ => (1/2 : ℝ) * ∫ z in pairPatch n,
      realPairIntegrand z) atTop (𝓝 (readMaterial runtime).intra) := by
  rw [(material_read runtime).2]
  exact Slater.intra_energy_patch_limit

structure PhysicalSlaterIQAClosure : Prop where
  source : Slater.Closure
  parent : type_of% complete_parent_preserved
  siblingBasin : type_of% sibling_basin_zero_flux
  siblingOccurrence : type_of% sibling_basin_same_occurrence
  basin : type_of% actual_basin_source
  fullJ : type_of% actual_full_parent_J
  regionalEnergy : type_of% actual_pair_energy_three_regions
  originalRepulsion : type_of% actual_source_repulsion
  positivity : type_of% actual_regional_nonnegative
  patchLimit : type_of% actual_intra_patch_limit
  physicalOccurrence : type_of% read_commutes_with_physicalOccurrence
  wholeLedger : type_of% wholeLedger_same_occurrence
  identity : type_of% row_identity
  clock : type_of% clock_preserved
  inherited : type_of% all_original_faces
  factorization : type_of% face_factorizes
  generatedNext : type_of% generated_same_next
  originalVisit : afterFirst.current.visit = Reentry.Runtime.generatedReentryAction.target.targetVisit
  allFaces : Nonempty (Face ≃ Fin 140)

theorem sourceGeneratedPhysicalSlaterIQANext : PhysicalSlaterIQAClosure :=
  ⟨(certificate_read afterFirst).2,complete_parent_preserved,
    sibling_basin_zero_flux,sibling_basin_same_occurrence,
    actual_basin_source,actual_full_parent_J,
    actual_pair_energy_three_regions,actual_source_repulsion,
    actual_regional_nonnegative,actual_intra_patch_limit,
    read_commutes_with_physicalOccurrence,wholeLedger_same_occurrence,
    row_identity,clock_preserved,all_original_faces,face_factorizes,
    generated_same_next,rfl,⟨faceEquiv⟩⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandIQA.Slater.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
