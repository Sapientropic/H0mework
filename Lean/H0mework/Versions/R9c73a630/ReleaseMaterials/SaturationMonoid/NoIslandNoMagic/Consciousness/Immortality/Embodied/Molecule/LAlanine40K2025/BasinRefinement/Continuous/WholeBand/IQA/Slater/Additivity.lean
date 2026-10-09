import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.IQA.Slater.Regions

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandIQA.Slater
open SourceGaussianModel GlobalSource WholeBandBasin SourceCoulomb Set MeasureTheory Filter
open scoped Topology
open LAlanine40K2025.UnifiedOrbitals
open LAlanine40K2025.UnifiedOrbitals.Frame
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb
noncomputable section

theorem four_region_integral (f : Point × Point → ℝ) (integrable : Integrable f) :
    (∫ z in intraRegion, f z)+
      (∫ z in firstCrossRegion, f z)+
      (∫ z in secondCrossRegion, f z)+
      (∫ z in exteriorRegion, f z) = ∫ z, f z := by
  have first := integral_add_compl inside_first_measurable integrable
  have inside := integral_add_compl
    (μ := volume.restrict insideFirst) inside_second_measurable
    integrable.integrableOn
  have outside := integral_add_compl
    (μ := volume.restrict insideFirstᶜ) inside_second_measurable
    integrable.integrableOn
  rw [Measure.restrict_restrict inside_second_measurable,
    Measure.restrict_restrict inside_second_measurable.compl] at inside outside
  rw [Set.inter_comm insideSecondᶜ insideFirst] at inside
  rw [Set.inter_comm insideSecond insideFirst] at inside
  rw [Set.inter_comm insideSecond insideFirstᶜ,
    Set.inter_comm insideSecondᶜ insideFirstᶜ] at outside
  rw [← intra_region_eq,← first_cross_region_eq] at inside
  rw [← second_cross_region_eq,← exterior_region_eq] at outside
  linarith only [first,inside,outside]

theorem full_pair_energy_four_regions :
    intraEnergy+firstCrossEnergy+secondCrossEnergy+exteriorEnergy =
      pairCoulombEnergy.re := by
  have h := four_region_integral realPairIntegrand real_pair_integrable
  have source : pairCoulombEnergy.re =
      (1/2 : ℝ) * ∫ z : Point × Point, realPairIntegrand z := by
    rw [pairCoulombEnergy]
    simp_rw [pair_integrand_real]
    rw [integral_complex_ofReal]
    norm_num
  rw [source]
  simp only [intraEnergy,firstCrossEnergy,secondCrossEnergy,exteriorEnergy]
  linarith only [h]

theorem four_region_nonnegative :
    0 ≤ intraEnergy ∧ 0 ≤ firstCrossEnergy ∧
      0 ≤ secondCrossEnergy ∧ 0 ≤ exteriorEnergy := by
  have measurable := regions_measurable
  have nonnegative (s : Set (Point × Point)) (hs : MeasurableSet s) :
      0 ≤ (1/2 : ℝ) * ∫ z in s, realPairIntegrand z :=
    mul_nonneg (by norm_num)
      (setIntegral_nonneg hs (fun z _ => real_pair_integrand_nonnegative z))
  exact ⟨nonnegative _ measurable.1,
    nonnegative _ measurable.2.1,
    nonnegative _ measurable.2.2.1,
    nonnegative _ measurable.2.2.2⟩

private theorem coulomb_kernel_even (x : Point) : kernel (-x)=kernel x := by
  simp only [kernel,distance,Pi.neg_apply,neg_sq]

theorem real_pair_integrand_swap (z : Point × Point) :
    realPairIntegrand (z.2,z.1)=realPairIntegrand z := by
  have innerNorm :
      ‖inner ℂ (occupiedVector z.1) (occupiedVector z.2)‖ =
        ‖inner ℂ (occupiedVector z.2) (occupiedVector z.1)‖ := by
    have hxy : inner ℂ (occupiedVector z.1) (occupiedVector z.2) =
        star (inner ℂ (occupiedVector z.2) (occupiedVector z.1)) :=
      (inner_conj_symm _ _).symm
    rw [hxy,norm_star]
  have kernelSymm : kernel (z.1-z.2)=kernel (z.2-z.1) := by
    have h : z.1-z.2=-(z.2-z.1) := by abel
    rw [h,coulomb_kernel_even]
  simp only [realPairIntegrand,realPairDensity]
  rw [innerNorm,kernelSymm]
  ring

theorem cross_region_energy_symmetry : firstCrossEnergy=secondCrossEnergy := by
  have h := setIntegral_prod_swap (μ := volume) (ν := volume)
    basin basinᶜ realPairIntegrand
  rw [← Measure.volume_eq_prod] at h
  have hpoint (z : Point × Point) : realPairIntegrand z.swap=realPairIntegrand z :=
    real_pair_integrand_swap z
  simp_rw [hpoint] at h
  dsimp [firstCrossEnergy,secondCrossEnergy,firstCrossRegion,secondCrossRegion]
  rw [h]

theorem full_pair_energy_three_regions :
    intraEnergy+2*firstCrossEnergy+exteriorEnergy=pairCoulombEnergy.re := by
  have h := full_pair_energy_four_regions
  rw [← cross_region_energy_symmetry] at h
  linarith only [h]

theorem intra_energy_patch_limit :
    Tendsto (fun n : ℕ => (1/2 : ℝ) * ∫ z in pairPatch n,
      realPairIntegrand z) atTop (𝓝 intraEnergy) := by
  have h : Tendsto (fun n : ℕ => ∫ z in pairPatch n,
      realPairIntegrand z) atTop
      (𝓝 (∫ z in intraRegion, realPairIntegrand z)) := by
    rw [intraRegion,basin_pair_union]
    exact tendsto_setIntegral_of_monotone
      (fun n => (entryPatch_open n).measurableSet.prod
        (entryPatch_open n).measurableSet)
      pairPatch_monotone real_pair_integrable.integrableOn
  simpa only [intraEnergy] using h.const_mul (1/2 : ℝ)

theorem original_ao_energy_four_regions :
    ((intraEnergy+firstCrossEnergy+secondCrossEnergy+exteriorEnergy : ℝ) : ℂ) =
      (1 / 2 : ℂ) *
      ∑ a : SourceFiniteData.Basis, ∑ b : SourceFiniteData.Basis,
        ∑ c : SourceFiniteData.Basis, ∑ d : SourceFiniteData.Basis,
          spinSummedTwoBody a b c d *
            ((∑ i : SourceFiniteData.Basis, ∑ j : SourceFiniteData.Basis,
              ∑ k : SourceFiniteData.Basis, ∑ l : SourceFiniteData.Basis,
                (normalizedSourceFrame i a * normalizedSourceFrame j c *
                  normalizedSourceFrame k b * normalizedSourceFrame l d) *
                    electronRepulsion i j k l) : ℝ) := by
  have real : (pairCoulombEnergy.re : ℂ)=pairCoulombEnergy := by
    apply Complex.ext
    · simp
    · simp [pair_energy_real_nonnegative.1]
  calc
    _ = (pairCoulombEnergy.re : ℂ) := by
      rw [full_pair_energy_four_regions]
    _ = pairCoulombEnergy := real
    _ = _ := pair_coulomb_energy_original_ao

end
end LAlanine40K2025.BasinRefinement.WholeBandIQA.Slater
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
