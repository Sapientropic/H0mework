import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Kernel

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb
open LAlanine40K2025.UnifiedOrbitals.Frame
open BasinRefinement SourceFiniteData SourceGaussianModel SourceCoulomb MeasureTheory
open scoped Matrix InnerProductSpace
noncomputable section

def realPairDensity (z : Point × Point) : ℝ :=
  4 * ‖occupiedVector z.1‖^2 * ‖occupiedVector z.2‖^2 -
    2 * ‖inner ℂ (occupiedVector z.2) (occupiedVector z.1)‖^2

theorem pair_density_real (z : Point × Point) :
    pairDensity z = (realPairDensity z : ℂ) := by
  rw [pair_density_kernel,kernel_inner,kernel_inner,kernel_inner,kernel_inner]
  let v := occupiedVector z.1
  let w := occupiedVector z.2
  have hv : inner ℂ v v = (‖v‖ : ℂ)^2 := inner_self_eq_norm_sq_to_K v
  have hw : inner ℂ w w = (‖w‖ : ℂ)^2 := inner_self_eq_norm_sq_to_K w
  have hxy : inner ℂ v w = star (inner ℂ w v) := (inner_conj_symm v w).symm
  rw [hv,hw,hxy]
  change 4 * (‖v‖ : ℂ)^2 * (‖w‖ : ℂ)^2 -
    2 * inner ℂ w v * star (inner ℂ w v) =
      ((4 * ‖v‖^2 * ‖w‖^2 - 2 * ‖inner ℂ w v‖^2 : ℝ) : ℂ)
  have hs : inner ℂ w v * star (inner ℂ w v) =
      (‖inner ℂ w v‖^2 : ℂ) := by simpa using Complex.mul_conj' (inner ℂ w v)
  calc
    4 * (‖v‖ : ℂ)^2 * (‖w‖ : ℂ)^2 -
        2 * inner ℂ w v * star (inner ℂ w v) =
      4 * (‖v‖ : ℂ)^2 * (‖w‖ : ℂ)^2 -
        2 * (inner ℂ w v * star (inner ℂ w v)) := by ring
    _ = _ := by rw [hs]; push_cast; ring

theorem real_pair_density_nonnegative (z : Point × Point) :
    0 ≤ realPairDensity z := by
  let v := occupiedVector z.1
  let w := occupiedVector z.2
  have cauchy : ‖inner ℂ w v‖ ≤ ‖w‖ * ‖v‖ := norm_inner_le_norm w v
  have cauchySq : ‖inner ℂ w v‖^2 ≤ (‖w‖ * ‖v‖)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) cauchy 2
  have vnonnegative : 0 ≤ ‖v‖^2 := sq_nonneg _
  have wnonnegative : 0 ≤ ‖w‖^2 := sq_nonneg _
  dsimp [realPairDensity]
  nlinarith

def realPairIntegrand (z : Point × Point) : ℝ :=
  realPairDensity z * kernel (z.2-z.1)

theorem pair_integrand_real (z : Point × Point) :
    pairCoulombIntegrand z = (realPairIntegrand z : ℂ) := by
  simp only [pairCoulombIntegrand,realPairIntegrand,pair_density_real]
  norm_cast

theorem real_pair_integrand_nonnegative (z : Point × Point) :
    0 ≤ realPairIntegrand z :=
  mul_nonneg (real_pair_density_nonnegative z) (kernel_nonnegative _)

theorem real_pair_integrable : Integrable realPairIntegrand := by
  have h := pair_integrable.re
  simpa [pair_integrand_real] using h

theorem pair_energy_real_nonnegative :
    pairCoulombEnergy.im = 0 ∧ 0 ≤ pairCoulombEnergy.re := by
  have integralNonnegative : 0 ≤ ∫ z : Point × Point, realPairIntegrand z :=
    integral_nonneg real_pair_integrand_nonnegative
  have energy : pairCoulombEnergy =
      (((1 / 2 : ℝ) * ∫ z : Point × Point, realPairIntegrand z) : ℂ) := by
    rw [pairCoulombEnergy]
    simp_rw [pair_integrand_real]
    rw [integral_complex_ofReal]
    push_cast
    ring
  rw [energy]
  constructor
  · simp
  · simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
      integralNonnegative

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
