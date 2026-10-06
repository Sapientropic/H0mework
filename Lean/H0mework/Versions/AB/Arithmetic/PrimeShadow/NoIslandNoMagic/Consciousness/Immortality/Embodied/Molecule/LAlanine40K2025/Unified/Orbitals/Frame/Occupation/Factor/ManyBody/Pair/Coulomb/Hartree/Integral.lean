import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Kernel

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb
open LAlanine40K2025.UnifiedOrbitals.Frame
open BasinRefinement SourceFiniteData SourceGaussianModel SourceCoulomb MeasureTheory
open scoped Matrix BigOperators
noncomputable section

private theorem quartet_integrable (i k j l : Basis) :
    Integrable (fun z : Point × Point => (quartet i k j l z : ℂ)) := by
  exact (normalized_quartet_integrable i k j l).ofReal

private theorem source_sum_integrable (coeff : Basis → Basis → Basis → Basis → ℂ) :
    Integrable (fun z : Point × Point =>
      ∑ i : Basis, ∑ j : Basis, ∑ k : Basis, ∑ l : Basis,
        coeff i j k l * (quartet i k j l z : ℂ)) :=
  integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    integrable_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ =>
      (quartet_integrable i k j l).const_mul _))))

theorem hartree_integrable : Integrable hartreeIntegrand :=
  source_sum_integrable _

theorem exchange_integrable : Integrable exchangeIntegrand :=
  source_sum_integrable _

private theorem source_sum_integral (coeff : Basis → Basis → Basis → Basis → ℂ) :
    (∫ z : Point × Point,
      ∑ i : Basis, ∑ j : Basis, ∑ k : Basis, ∑ l : Basis,
        coeff i j k l * (quartet i k j l z : ℂ)) =
      ∑ i : Basis, ∑ j : Basis, ∑ k : Basis, ∑ l : Basis,
        coeff i j k l * (normalizedRepulsion i k j l : ℂ) := by
  have each (i j k l : Basis) : Integrable (fun z : Point × Point =>
      coeff i j k l * (quartet i k j l z : ℂ)) :=
    (quartet_integrable i k j l).const_mul _
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    integrable_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ => each i j k l))))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ =>
    integrable_finsetSum _ (fun l _ => each i j k l)))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ => each i j k l))]
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_finsetSum _ (fun l _ => each i j k l)]
  apply Finset.sum_congr rfl
  intro l _
  simp only [integral_const_mul,integral_complex_ofReal,normalizedRepulsion,quartet]

theorem hartree_integral_source :
    (∫ z : Point × Point, hartreeIntegrand z) = directEnergy := by
  simp only [hartreeIntegrand]
  rw [source_sum_integral]
  unfold directEnergy
  simp_rw [show ∀ i j k l : Basis,
      (2 : ℂ) * projector24 i k * projector24 j l *
        (normalizedRepulsion i k j l : ℂ) =
        2 * (projector24 i k * projector24 j l *
          (normalizedRepulsion i k j l : ℝ)) from fun _ _ _ _ => by ring]
  simp only [Finset.mul_sum]

theorem exchange_integral_source :
    (∫ z : Point × Point, exchangeIntegrand z) = exchangeEnergy := by
  simp only [exchangeIntegrand]
  rw [source_sum_integral]
  rfl

theorem pair_energy_hartree_exchange :
    pairCoulombEnergy = (∫ z : Point × Point, hartreeIntegrand z) -
      (∫ z : Point × Point, exchangeIntegrand z) := by
  rw [hartree_integral_source,exchange_integral_source]
  exact pair_coulomb_direct_exchange

theorem real_hartree_integrable : Integrable realHartreeIntegrand := by
  have h := hartree_integrable.re
  simpa [hartree_integrand_real] using h

theorem real_exchange_integrable : Integrable realExchangeIntegrand := by
  have h := exchange_integrable.re
  simpa [exchange_integrand_real] using h

theorem direct_energy_real_integral :
    directEnergy = ((∫ z : Point × Point, realHartreeIntegrand z) : ℂ) := by
  rw [← hartree_integral_source]
  simp_rw [hartree_integrand_real]

theorem exchange_energy_real_integral :
    exchangeEnergy = ((∫ z : Point × Point, realExchangeIntegrand z) : ℂ) := by
  rw [← exchange_integral_source]
  simp_rw [exchange_integrand_real]

theorem direct_energy_real_nonnegative :
    directEnergy.im = 0 ∧ 0 ≤ directEnergy.re := by
  constructor
  · simp only [direct_energy_real_integral,integral_complex_ofReal,Complex.ofReal_im]
  · simpa only [direct_energy_real_integral,integral_complex_ofReal,Complex.ofReal_re]
      using integral_nonneg hartree_integrand_nonnegative

theorem exchange_energy_real_nonnegative :
    exchangeEnergy.im = 0 ∧ 0 ≤ exchangeEnergy.re := by
  constructor
  · simp only [exchange_energy_real_integral,integral_complex_ofReal,Complex.ofReal_im]
  · simpa only [exchange_energy_real_integral,integral_complex_ofReal,Complex.ofReal_re]
      using integral_nonneg exchange_integrand_nonnegative

theorem exchange_energy_bounded : 2 * exchangeEnergy.re ≤ directEnergy.re := by
  have hmono :
      (∫ z : Point × Point, 2 * realExchangeIntegrand z) ≤
        (∫ z : Point × Point, realHartreeIntegrand z) :=
    integral_mono (real_exchange_integrable.const_mul 2) real_hartree_integrable
      exchange_integrand_bounded
  rw [integral_const_mul] at hmono
  rw [direct_energy_real_integral,exchange_energy_real_integral]
  simpa only [integral_complex_ofReal,Complex.ofReal_re] using hmono

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
