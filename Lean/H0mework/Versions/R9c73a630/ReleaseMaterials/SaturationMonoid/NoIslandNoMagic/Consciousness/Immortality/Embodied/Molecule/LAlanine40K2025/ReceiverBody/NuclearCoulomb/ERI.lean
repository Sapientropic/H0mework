import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearCoulomb.AttractionRate

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearCoulomb
open BasinRefinement SourceGaussianModel NuclearBasis
open MeasureTheory
noncomputable section

abbrev Quartet := Fin 4

def raiseSlot (jets : Quartet → MultiIndex) (h : Quartet) (k : Fin 3) : Quartet → MultiIndex :=
  Function.update jets h (raise (jets h) k)

def eriIntegrand (terms : Quartet → Term) (jets : Quartet → MultiIndex) (centres : Quartet → Point)
    (z : Point × Point) : ℝ :=
  (centredValue (terms 0) (jets 0) (centres 0) z.1 * centredValue (terms 1) (jets 1) (centres 1) z.1) *
    (centredValue (terms 2) (jets 2) (centres 2) z.2 * centredValue (terms 3) (jets 3) (centres 3) z.2) *
      SourceCoulomb.kernel (z.2-z.1)

def eriRate (terms : Quartet → Term) (jets : Quartet → MultiIndex) (centres speeds : Quartet → Point)
    (z : Point × Point) : ℝ :=
  -(∑ h : Quartet, ∑ k : Fin 3, speeds h k * eriIntegrand terms (raiseSlot jets h k) centres z)

theorem eri_integrand_derivative (terms : Quartet → Term) (jets : Quartet → MultiIndex)
    (centres : ℝ → Quartet → Point) (speeds : Quartet → Point) (t : ℝ) (z : Point × Point)
    (motion : ∀ h k, HasDerivAt (fun s => centres s h k) (speeds h k) t) :
    HasDerivAt (fun s => eriIntegrand terms jets (centres s) z) (eriRate terms jets (centres t) speeds z) t := by
  have each (h : Quartet) (x : Point) :=
    centred_value_derivative (terms h) (jets h) (fun s => centres s h) (speeds h) t x (motion h)
  have generated := (((each 0 z.1).mul (each 1 z.1)).mul ((each 2 z.2).mul (each 3 z.2))).mul_const
    (SourceCoulomb.kernel (z.2-z.1))
  convert! generated using 1
  simp only [eriRate,eriIntegrand,Fin.sum_univ_four,Fin.sum_univ_three,raiseSlot,Pi.mul_apply]
  simp only [Function.update_self,Function.update_of_ne (by decide : (0 : Fin 4) ≠ 1),
    Function.update_of_ne (by decide : (0 : Fin 4) ≠ 2),Function.update_of_ne (by decide : (0 : Fin 4) ≠ 3),
    Function.update_of_ne (by decide : (1 : Fin 4) ≠ 0),Function.update_of_ne (by decide : (1 : Fin 4) ≠ 2),
    Function.update_of_ne (by decide : (1 : Fin 4) ≠ 3),Function.update_of_ne (by decide : (2 : Fin 4) ≠ 0),
    Function.update_of_ne (by decide : (2 : Fin 4) ≠ 1),Function.update_of_ne (by decide : (2 : Fin 4) ≠ 3),
    Function.update_of_ne (by decide : (3 : Fin 4) ≠ 0),Function.update_of_ne (by decide : (3 : Fin 4) ≠ 1),
    Function.update_of_ne (by decide : (3 : Fin 4) ≠ 2)]
  ring

def eriEnvelope (terms : Quartet → Term) (jets : Quartet → MultiIndex) (C : ℝ) : Point × Point → ℝ :=
  coulombEnvelope (terms 0) (terms 1) (terms 2) (terms 3) (jets 0) (jets 1) (jets 2) (jets 3) C

theorem eri_envelope_integrable (terms : Quartet → Term) (positive : ∀ h, 0 < (terms h).exponent)
    (jets : Quartet → MultiIndex) (C : ℝ) : Integrable (eriEnvelope terms jets C) :=
  coulomb_envelope_integrable _ _ _ _ (positive 0) (positive 1) (positive 2) (positive 3) _ _ _ _ C

theorem eri_uniform_bound (terms : Quartet → Term) (positive : ∀ h, 0 < (terms h).exponent)
    (jets : Quartet → MultiIndex) (centres : Quartet → Point) (C : ℝ) (bounded : ∀ h, ‖centres h‖ ≤ C)
    (z : Point × Point) : ‖eriIntegrand terms jets centres z‖ ≤ eriEnvelope terms jets C z :=
  coulomb_uniform_bound _ _ _ _ (positive 0) (positive 1) (positive 2) (positive 3) _ _ _ _ C
    _ _ _ _ (bounded 0) (bounded 1) (bounded 2) (bounded 3) z

theorem eri_integrand_measurable (terms : Quartet → Term) (jets : Quartet → MultiIndex) (centres : Quartet → Point) :
    AEStronglyMeasurable (eriIntegrand terms jets centres) :=
  ((((centred_continuous (terms 0) (jets 0) (centres 0)).comp continuous_fst).mul
    ((centred_continuous (terms 1) (jets 1) (centres 1)).comp continuous_fst)).mul
    (((centred_continuous (terms 2) (jets 2) (centres 2)).comp continuous_snd).mul
      ((centred_continuous (terms 3) (jets 3) (centres 3)).comp continuous_snd))).aestronglyMeasurable.mul
        (SourceCoulomb.kernel_measurable.comp (measurable_snd.sub measurable_fst)).aestronglyMeasurable

theorem eri_integrand_integrable (terms : Quartet → Term) (positive : ∀ h, 0 < (terms h).exponent)
    (jets : Quartet → MultiIndex) (centres : Quartet → Point) : Integrable (eriIntegrand terms jets centres) :=
  (eri_envelope_integrable terms positive jets ‖centres‖).mono' (eri_integrand_measurable terms jets centres)
    (Filter.Eventually.of_forall fun z => eri_uniform_bound terms positive jets centres ‖centres‖
      (fun h => norm_le_pi_norm centres h) z)

theorem eri_rate_measurable (terms : Quartet → Term) (jets : Quartet → MultiIndex) (centres speeds : Quartet → Point) :
    AEStronglyMeasurable (eriRate terms jets centres speeds) :=
  (Finset.aestronglyMeasurable_fun_sum _ (fun h _ => Finset.aestronglyMeasurable_fun_sum _ (fun k _ =>
    (eri_integrand_measurable terms (raiseSlot jets h k) centres).const_mul (speeds h k)))).neg

def eriRateEnvelope (terms : Quartet → Term) (jets : Quartet → MultiIndex) (C : ℝ) (z : Point × Point) : ℝ :=
  C * ∑ h : Quartet, ∑ k : Fin 3, eriEnvelope terms (raiseSlot jets h k) C z

theorem eri_rate_envelope_integrable (terms : Quartet → Term) (positive : ∀ h, 0 < (terms h).exponent)
    (jets : Quartet → MultiIndex) (C : ℝ) : Integrable (eriRateEnvelope terms jets C) :=
  (integrable_finsetSum _ (fun h _ => integrable_finsetSum _ (fun k _ =>
    eri_envelope_integrable terms positive (raiseSlot jets h k) C))).const_mul C

theorem eri_rate_uniform_bound (terms : Quartet → Term) (positive : ∀ h, 0 < (terms h).exponent)
    (jets : Quartet → MultiIndex) (centres speeds : Quartet → Point) (C : ℝ)
    (bc : ∀ h, ‖centres h‖ ≤ C) (bv : ∀ h, ‖speeds h‖ ≤ C) (z : Point × Point) :
    ‖eriRate terms jets centres speeds z‖ ≤ eriRateEnvelope terms jets C z := by
  rw [eriRate,norm_neg]
  calc
    _ ≤ ∑ h : Quartet, ‖∑ k : Fin 3, speeds h k * eriIntegrand terms (raiseSlot jets h k) centres z‖ := norm_sum_le _ _
    _ ≤ ∑ h : Quartet, ∑ k : Fin 3, C * eriEnvelope terms (raiseSlot jets h k) C z := by
      apply Finset.sum_le_sum
      intro h _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul,Real.norm_eq_abs]
      have speed : |speeds h k| ≤ C := by
        simpa only [Real.norm_eq_abs] using (norm_le_pi_norm (speeds h) k).trans (bv h)
      exact mul_le_mul speed (eri_uniform_bound terms positive (raiseSlot jets h k) centres C bc z)
        (norm_nonneg _) ((norm_nonneg (speeds h)).trans (bv h))
    _ = _ := by simp only [eriRateEnvelope,Finset.mul_sum]

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearCoulomb
