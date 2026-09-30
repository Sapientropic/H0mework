import H0mework.Chemistry.LAlanineEntropy.FiniteThermalEntropy

/-!
# Joint PMFs generate their entropy comparison with their own marginals

The product reference is formed with PMF bind/map. Its support contains the
actual joint support, including zero marginals. Finite KL is therefore
available without a full-support premise.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Quantum

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal BigOperators
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Population

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

noncomputable section

def productPMF (p : PMF ι) (q : PMF κ) : PMF (ι × κ) :=
  p.bind fun i => q.map (Prod.mk i)

@[simp] theorem productPMF_apply (p : PMF ι) (q : PMF κ) (i : ι) (j : κ) :
    productPMF p q (i, j) = p i * q j := by
  classical
  simp [productPMF, PMF.bind_apply, PMF.map_apply, Prod.mk.injEq, tsum_fintype, ite_and]

def fstMarginal (p : PMF (ι × κ)) : PMF ι := p.map Prod.fst

def sndMarginal (p : PMF (ι × κ)) : PMF κ := p.map Prod.snd

omit [Fintype ι] [Fintype κ] in
theorem joint_marginals_nonzero (p : PMF (ι × κ)) (x : ι × κ) (present : p x ≠ 0) :
    fstMarginal p x.1 ≠ 0 ∧ sndMarginal p x.2 ≠ 0 := by
  constructor
  · exact (PMF.mem_support_map_iff Prod.fst p x.1).mpr ⟨x, present, rfl⟩
  · exact (PMF.mem_support_map_iff Prod.snd p x.2).mpr ⟨x, present, rfl⟩

private theorem weighted_log_mul (x y : ℝ) :
    x * y * Real.log (x * y) = (x * Real.log x) * y + x * (y * Real.log y) := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  rw [Real.log_mul hx hy]
  ring

theorem entropy_product (p : PMF ι) (q : PMF κ) :
    entropy (productPMF p q) = entropy p + entropy q := by
  unfold entropy
  rw [Fintype.sum_prod_type]
  simp_rw [productPMF_apply, ENNReal.toReal_mul, weighted_log_mul,
    Finset.sum_add_distrib, ← Finset.mul_sum, pmf_sum_toReal, mul_one]
  rw [← Finset.sum_mul, pmf_sum_toReal, one_mul]
  ring

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [MeasurableSpace κ] [MeasurableSingletonClass κ]

theorem sum_map_read (p : PMF ι) (f : ι → κ) (read : κ → ℝ) :
    ∑ j, (p.map f j).toReal * read j = ∑ i, (p i).toReal * read (f i) := by
  have measurable : Measurable f := measurable_of_countable f
  have transported := MeasureTheory.integral_map
    (μ := p.toMeasure) measurable.aemeasurable
    (show AEStronglyMeasurable read (p.toMeasure.map f) from .of_discrete)
  rw [PMF.toMeasure_map f p measurable] at transported
  simpa only [PMF.integral_eq_sum, smul_eq_mul] using transported

omit [MeasurableSingletonClass ι] [MeasurableSingletonClass κ] in
theorem joint_product_absolutelyContinuous (p : PMF (ι × κ)) :
    p.toMeasure ≪ (productPMF (fstMarginal p) (sndMarginal p)).toMeasure := by
  have supports : p.support ⊆ (productPMF (fstMarginal p) (sndMarginal p)).support := by
    intro x present
    obtain ⟨first, second⟩ := joint_marginals_nonzero p x present
    change productPMF (fstMarginal p) (sndMarginal p) x ≠ 0
    obtain ⟨i, j⟩ := x
    rw [productPMF_apply]
    exact mul_ne_zero first second
  apply Measure.AbsolutelyContinuous.mk
  intro s measurable null
  apply (p.toMeasure_apply_eq_zero_iff measurable).mpr
  exact ((productPMF (fstMarginal p) (sndMarginal p)).toMeasure_apply_eq_zero_iff
    measurable).mp null |>.mono_left supports

theorem joint_product_KL_finite (p : PMF (ι × κ)) :
    klDiv p.toMeasure (productPMF (fstMarginal p) (sndMarginal p)).toMeasure ≠ ∞ :=
  finiteKL_of_ac p _ (joint_product_absolutelyContinuous p)

/-- Joint KL is exactly the entropy excess of its two actual marginals. -/
theorem jointKL_entropy_commutes (p : PMF (ι × κ)) :
    realKL p (productPMF (fstMarginal p) (sndMarginal p)) =
      entropy (fstMarginal p) + entropy (sndMarginal p) - entropy p := by
  rw [realKL_eq_sum_of_ac p _ (joint_product_absolutelyContinuous p)]
  calc
    _ = (∑ x, (p x).toReal * Real.log (p x).toReal) -
        (∑ x, (p x).toReal * Real.log (fstMarginal p x.1).toReal) -
        (∑ x, (p x).toReal * Real.log (sndMarginal p x.2).toReal) := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro x _membership
      by_cases zero : p x = 0
      · simp [zero]
      · obtain ⟨first, second⟩ := joint_marginals_nonzero p x zero
        have pReal := (ENNReal.toReal_pos zero (p.apply_ne_top x)).ne'
        have firstReal := (ENNReal.toReal_pos first ((fstMarginal p).apply_ne_top x.1)).ne'
        have secondReal := (ENNReal.toReal_pos second ((sndMarginal p).apply_ne_top x.2)).ne'
        obtain ⟨i, j⟩ := x
        rw [productPMF_apply, ENNReal.toReal_mul,
          Real.log_div pReal (mul_ne_zero firstReal secondReal), Real.log_mul firstReal secondReal]
        ring
    _ = _ := by
      rw [← sum_map_read p Prod.fst (fun i => Real.log (fstMarginal p i).toReal),
        ← sum_map_read p Prod.snd (fun j => Real.log (sndMarginal p j).toReal)]
      simp only [entropy, fstMarginal, sndMarginal]
      ring

theorem classical_entropy_subadditive (p : PMF (ι × κ)) :
    entropy p ≤ entropy (fstMarginal p) + entropy (sndMarginal p) := by
  have nonnegative := kl_sum_nonneg_of_ac p _ (joint_product_absolutelyContinuous p)
  rw [← realKL_eq_sum_of_ac p _ (joint_product_absolutelyContinuous p),
    jointKL_entropy_commutes] at nonnegative
  exact sub_nonneg.mp nonnegative

end

end LAlanine40K2025.Thermal.Quantum
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
