import H0mework.Chemistry.LAlanineEntropy.FiniteGibbsPopulation
import H0mework.Chemistry.LAlanineEntropy.FiniteThermalDataProcessing

/-!
# Finite KL differences commute with the thermal entropy ledger

Gibbs weights have full support, so every admitted population has finite KL.
The real-valued difference is expanded only after finiteness is established;
zero population coordinates retain their zero contribution.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Population

open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal BigOperators

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

noncomputable section

omit [Fintype ι] in
theorem pmf_absolutelyContinuous (p π : PMF ι) (fullSupport : ∀ i, π i ≠ 0) :
    p.toMeasure ≪ π.toMeasure := by
  apply Measure.AbsolutelyContinuous.mk
  intro s _measurable null
  have empty : s = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have singletonNull := measure_mono_null (Set.singleton_subset_iff.mpr hi) null
    exact fullSupport i (by
      simpa only [PMF.toMeasure_apply_singleton, measurableSet_singleton] using singletonNull)
  simp [empty]

theorem finiteKL_of_ac (p π : PMF ι) (ac : p.toMeasure ≪ π.toMeasure) :
    klDiv p.toMeasure π.toMeasure ≠ ∞ :=
  InformationTheory.klDiv_ne_top ac .of_finite

theorem finiteKL (p π : PMF ι) (fullSupport : ∀ i, π i ≠ 0) :
    klDiv p.toMeasure π.toMeasure ≠ ∞ :=
  finiteKL_of_ac p π (pmf_absolutelyContinuous p π fullSupport)

omit [Fintype ι] in
theorem rnDeriv_pmf_of_ac (p π : PMF ι) (ac : p.toMeasure ≪ π.toMeasure)
    (i : ι) (nonzero : π i ≠ 0) :
    p.toMeasure.rnDeriv π.toMeasure i = p i / π i := by
  have singletonIntegral := Measure.setLIntegral_rnDeriv ac ({i} : Set ι)
  simp only [lintegral_singleton, PMF.toMeasure_apply_singleton, measurableSet_singleton]
    at singletonIntegral
  apply (ENNReal.eq_div_iff nonzero (π.apply_ne_top i)).mpr
  simpa only [mul_comm] using singletonIntegral

def realKL (p π : PMF ι) : ℝ := (klDiv p.toMeasure π.toMeasure).toReal

theorem realKL_eq_sum_of_ac (p π : PMF ι) (ac : p.toMeasure ≪ π.toMeasure) :
    realKL p π = ∑ i, (p i).toReal * Real.log ((p i).toReal / (π i).toReal) := by
  rw [realKL, InformationTheory.toReal_klDiv_of_measure_eq ac (by simp), PMF.integral_eq_sum]
  apply Finset.sum_congr rfl
  intro i _membership
  by_cases zero : p i = 0
  · simp [zero]
  · have nonzero : π i ≠ 0 := by
      intro vanished
      apply zero
      have null : π.toMeasure ({i} : Set ι) = 0 := by
        simpa only [PMF.toMeasure_apply_singleton, measurableSet_singleton] using vanished
      simpa only [PMF.toMeasure_apply_singleton, measurableSet_singleton] using ac null
    rw [smul_eq_mul, llr, rnDeriv_pmf_of_ac p π ac i nonzero, ENNReal.toReal_div]

theorem realKL_eq_sum (p π : PMF ι) (fullSupport : ∀ i, π i ≠ 0) :
    realKL p π = ∑ i, (p i).toReal * Real.log ((p i).toReal / (π i).toReal) :=
  realKL_eq_sum_of_ac p π (pmf_absolutelyContinuous p π fullSupport)

theorem kl_sum_nonneg_of_ac (p π : PMF ι) (ac : p.toMeasure ≪ π.toMeasure) :
    0 ≤ ∑ i, (p i).toReal * Real.log ((p i).toReal / (π i).toReal) := by
  rw [← realKL_eq_sum_of_ac p π ac]
  exact ENNReal.toReal_nonneg

variable [Nonempty ι]

theorem gibbs_kl_finite (energy : ι → ℝ) (beta : ℝ) (p : PMF ι) :
    klDiv p.toMeasure (gibbsPMF energy beta).toMeasure ≠ ∞ :=
  finiteKL p (gibbsPMF energy beta) (fun i => (gibbsPMF_positive energy beta i).ne')

theorem realKL_gibbs (energy : ι → ℝ) (beta : ℝ) (p : PMF ι) :
    realKL p (gibbsPMF energy beta) =
      -entropy p + beta * meanEnergy energy p + Real.log (partitionFunction energy beta) := by
  rw [realKL_eq_sum p (gibbsPMF energy beta)
    (fun i => (gibbsPMF_positive energy beta i).ne')]
  calc
    _ = ∑ i, ((p i).toReal * Real.log (p i).toReal +
        beta * (energy i * (p i).toReal) +
        Real.log (partitionFunction energy beta) * (p i).toReal) := by
      apply Finset.sum_congr rfl
      intro i _membership
      by_cases zero : (p i).toReal = 0
      · simp [zero]
      · rw [Real.log_div zero (gibbsPMF_real_positive energy beta i).ne', log_gibbsPMF]
        ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, pmf_sum_toReal, mul_one]
      simp only [entropy, meanEnergy, neg_neg]

/-- An exact real-valued ledger identity, with both KL values finite. -/
theorem klHeatEntropy_commutes (energy : ι → ℝ) (beta : ℝ) (p next : PMF ι) :
    realKL p (gibbsPMF energy beta) - realKL next (gibbsPMF energy beta) =
      entropy next - entropy p -
        beta * ∑ i, energy i * ((next i).toReal - (p i).toReal) := by
  rw [realKL_gibbs, realKL_gibbs]
  simp only [mul_sub, Finset.sum_sub_distrib, meanEnergy]
  ring

theorem mix_realKL_contracts (energy : ι → ℝ) (beta : ℝ) (p : PMF ι)
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    realKL (mixPMF p (gibbsPMF energy beta) a ha0 ha1) (gibbsPMF energy beta) ≤
      realKL p (gibbsPMF energy beta) :=
  ENNReal.toReal_mono (gibbs_kl_finite energy beta p)
    (mix_kl_contracts p (gibbsPMF energy beta) a ha0 ha1)

/-- The actual population mixture consumes DPI to produce the Clausius sum. -/
theorem mix_clausius (energy : ι → ℝ) (beta : ℝ) (p : PMF ι)
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    let next := mixPMF p (gibbsPMF energy beta) a ha0 ha1
    0 ≤ entropy next - entropy p -
      beta * ∑ i, energy i * ((next i).toReal - (p i).toReal) := by
  dsimp only
  rw [← klHeatEntropy_commutes]
  exact sub_nonneg.mpr (mix_realKL_contracts energy beta p a ha0 ha1)

end

end LAlanine40K2025.Thermal.Population
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
