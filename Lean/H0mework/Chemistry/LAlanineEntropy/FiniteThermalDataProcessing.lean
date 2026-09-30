import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-! # Finite thermal populations consume the existing Markov data-processing theorem -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Population

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

variable {ι : Type*}

noncomputable section

theorem invariantKernel_kl [MeasurableSpace ι] (p π : PMF ι) (κ : Kernel ι ι) [IsMarkovKernel κ]
    (invariant : κ ∘ₘ π.toMeasure = π.toMeasure) :
    klDiv (κ ∘ₘ p.toMeasure) π.toMeasure ≤ klDiv p.toMeasure π.toMeasure := by
  simpa only [invariant] using
    InformationTheory.klDiv_comp_right_le p.toMeasure π.toMeasure κ

variable [Fintype ι]

theorem pmf_sum (p : PMF ι) : ∑ i, p i = 1 := by
  simpa only [tsum_fintype] using p.tsum_coe

def mixPMF (p π : PMF ι) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : PMF ι :=
  PMF.ofFintype (fun i => ENNReal.ofReal (1 - a) * p i + ENNReal.ofReal a * π i) (by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, pmf_sum, pmf_sum,
      mul_one, mul_one, ← ENNReal.ofReal_add (sub_nonneg.mpr ha1) ha0]
    simp)

@[simp] theorem mixPMF_apply (p π : PMF ι) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (i : ι) :
    mixPMF p π a ha0 ha1 i =
      ENNReal.ofReal (1 - a) * p i + ENNReal.ofReal a * π i := rfl

theorem mixPMF_apply_toReal (p π : PMF ι) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (i : ι) :
    (mixPMF p π a ha0 ha1 i).toReal = (1 - a) * (p i).toReal + a * (π i).toReal := by
  rw [mixPMF_apply, ENNReal.toReal_add
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (p.apply_ne_top i))
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (π.apply_ne_top i))]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sub_nonneg.mpr ha1),
    ENNReal.toReal_ofReal ha0]

theorem mixPMF_self (π : PMF ι) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    mixPMF π π a ha0 ha1 = π := by
  ext i
  rw [mixPMF_apply, ← add_mul, ← ENNReal.ofReal_add (sub_nonneg.mpr ha1) ha0]
  simp

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

def mixKernel (π : PMF ι) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : Kernel ι ι where
  toFun i := (mixPMF (PMF.pure i) π a ha0 ha1).toMeasure
  measurable' := measurable_of_countable _

instance mixKernel_isMarkov (π : PMF ι) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    IsMarkovKernel (mixKernel π a ha0 ha1) :=
  ⟨fun i => inferInstanceAs (IsProbabilityMeasure (mixPMF (PMF.pure i) π a ha0 ha1).toMeasure)⟩

theorem mixKernel_comp (p π : PMF ι) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    mixKernel π a ha0 ha1 ∘ₘ p.toMeasure = (mixPMF p π a ha0 ha1).toMeasure := by
  classical
  apply Measure.ext_iff_singleton.mpr
  intro j
  rw [Measure.bind_apply (measurableSet_singleton j) (Kernel.aemeasurable _), lintegral_fintype]
  simp [mixKernel, PMF.pure_apply, add_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, pmf_sum]

theorem mixKernel_invariant (π : PMF ι) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    mixKernel π a ha0 ha1 ∘ₘ π.toMeasure = π.toMeasure := by
  rw [mixKernel_comp, mixPMF_self]

theorem mix_kl_contracts (p π : PMF ι) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    klDiv (mixPMF p π a ha0 ha1).toMeasure π.toMeasure ≤ klDiv p.toMeasure π.toMeasure := by
  simpa only [mixKernel_comp] using
    invariantKernel_kl p π (mixKernel π a ha0 ha1) (mixKernel_invariant π a ha0 ha1)

end

end LAlanine40K2025.Thermal.Population
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
