import H0mework.Chemistry.LAlanineEntropy.UnitaryBornKernel
import H0mework.Chemistry.LAlanineEntropy.FiniteThermalEntropy

/-! # Unitary measurement increases diagonal entropy by the existing classical DPI -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Quantum

open MeasureTheory ProbabilityTheory InformationTheory
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Population
open scoped ENNReal

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def uniformReference : PMF ι := gibbsPMF (fun _ : ι => 0) 1

theorem bornPopulation_uniform (U : Matrix.unitaryGroup ι ℂ) :
    bornPopulation U uniformReference = uniformReference := by
  ext i
  apply (ENNReal.toReal_eq_toReal_iff' ((bornPopulation U uniformReference).apply_ne_top i)
    (uniformReference.apply_ne_top i)).mp
  rw [bornPopulation_toReal]
  simp only [uniformReference, gibbsPMF_toReal, mul_zero, Real.exp_zero]
  rw [← Finset.mul_sum, bornWeight_row, mul_one]

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem bornKernel_uniform (U : Matrix.unitaryGroup ι ℂ) :
    bornKernel U ∘ₘ (uniformReference : PMF ι).toMeasure = uniformReference.toMeasure := by
  rw [bornKernel_comp, bornPopulation_uniform]

theorem born_entropy_nondecreasing (U : Matrix.unitaryGroup ι ℂ) (p : PMF ι) :
    entropy p ≤ entropy (bornPopulation U p) := by
  have contraction := invariantKernel_kl p (uniformReference : PMF ι) (bornKernel U)
    (bornKernel_uniform U)
  rw [bornKernel_comp] at contraction
  have finiteBefore := gibbs_kl_finite (fun _ : ι => 0) 1 p
  have realContraction := ENNReal.toReal_mono finiteBefore contraction
  change realKL (bornPopulation U p) (gibbsPMF (fun _ : ι => 0) 1) ≤
    realKL p (gibbsPMF (fun _ : ι => 0) 1) at realContraction
  rw [realKL_gibbs, realKL_gibbs] at realContraction
  simp only [meanEnergy, zero_mul, Finset.sum_const_zero, mul_zero, add_zero] at realContraction
  linarith

end

end LAlanine40K2025.Thermal.Quantum
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
