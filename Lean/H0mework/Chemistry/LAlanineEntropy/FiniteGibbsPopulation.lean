import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Strictly positive Gibbs PMFs generated from a finite energy family -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Population

open scoped ENNReal BigOperators

variable {ι : Type*} [Fintype ι]

noncomputable section

def partitionFunction (energy : ι → ℝ) (beta : ℝ) : ℝ :=
  ∑ i, Real.exp (-beta * energy i)

theorem partitionFunction_positive [Nonempty ι] (energy : ι → ℝ) (beta : ℝ) :
    0 < partitionFunction energy beta := by
  exact Finset.sum_pos (fun i _ => Real.exp_pos (-beta * energy i)) Finset.univ_nonempty

def gibbsProbability (energy : ι → ℝ) (beta : ℝ) (i : ι) : ℝ :=
  Real.exp (-beta * energy i) / partitionFunction energy beta

theorem gibbsProbability_positive [Nonempty ι] (energy : ι → ℝ) (beta : ℝ) (i : ι) :
    0 < gibbsProbability energy beta i :=
  div_pos (Real.exp_pos _) (partitionFunction_positive energy beta)

theorem gibbsProbability_sum [Nonempty ι] (energy : ι → ℝ) (beta : ℝ) :
    ∑ i, gibbsProbability energy beta i = 1 := by
  simp only [gibbsProbability, ← Finset.sum_div]
  exact div_self (partitionFunction_positive energy beta).ne'

def gibbsPMF [Nonempty ι] (energy : ι → ℝ) (beta : ℝ) : PMF ι :=
  PMF.ofFintype (fun i => ENNReal.ofReal (gibbsProbability energy beta i)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun i _ => (gibbsProbability_positive energy beta i).le), gibbsProbability_sum]
    simp)

@[simp] theorem gibbsPMF_apply [Nonempty ι] (energy : ι → ℝ) (beta : ℝ) (i : ι) :
    gibbsPMF energy beta i = ENNReal.ofReal (gibbsProbability energy beta i) := rfl

theorem gibbsPMF_toReal [Nonempty ι] (energy : ι → ℝ) (beta : ℝ) (i : ι) :
    (gibbsPMF energy beta i).toReal =
      Real.exp (-beta * energy i) / partitionFunction energy beta := by
  rw [gibbsPMF_apply, ENNReal.toReal_ofReal (gibbsProbability_positive energy beta i).le]
  rfl

theorem gibbsPMF_positive [Nonempty ι] (energy : ι → ℝ) (beta : ℝ) (i : ι) :
    0 < gibbsPMF energy beta i := by
  rw [gibbsPMF_apply, ENNReal.ofReal_pos]
  exact gibbsProbability_positive energy beta i

theorem gibbsPMF_real_positive [Nonempty ι] (energy : ι → ℝ) (beta : ℝ) (i : ι) :
    0 < (gibbsPMF energy beta i).toReal := by
  rw [gibbsPMF_toReal]
  exact gibbsProbability_positive energy beta i

theorem log_gibbsPMF [Nonempty ι] (energy : ι → ℝ) (beta : ℝ) (i : ι) :
    Real.log (gibbsPMF energy beta i).toReal =
      -beta * energy i - Real.log (partitionFunction energy beta) := by
  rw [gibbsPMF_toReal, Real.log_div (Real.exp_ne_zero _)
    (partitionFunction_positive energy beta).ne', Real.log_exp]

theorem pmf_sum_toReal (p : PMF ι) : ∑ i, (p i).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun i _ => p.apply_ne_top i)]
  have total : ∑ i, p i = 1 := by simpa only [tsum_fintype] using p.tsum_coe
  rw [total, ENNReal.toReal_one]

def entropy (p : PMF ι) : ℝ := -∑ i, (p i).toReal * Real.log (p i).toReal

def meanEnergy (energy : ι → ℝ) (p : PMF ι) : ℝ :=
  ∑ i, energy i * (p i).toReal

end

end LAlanine40K2025.Thermal.Population
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
