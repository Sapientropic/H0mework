import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.FiniteGain
import Mathlib.Analysis.Calculus.Taylor

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled
open Propagation.Producer Load.Producer.StrictThermal
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def sinePolynomial (x : ℝ) : ℝ := x-x^3/6
def cosinePolynomial (x : ℝ) : ℝ := 1-x^2/2+x^4/24

private theorem sine_taylor (x : ℝ) (positive : 0 < x) :
    taylorWithinEval Real.sin 4 (Set.Icc 0 x) 0 x=sinePolynomial x := by
  rw [taylor_within_apply]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  simp only [Real.iteratedDerivWithin_sin_Icc _ positive (show (0 : ℝ) ∈ Set.Icc 0 x from ⟨le_rfl,positive.le⟩)]
  norm_num [sinePolynomial,iteratedDeriv_succ]
  ring

private theorem cosine_taylor (x : ℝ) (positive : 0 < x) :
    taylorWithinEval Real.cos 4 (Set.Icc 0 x) 0 x=cosinePolynomial x := by
  rw [taylor_within_apply]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  simp only [Real.iteratedDerivWithin_cos_Icc _ positive (show (0 : ℝ) ∈ Set.Icc 0 x from ⟨le_rfl,positive.le⟩)]
  norm_num [cosinePolynomial,iteratedDeriv_succ]
  ring

theorem sine_polynomial_error (x : ℝ) (positive : 0 < x) :
    |Real.sin x-sinePolynomial x| ≤ x^5/24 := by
  have paid := taylor_mean_remainder_bound (f := Real.sin) (n := 4) positive.le Real.contDiff_sin.contDiffOn
    (show x ∈ Set.Icc 0 x from ⟨positive.le,le_rfl⟩) (C := 1)
    (by intro y hy; rw [Real.iteratedDerivWithin_sin_Icc _ positive hy,Real.norm_eq_abs]; exact Real.abs_iteratedDeriv_sin_le_one _ _)
  rw [sine_taylor x positive] at paid
  norm_num only [Real.norm_eq_abs,sub_zero,one_mul,Nat.factorial] at paid
  exact paid

theorem cosine_polynomial_error (x : ℝ) (positive : 0 < x) :
    |Real.cos x-cosinePolynomial x| ≤ x^5/24 := by
  have paid := taylor_mean_remainder_bound (f := Real.cos) (n := 4) positive.le Real.contDiff_cos.contDiffOn
    (show x ∈ Set.Icc 0 x from ⟨positive.le,le_rfl⟩) (C := 1)
    (by intro y hy; rw [Real.iteratedDerivWithin_cos_Icc _ positive hy,Real.norm_eq_abs]; exact Real.abs_iteratedDeriv_cos_le_one _ _)
  rw [cosine_taylor x positive] at paid
  norm_num only [Real.norm_eq_abs,sub_zero,one_mul,Nat.factorial] at paid
  exact paid

theorem source_polynomial_error :
    |Real.cos BasisInverse.actualAngle-sinePolynomial (nativeClockStep : ℝ)| ≤ (1/10^18 : ℝ) ∧
    |Real.sin BasisInverse.actualAngle-cosinePolynomial (nativeClockStep : ℝ)| ≤ (1/10^18 : ℝ) := by
  have bound : (nativeClockStep : ℝ)^5/24 ≤ (1/10^18 : ℝ) := by rw [nativeClockStep_exact]; norm_num
  rw [BasisInverse.actualAngle,Real.cos_pi_div_two_sub,Real.sin_pi_div_two_sub]
  exact ⟨(sine_polynomial_error _ nativeClock_small.1).trans bound,(cosine_polynomial_error _ nativeClock_small.1).trans bound⟩

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
