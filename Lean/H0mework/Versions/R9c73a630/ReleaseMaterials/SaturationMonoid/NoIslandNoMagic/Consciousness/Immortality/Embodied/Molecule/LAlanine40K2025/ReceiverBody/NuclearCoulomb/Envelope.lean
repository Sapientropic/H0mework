import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearBasis.Calculus
import H0mework.Chemistry.LAlanineBandGlobalSource.Decay.Term
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.SpecificCodomains.Pi

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearCoulomb
open BasinRefinement SourceGaussianModel GlobalSource NuclearBasis
open MeasureTheory
noncomputable section

theorem sum_square_bound (x : Point) : (∑ k : Fin 3, (x k)^2) ≤ 3 * ‖x‖^2 := by
  have each (k : Fin 3) : (x k)^2 ≤ ‖x‖^2 := by
    have bound : |x k| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x k
    nlinarith [sq_abs (x k),abs_nonneg (x k),norm_nonneg x]
  simp only [Fin.sum_univ_three]
  linarith only [each 0,each 1,each 2]

theorem bounded_centre_square (x c : Point) (C : ℝ) (bounded : ‖c‖ ≤ C) :
    (∑ k : Fin 3, (x k)^2) ≤ 6 * ‖x-c‖^2 + 6 * C^2 := by
  have triangle : ‖x‖ ≤ ‖x-c‖ + ‖c‖ := by
    simpa only [sub_add_cancel] using norm_add_le (x-c) c
  have centre : ‖c‖^2 ≤ C^2 := by nlinarith [norm_nonneg c]
  have square : ‖x‖^2 ≤ 2 * ‖x-c‖^2 + 2 * ‖c‖^2 := by
    nlinarith [norm_nonneg x,norm_nonneg (x-c),norm_nonneg c,sq_nonneg (‖x-c‖-‖c‖)]
  linarith only [sum_square_bound x,square,centre]

def envelopeScale (term : Term) (jet : MultiIndex) (C : ℝ) : ℝ :=
  (termBound term jet : ℝ) * Real.exp ((term.exponent : ℝ)/2 * C^2)

def envelope (term : Term) (jet : MultiIndex) (C : ℝ) (x : Point) : ℝ :=
  envelopeScale term jet C * ∏ k : Fin 3, Real.exp (-((term.exponent : ℝ)/12) * (x k)^2)

theorem envelope_nonnegative (term : Term) (jet : MultiIndex) (C : ℝ) (x : Point) :
    0 ≤ envelope term jet C x := by
  unfold envelope envelopeScale
  positivity

theorem envelope_normal (term : Term) (jet : MultiIndex) (C : ℝ) (x : Point) :
    envelope term jet C x = envelopeScale term jet C *
      Real.exp (-((term.exponent : ℝ)/12) * ∑ k : Fin 3, (x k)^2) := by
  simp only [envelope,Fin.prod_univ_three,Fin.sum_univ_three,mul_add,Real.exp_add]

theorem envelope_bounded (term : Term) (positive : 0 < term.exponent) (jet : MultiIndex) (C : ℝ) (x : Point) :
    envelope term jet C x ≤ envelopeScale term jet C := by
  have alpha : (0 : ℝ) < term.exponent := by exact_mod_cast positive
  have sum : 0 ≤ ∑ k : Fin 3, (x k)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have decay : Real.exp (-((term.exponent : ℝ)/12) * ∑ k : Fin 3, (x k)^2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) sum)
  rw [envelope_normal]
  exact (mul_le_mul_of_nonneg_left decay (by unfold envelopeScale; positivity)).trans_eq (mul_one _)

theorem envelope_integrable (term : Term) (positive : 0 < term.exponent) (jet : MultiIndex) (C : ℝ) :
    Integrable (envelope term jet C) := by
  have alpha : (0 : ℝ) < term.exponent := by exact_mod_cast positive
  exact (Integrable.fintype_prod (fun _ : Fin 3 => integrable_exp_neg_mul_sq
    (show (0 : ℝ) < (term.exponent : ℝ)/12 by positivity))).const_mul (envelopeScale term jet C)

theorem centred_uniform_tail (term : Term) (positive : 0 < term.exponent) (jet : MultiIndex)
    (C : ℝ) (c x : Point) (bounded : ‖c‖ ≤ C) :
    |centredValue term jet c x| ≤ envelope term jet C x := by
  have tail := term_gaussian_tail term positive jet (fun k => x k-c k+(term.centre k : ℝ))
  have recentre : (fun k => x k-c k+(term.centre k : ℝ)) - termCentre term = x-c := by
    funext k
    simp only [Pi.sub_apply,termCentre,add_sub_cancel_right]
  rw [recentre] at tail
  have alpha : (0 : ℝ) < term.exponent := by exact_mod_cast positive
  have scaled := mul_le_mul_of_nonneg_left (bounded_centre_square x c C bounded)
    (show (0 : ℝ) ≤ (term.exponent : ℝ)/12 by positivity)
  have exponent : -((term.exponent : ℝ)/2) * ‖x-c‖^2 ≤
      (term.exponent : ℝ)/2 * C^2 - (term.exponent : ℝ)/12 * ∑ k : Fin 3, (x k)^2 := by
    nlinarith only [scaled]
  change |centredValue term jet c x| ≤ _ at tail
  apply tail.trans
  rw [envelope_normal,envelopeScale]
  have expanded : Real.exp ((term.exponent : ℝ)/2 * C^2) *
      Real.exp (-((term.exponent : ℝ)/12) * ∑ k : Fin 3, (x k)^2) =
      Real.exp ((term.exponent : ℝ)/2 * C^2 - (term.exponent : ℝ)/12 * ∑ k : Fin 3, (x k)^2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [mul_assoc,expanded]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr exponent) (termBound term jet).coe_nonneg

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearCoulomb
