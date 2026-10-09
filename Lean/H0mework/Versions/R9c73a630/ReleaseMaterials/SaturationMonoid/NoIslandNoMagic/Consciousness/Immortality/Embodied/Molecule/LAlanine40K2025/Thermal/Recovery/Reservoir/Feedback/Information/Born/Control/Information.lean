import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Information.Born.BranchMean
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Information.Born.Work
import H0mework.Probability.Recovery.RecoveryMap

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.SourceGeneratedConditionalWork.Information

open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Collision

noncomputable section

local instance : MeasurableSpace PointerIndex := ⊤
local instance : MeasurableSingletonClass PointerIndex := ⟨fun _ => trivial⟩

private theorem norm_difference (left right : ℂ) :
    ‖left - right‖ ^ 2 = (left.re - right.re) ^ 2 + (left.im - right.im) ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  ring

private theorem binary_deviation (p q : ℝ) (left right constant : ℂ)
    (total : p + q = 1) (leftImag : p * left.im = 0) (rightImag : q * right.im = 0) :
    p * ‖left - constant‖ ^ 2 + q * ‖right - constant‖ ^ 2 =
      p * q * (left.re - right.re) ^ 2 +
        ‖((p * left.re + q * right.re : ℝ) : ℂ) - constant‖ ^ 2 := by
  have imaginary (weight : ℝ) (value : ℂ) (zero : weight * value.im = 0) :
      weight * (value.im - constant.im) ^ 2 = weight * constant.im ^ 2 := by
    calc
      _ = (weight * value.im) * (value.im - 2 * constant.im) + weight * constant.im ^ 2 := by ring
      _ = _ := by rw [zero]; ring
  simp only [norm_difference, Complex.ofReal_re, Complex.ofReal_im, zero_sub, neg_sq]
  calc
    _ = p * (left.re - constant.re) ^ 2 + q * (right.re - constant.re) ^ 2 +
        (p + q) * constant.im ^ 2 := by
      calc
        _ = p * (left.re - constant.re) ^ 2 + q * (right.re - constant.re) ^ 2 +
            (p * (left.im - constant.im) ^ 2 + q * (right.im - constant.im) ^ 2) := by ring
        _ = _ := by rw [imaginary p left leftImag, imaginary q right rightImag]; ring
    _ = _ := by
      have qValue : q = 1 - p := by linarith
      rw [total, qValue]
      ring

private theorem weighted_real_decoder {A B : Type*} [Fintype A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B]
    (source : PMF A) (observer : A → B) (task : A → ℝ) (atom : B) :
    ((source.map observer) atom).toReal *
      (SourceWeightedRecovery.optimalDecoder source observer (fun index => (task index : ℂ)) atom).im = 0 := by
  have original := congrArg Complex.im
    (SourceWeightedRecovery.weighted_optimal source observer (fun index => (task index : ℂ)) atom)
  simpa only [SourceWeightedRecovery.observed, Complex.im_sum, Complex.smul_im,
    apply_ite, Complex.ofReal_im, Complex.zero_im, ite_self, smul_zero,
    Finset.sum_const_zero, smul_eq_mul, mul_zero] using original

variable (observable : Current.FullJoint) (hermitian : observable.IsHermitian) (current : Live.State)

def mean : ℂ := energy observable (bodyRead current.joint)

include observable hermitian in
private theorem weights : zeroRead current.joint + oneRead current.joint = 1 := by
  let law := (Born.distribution observable hermitian current).map Born.pointer
  have total := congrArg ENNReal.toReal law.tsum_coe
  rw [tsum_fintype, Fin.sum_univ_two,
    ENNReal.toReal_add (law.apply_ne_top 0) (law.apply_ne_top 1), ENNReal.toReal_one] at total
  exact ((congrArg₂ (· + ·) (Born.pointer_zero_read observable hermitian current)
    (Born.pointer_one_read observable hermitian current)).symm).trans total

private theorem weighted_branch_imag (branch : Fin 2) :
    (((Born.distribution observable hermitian current).map Born.pointer) branch).toReal *
      (Born.bestDecoder observable hermitian current branch).im = 0 :=
  weighted_real_decoder (Born.distribution observable hermitian current) Born.pointer
    (Born.outcome observable hermitian) branch

theorem weighted_decoder_imag_zero :
    zeroRead current.joint * (Born.bestDecoder observable hermitian current 0).im = 0 ∧
      oneRead current.joint * (Born.bestDecoder observable hermitian current 1).im = 0 := by
  have left := weighted_branch_imag observable hermitian current 0
  have right := weighted_branch_imag observable hermitian current 1
  rw [Born.pointer_zero_read] at left
  rw [Born.pointer_one_read] at right
  exact ⟨left, right⟩

theorem first_moment :
    zeroRead current.joint • Born.bestDecoder observable hermitian current 0 +
      oneRead current.joint • Born.bestDecoder observable hermitian current 1 = mean observable current := by
  apply Complex.ext
  · simp only [Complex.add_re, Complex.smul_re, mean, Complex.ofReal_re, smul_eq_mul]
    exact Born.pointerMean_energy observable hermitian current
  · simp only [Complex.add_im, Complex.smul_im, mean, Complex.ofReal_im, smul_eq_mul]
    rw [(weighted_decoder_imag_zero observable hermitian current).1,
      (weighted_decoder_imag_zero observable hermitian current).2, add_zero]

private theorem loss_binary (constant : ℂ) :
    Born.loss observable hermitian current (fun _ => constant) =
      Born.loss observable hermitian current (Born.bestDecoder observable hermitian current) +
        (zeroRead current.joint * ‖Born.bestDecoder observable hermitian current 0 - constant‖ ^ 2 +
          oneRead current.joint * ‖Born.bestDecoder observable hermitian current 1 - constant‖ ^ 2) := by
  have mapped := SourceWeightedRecovery.error_map (Born.distribution observable hermitian current)
    Born.pointer id (Born.bestDecoder observable hermitian current) (fun _ => constant)
  have binary : SourceWeightedRecovery.error (Born.distribution observable hermitian current) Born.pointer
      (fun index => Born.bestDecoder observable hermitian current (Born.pointer index)) (fun _ => constant) =
        zeroRead current.joint * ‖Born.bestDecoder observable hermitian current 0 - constant‖ ^ 2 +
          oneRead current.joint * ‖Born.bestDecoder observable hermitian current 1 - constant‖ ^ 2 := by
    simpa only [Function.comp_def, id_eq, SourceWeightedRecovery.error, Fin.sum_univ_two,
      Born.pointer_zero_read, Born.pointer_one_read] using mapped.symm
  exact (Born.loss_decomposition observable hermitian current (fun _ => constant)).trans
    (congrArg (fun cost : ℝ => Born.loss observable hermitian current
      (Born.bestDecoder observable hermitian current) + cost) binary)

theorem constant_loss_formula (constant : ℂ) :
    Born.loss observable hermitian current (fun _ => constant) =
      Born.loss observable hermitian current (Born.bestDecoder observable hermitian current) +
        zeroRead current.joint * oneRead current.joint *
          ((Born.bestDecoder observable hermitian current 0).re -
            (Born.bestDecoder observable hermitian current 1).re) ^ 2 +
        ‖mean observable current - constant‖ ^ 2 := by
  have realMean := congrArg Complex.re (first_moment observable hermitian current)
  simp only [Complex.add_re, Complex.smul_re, mean, Complex.ofReal_re, smul_eq_mul] at realMean
  have deviation := binary_deviation (zeroRead current.joint) (oneRead current.joint)
    (Born.bestDecoder observable hermitian current 0) (Born.bestDecoder observable hermitian current 1) constant
    (weights observable hermitian current) (weighted_decoder_imag_zero observable hermitian current).1
    (weighted_decoder_imag_zero observable hermitian current).2
  rw [realMean] at deviation
  rw [loss_binary, deviation]
  exact (add_assoc _ _ _).symm

def gain : ℝ :=
  Born.loss observable hermitian current (fun _ => mean observable current) -
    Born.loss observable hermitian current (Born.bestDecoder observable hermitian current)

theorem gain_exact : gain observable hermitian current =
    zeroRead current.joint * oneRead current.joint *
      ((Born.bestDecoder observable hermitian current 0).re -
        (Born.bestDecoder observable hermitian current 1).re) ^ 2 := by
  have formula := constant_loss_formula observable hermitian current (mean observable current)
  simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero] at formula
  unfold gain
  linarith

theorem constant_loss_decomposition (constant : ℂ) :
    Born.loss observable hermitian current (fun _ => constant) =
      Born.loss observable hermitian current (fun _ => mean observable current) +
        ‖mean observable current - constant‖ ^ 2 := by
  have atConstant := constant_loss_formula observable hermitian current constant
  have atMean := constant_loss_formula observable hermitian current (mean observable current)
  simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero] at atMean
  linarith

theorem constant_loss_minimal (constant : ℂ) :
    Born.loss observable hermitian current (fun _ => mean observable current) ≤
      Born.loss observable hermitian current (fun _ => constant) := by
  have decomposition := constant_loss_decomposition observable hermitian current constant
  have nonnegative := sq_nonneg ‖mean observable current - constant‖
  linarith

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.SourceGeneratedConditionalWork.Information
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
