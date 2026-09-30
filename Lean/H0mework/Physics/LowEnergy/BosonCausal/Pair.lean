import H0mework.Physics.LowEnergy.BosonCausal.Laplace
import Mathlib.Analysis.Complex.Trigonometric

/-! Difference pairs give the genuine oscillatory and growing retarded kernels. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.BosonCausal
open MeasureTheory
noncomputable section

def pairKernel (rate : ℂ) (time : ℝ) : ℂ := (mode rate time-mode (-rate) time)/(2*rate)

theorem pair_integrable (rate : ℂ) (energy damping : ℝ)
    (plus : rate.re<damping) (minus : (-rate).re<damping) :
    IntegrableOn (fun t => weight energy damping t*pairKernel rate t) (Set.Ioi 0) := by
  have each (t : ℝ) : weight energy damping t*pairKernel rate t=
      (weight energy damping t*mode rate t-weight energy damping t*mode (-rate) t)/(2*rate) := by
    unfold pairKernel
    ring
  simp_rw [each]
  exact ((mode_integrable rate energy damping plus).sub (mode_integrable (-rate) energy damping minus)).div_const _

theorem pair_fraction (parameter rate : ℂ) (nonzero : rate≠0)
    (left : parameter-rate≠0) (right : parameter+rate≠0) :
    ((parameter-rate)⁻¹-(parameter+rate)⁻¹)/(2*rate)=(parameter^2-rate^2)⁻¹ := by
  have denominator : parameter^2-rate^2≠0 := by
    have factor : parameter^2-rate^2=(parameter-rate)*(parameter+rate) := by ring
    rw [factor]
    exact mul_ne_zero left right
  field_simp
  ring

theorem pair_transform (rate : ℂ) (nonzero : rate≠0) (energy damping : ℝ)
    (plus : rate.re<damping) (minus : (-rate).re<damping) :
    (∫ t : ℝ in Set.Ioi 0, weight energy damping t*pairKernel rate t)=
      ((laplaceParameter energy damping)^2-rate^2)⁻¹ := by
  have each (t : ℝ) : weight energy damping t*pairKernel rate t=
      (weight energy damping t*mode rate t-weight energy damping t*mode (-rate) t)/(2*rate) := by
    unfold pairKernel
    ring
  simp_rw [each]
  rw [integral_div,integral_sub (mode_integrable rate energy damping plus)
    (mode_integrable (-rate) energy damping minus),mode_transform rate energy damping plus,
    mode_transform (-rate) energy damping minus,sub_neg_eq_add]
  apply pair_fraction _ _ nonzero
  · intro same
    have re := congrArg Complex.re same
    simp [laplaceParameter] at re
    linarith
  · intro same
    have re := congrArg Complex.re same
    simp [laplaceParameter] at re
    simp only [Complex.neg_re] at minus
    linarith

theorem pair_hyperbolic (rate time : ℝ) : pairKernel (rate : ℂ) time=
    Complex.sinh ((rate : ℂ)*(time : ℂ))/(rate : ℂ) := by
  unfold pairKernel mode Complex.sinh
  simp only [neg_mul]
  ring

theorem pair_oscillatory (rate time : ℝ) : pairKernel (Complex.I*(rate : ℂ)) time=
    Complex.sin ((rate : ℂ)*(time : ℂ))/(rate : ℂ) := by
  unfold pairKernel mode Complex.sin
  have forward : Complex.I*(rate : ℂ)*(time : ℂ)=((rate : ℂ)*(time : ℂ))*Complex.I := by ring
  have backward : -(Complex.I*(rate : ℂ))*(time : ℂ)= -((rate : ℂ)*(time : ℂ))*Complex.I := by ring
  rw [forward,backward]
  field_simp
  ring_nf
  simp [Complex.I_sq,sub_eq_add_neg]

end
end SaturationMonoid.PhysicsCore.LowEnergy.BosonCausal
