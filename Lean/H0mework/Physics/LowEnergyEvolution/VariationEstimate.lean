import H0mework.Physics.LowEnergyEvolution.Variation

/-! A Gronwall estimate of the actual nonlinear solution against the source Jacobian flow. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Evolution.Variation
open Set Filter Metric
open scoped Topology
noncomputable section

def linearError (family : UniformDevelopment baseState) (initial : State) (time : ℝ) : State :=
  displacement family initial time-linearFlow time (initial-baseState)

def growthBound : ℝ := ‖jacobian‖+1
theorem growthBound_positive : 0 < growthBound := by unfold growthBound; positivity

theorem linearError_initial (family : UniformDevelopment baseState) (initial : State)
    (inside : initial ∈ closedBall baseState family.initialRadius) : linearError family initial 0 = 0 := by
  rw [linearError, displacement_initial family initial inside, linearFlow_zero]
  simp

theorem linearError_derivative (family : UniformDevelopment baseState) (initial : State)
    (initialInside : initial ∈ closedBall baseState family.initialRadius) (time : ℝ)
    (inside : time ∈ Ioo (-family.timeRadius) family.timeRadius) :
    HasDerivAt (linearError family initial)
      (centeredGenerator (displacement family initial time)-jacobian (linearFlow time (initial-baseState))) time :=
  (displacement_derivative family initial initialInside time inside).sub (linearFlow_derivative _ time)

theorem norm_linearError_le (family : UniformDevelopment baseState) (initial : State)
    (initialInside : initial ∈ closedBall baseState family.initialRadius)
    (sign horizon remainderBound : ℝ) (signNorm : |sign| = 1)
    (horizonNonnegative : 0 ≤ horizon) (horizonInside : horizon < family.timeRadius)
    (remainder : ∀ t ∈ Icc 0 horizon,
      ‖centeredGenerator (displacement family initial (sign*t))-
        jacobian (displacement family initial (sign*t))‖ ≤ remainderBound) :
    ‖linearError family initial (sign*horizon)‖ ≤ gronwallBound 0 growthBound remainderBound horizon := by
  have temporal (t : ℝ) (inside : t ∈ Icc 0 horizon) : sign*t ∈ Ioo (-family.timeRadius) family.timeRadius := by
    apply abs_lt.mp
    rw [abs_mul, signNorm, one_mul, abs_of_nonneg inside.1]
    exact lt_of_le_of_lt inside.2 horizonInside
  have derivative (t : ℝ) (inside : t ∈ Icc 0 horizon) :
      HasDerivAt (fun u => linearError family initial (sign*u))
        (sign • (centeredGenerator (displacement family initial (sign*t))-
          jacobian (linearFlow (sign*t) (initial-baseState)))) t := by
    convert! (linearError_derivative family initial initialInside (sign*t) (temporal t inside)).scomp t
      ((hasDerivAt_id t).const_mul sign) using 1
    simp
  have bound (t : ℝ) (inside : t ∈ Ico 0 horizon) :
      ‖sign • (centeredGenerator (displacement family initial (sign*t))-
        jacobian (linearFlow (sign*t) (initial-baseState)))‖ ≤
      growthBound * ‖linearError family initial (sign*t)‖+remainderBound := by
    rw [norm_smul, Real.norm_eq_abs, signNorm, one_mul]
    have decomposition : centeredGenerator (displacement family initial (sign*t))-
        jacobian (linearFlow (sign*t) (initial-baseState)) =
        jacobian (linearError family initial (sign*t))+
          (centeredGenerator (displacement family initial (sign*t))-
            jacobian (displacement family initial (sign*t))) := by
      simp only [linearError, map_sub]
      abel
    rw [decomposition]
    calc
      _ ≤ ‖jacobian (linearError family initial (sign*t))‖+
          ‖centeredGenerator (displacement family initial (sign*t))-
            jacobian (displacement family initial (sign*t))‖ := norm_add_le _ _
      _ ≤ ‖jacobian‖*‖linearError family initial (sign*t)‖+remainderBound :=
        add_le_add (jacobian.le_opNorm _) (remainder t (Ico_subset_Icc_self inside))
      _ ≤ _ := by unfold growthBound; nlinarith [norm_nonneg (linearError family initial (sign*t))]
  have estimated := norm_le_gronwallBound_of_norm_deriv_right_le
    (HasDerivAt.continuousOn derivative)
    (fun t ht => (derivative t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (show ‖linearError family initial (sign*0)‖ ≤ 0 by rw [mul_zero, linearError_initial family initial initialInside]; simp)
    bound horizon ⟨horizonNonnegative, le_rfl⟩
  simpa only [sub_zero] using estimated

end
end SaturationMonoid.PhysicsCore.LowEnergy.Evolution.Variation
