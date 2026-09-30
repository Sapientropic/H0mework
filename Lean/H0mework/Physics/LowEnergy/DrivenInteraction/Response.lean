import H0mework.Physics.LowEnergy.DrivenInteraction.Time

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.DrivenInteraction
open LightInteraction LightCausal LightSpace Stage9C.Material.SpinPair
noncomputable section
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]

def orientedResponse (momentum : Fin 3 → ℝ) (source : ℝ → A) (time : ℝ) (positive : Bool) : A :=
  forcedVector (growthSign positive*(thetaRate momentum : ℂ)) source time

def drivenPair (momentum : Fin 3 → ℝ) (first second : ℝ → A) (time : ℝ) : A :=
  fourPair (physicalGrowthCoupling (radialMomentum momentum)) (physicalCoupling (radialMomentum momentum))
    (orientedResponse momentum first time) (orientedResponse momentum second time)

theorem driven_pair_whole_growth_sum (momentum : Fin 3 → ℝ) (first second : ℝ → A) (time : ℝ) :
    drivenPair momentum first second time=
      ∑ a, ∑ b, (pairCoupling a b (radialMomentum momentum) : ℂ) •
        (orientedResponse momentum first time a*orientedResponse momentum second time b) := by
  unfold drivenPair fourPair pairCoupling
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  split <;> rfl

theorem driven_pair_field_velocity (momentum : Fin 3 → ℝ) (nonzero : momentum≠0)
    (small : Rotation.momentumRadius momentum ≤ spinScale*LightModes.momentumRadius)
    (first second : ℝ → A) (time : ℝ) :
    drivenPair momentum first second time=
      (positionWeight momentum : ℂ) •
        (metricDevelopment momentum first time*metricDevelopment momentum second time)+
      (velocityWeight momentum : ℂ) •
        (metricVelocity momentum first time*metricVelocity momentum second time) := by
  rw [drivenPair,four_pair_coordinates _ _ (metricResidue momentum) (thetaRate momentum)
    _ _ (metricResidue_nonzero momentum nonzero small)
      (Complex.ofReal_ne_zero.mpr (thetaRate_positive momentum nonzero).ne')]
  simp only [orientedResponse,growthSign,Bool.false_eq_true,↓reduceIte,one_mul,neg_one_mul,
    metricDevelopment,metricVelocity,positionWeight,velocityWeight,
    Complex.ofReal_add,Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_div,
    Complex.ofReal_pow,Complex.ofReal_ofNat,metricResidueReal_cast]

theorem driven_pair_initial (momentum : Fin 3 → ℝ) (first second : ℝ → A) :
    drivenPair momentum first second 0=0 := by
  simp [drivenPair,fourPair,orientedResponse,forcedVector_initial]

end
end SaturationMonoid.PhysicsCore.LowEnergy.DrivenInteraction
