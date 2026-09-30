import H0mework.Physics.LowEnergy.DrivenInteraction.Pairings
import H0mework.Physics.LowEnergy.LightCausal.Development
import H0mework.Physics.LowEnergy.LightCausal.Reality

/-! Four source growth pairings combine into position and velocity products without commuting the quantum current operators. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.DrivenInteraction
open LightInteraction LightCausal LightSpace Stage9C.Material.SpinPair
noncomputable section
variable {A : Type*} [Ring A] [Algebra ℂ A]

def fourPair (same opposite : ℂ) (first second : Bool → A) : A :=
  ∑ a, ∑ b, (if a=b then same else opposite) • (first a*second b)

theorem four_pair_decomposition (same opposite : ℂ) (first second : Bool → A) :
    fourPair same opposite first second=
      ((same-opposite)/2) • ((first true-first false)*(second true-second false))+
      ((same+opposite)/2) • ((first true+first false)*(second true+second false)) := by
  simp only [fourPair,Fintype.sum_bool,Bool.false_eq_true,Bool.true_eq_false,↓reduceIte,
    add_mul,mul_add,sub_mul,mul_sub]
  module

theorem four_pair_coordinates (same opposite residue rate : ℂ) (first second : Bool → A)
    (residueNonzero : residue≠0) (rateNonzero : rate≠0) :
    fourPair same opposite first second=
      ((same-opposite)/(2*residue^2)) •
        (((-residue) • (first true-first false))*((-residue) • (second true-second false)))+
      ((same+opposite)/(2*residue^2*rate^2)) •
        (((-residue*rate) • (first true+first false))*((-residue*rate) • (second true+second false))) := by
  have position : ((same-opposite)/(2*residue^2))*((-residue)*(-residue))=(same-opposite)/2 := by
    field_simp
  have velocity : ((same+opposite)/(2*residue^2*rate^2))*((-residue*rate)*(-residue*rate))=(same+opposite)/2 := by
    field_simp
  rw [smul_mul_smul_comm,smul_mul_smul_comm,smul_smul,smul_smul,position,velocity]
  exact four_pair_decomposition same opposite first second

def positionWeight (momentum : Fin 3 → ℝ) : ℝ :=
  (physicalGrowthCoupling (radialMomentum momentum)-physicalCoupling (radialMomentum momentum))/
    (2*(metricResidueReal momentum)^2)

def velocityWeight (momentum : Fin 3 → ℝ) : ℝ :=
  (physicalGrowthCoupling (radialMomentum momentum)+physicalCoupling (radialMomentum momentum))/
    (2*(metricResidueReal momentum)^2*(thetaRate momentum)^2)

theorem velocity_weight_positive (momentum : Fin 3 → ℝ) (nonzero : momentum≠0)
    (small : Rotation.momentumRadius momentum ≤ spinScale*LightModes.momentumRadius) :
    0<velocityWeight momentum := by
  have same := physical_growth_coupling_positive (radialMomentum momentum) (radial_small momentum small)
  have opposite := physical_coupling_positive (radialMomentum momentum) (radial_small momentum small)
  have residueNonzero : metricResidueReal momentum≠0 := by
    intro zero
    have wrong := metricResidueReal_cast momentum
    rw [zero,Complex.ofReal_zero] at wrong
    exact metricResidue_nonzero momentum nonzero small wrong.symm
  unfold velocityWeight
  exact div_pos (add_pos same opposite)
    (mul_pos (mul_pos (by norm_num) (sq_pos_of_ne_zero residueNonzero))
      (sq_pos_of_pos (thetaRate_positive momentum nonzero)))

end
end SaturationMonoid.PhysicsCore.LowEnergy.DrivenInteraction
