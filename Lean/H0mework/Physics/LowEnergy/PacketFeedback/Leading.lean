import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.Basic

/-! The true vector derivative fixes the quadratic norm limit on any real normed space. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketFeedback
open Filter Topology
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_square_slope (field : ℝ → E) (direction : E)
    (initial : field 0=0) (derivative : HasDerivAt field direction 0) :
    Tendsto (fun time : ℝ => ‖field time‖^2/time^2) (𝓝[≠] 0) (𝓝 (‖direction‖^2)) := by
  have squareContinuous : Continuous (fun value : E => ‖value‖^2) := continuous_norm.pow 2
  have generated := squareContinuous.continuousAt.tendsto.comp derivative.tendsto_slope
  convert! generated using 1
  funext time
  simp only [Function.comp_def,slope,initial,vsub_eq_sub,sub_zero,norm_smul,
    Real.norm_eq_abs,mul_pow,sq_abs,inv_pow,div_eq_mul_inv,mul_comm]

theorem quadratic_norm_leading (positionWeight velocityWeight : ℝ)
    (position velocity : ℝ → E) (acceleration : E)
    (positionInitial : position 0=0) (velocityInitial : velocity 0=0)
    (positionDerivative : HasDerivAt position 0 0)
    (velocityDerivative : HasDerivAt velocity acceleration 0) :
    Tendsto (fun time : ℝ =>
        (positionWeight*‖position time‖^2+velocityWeight*‖velocity time‖^2)/time^2)
      (𝓝[≠] 0) (𝓝 (velocityWeight*‖acceleration‖^2)) := by
  have positionLimit := (norm_square_slope position 0 positionInitial positionDerivative).const_mul positionWeight
  have velocityLimit := (norm_square_slope velocity acceleration velocityInitial velocityDerivative).const_mul velocityWeight
  have generated := positionLimit.add velocityLimit
  simp only [norm_zero,zero_pow (by decide : (2 : ℕ)≠0),mul_zero,zero_add] at generated
  convert! generated using 1
  funext time
  ring

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketFeedback
