import H0mework.Physics.LowEnergy.BosonEffective.Order
import H0mework.Physics.LowEnergy.BosonEffective.Analytic
import H0mework.Physics.LowEnergy.BosonEffective.Readback
import H0mework.Physics.LowEnergy.BosonEffective.Metric
import Mathlib.Analysis.CStarAlgebra.Matrix

set_option autoImplicit false
open scoped Matrix Matrix.Norms.L2Operator
namespace SaturationMonoid.PhysicsCore.LowEnergy.BosonEffective.Consumer
noncomputable section

theorem source55_matter48_response (A : Matrix (Fin 55) (Fin 55) ℂ)
    (B : Matrix (Fin 55) (Fin 48) ℂ) (C : Matrix (Fin 48) (Fin 55) ℂ)
    (D G : Matrix (Fin 48) (Fin 48) ℂ) (R : Matrix (Fin 55) (Fin 55) ℂ)
    (matterInverse : D*G=1) (bosonInverse : schur A B C G*R=1) (current : Fin 55 → ℂ) :
    A*ᵥ(R*ᵥcurrent)+B*ᵥmatterWrite G C (R*ᵥcurrent)=current ∧
    C*ᵥ(R*ᵥcurrent)+D*ᵥmatterWrite G C (R*ᵥcurrent)=0 :=
  full_response _ _ _ _ _ _ matterInverse bosonInverse _

theorem original168_auxiliary_order (A : Matrix (Fin 168) (Fin 168) ℂ)
    (B : Matrix (Fin 168) (Fin 48) ℂ) (C : Matrix (Fin 48) (Fin 168) ℂ)
    (D : Matrix (Fin 48) (Fin 48) ℂ)
    [Invertible A] [Invertible D] [Invertible (D-C*⅟A*B)] [Invertible (A-B*⅟D*C)] :
    auxiliaryFirst A B C D=matterFirst A B C D := elimination_order _ _ _ _

theorem heavy42_second_order (A G delta : Matrix (Fin 42) (Fin 42) ℂ)
    (left : G*A=1) (right : A*G=1) (small : ‖G*delta‖<1) :
    IsUnit (A+delta) ∧
    ‖Ring.inverse (A+delta)-inverseJet G delta‖≤‖G*delta‖^3*‖Ring.inverse (A+delta)‖ :=
  ⟨perturbation_regular _ _ _ left right small,inverse_remainder_bound _ _ _ left right small⟩

theorem original289_boson55_propagator (H : Matrix (Fin 289) (Fin 289) ℂ)
    (F J : Matrix (Fin 289) (Fin 55) ℂ) (S R : Matrix (Fin 55) (Fin 55) ℂ)
    (sourceBridge : H*F=J*S) (inverse : S*R=1) (current : Fin 55 → ℂ) :
    H*ᵥ(F*ᵥ(R*ᵥcurrent))=J*ᵥcurrent := original_source_response _ _ _ _ _ sourceBridge inverse _

theorem source42_cubic_identity (A G delta : Matrix (Fin 42) (Fin 42) ℂ) (right : A*G=1) :
    (A+delta)*inverseJet G delta=1+delta*G*delta*G*delta*G := inverseJet_residual _ _ _ right

open Filter Topology in
theorem true_dynamic_metric_low_ray (r : ℝ) (regular : 162*r^2-125≠0) :
    Tendsto (fun q : ℝ => Metric.response (r*q) q) (𝓝[≠] 0) (𝓝 (Metric.leading r)) :=
  Metric.source_ray_limit r regular

theorem source_metric_two_limits : Metric.leading 0≠Metric.leading 1 := Metric.two_directional_limits_differ

#print axioms source55_matter48_response
#print axioms original168_auxiliary_order
#print axioms heavy42_second_order
#print axioms original289_boson55_propagator
#print axioms source42_cubic_identity
#print axioms true_dynamic_metric_low_ray
#print axioms source_metric_two_limits
end
end SaturationMonoid.PhysicsCore.LowEnergy.BosonEffective.Consumer
