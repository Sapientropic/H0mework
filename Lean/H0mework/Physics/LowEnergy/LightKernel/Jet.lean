import H0mework.Physics.LowEnergy.BosonEffective.Analytic

/-! The full original polynomial complement generates its quadratic inverse
jet and an exact remainder, so the light calculation is not performed on a
truncation treated as an exact source. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.LightKernel
noncomputable section
section Algebra
variable {R : Type*} [Ring R]

def quadraticInverse (G linear quadratic : R) : R :=
  G-G*linear*G+G*linear*G*linear*G-G*quadratic*G

def inverseResidual (G linear quadratic : R) : R :=
  linear*G*linear*G*linear*G-linear*G*quadratic*G-quadratic*G*linear*G+
    quadratic*G*linear*G*linear*G-quadratic*G*quadratic*G

theorem quadratic_inverse_residual (A G linear quadratic : R) (right : A*G=1) :
    (A+linear+quadratic)*quadraticInverse G linear quadratic=1+inverseResidual G linear quadratic := by
  unfold quadraticInverse inverseResidual
  calc
    _ = A*G-(A*G)*linear*G+(A*G)*linear*G*linear*G-(A*G)*quadratic*G+
      linear*G-linear*G*linear*G+linear*G*linear*G*linear*G-linear*G*quadratic*G+
      quadratic*G-quadratic*G*linear*G+quadratic*G*linear*G*linear*G-quadratic*G*quadratic*G := by noncomm_ring
    _ = _ := by rw [right]; noncomm_ring

theorem quadratic_inverse_exact (A G linear quadratic actual : R)
    (right : A*G=1) (actualLeft : actual*(A+linear+quadratic)=1) :
    actual=quadraticInverse G linear quadratic-actual*inverseResidual G linear quadratic := by
  have identity := congrArg (fun x => actual*x) (quadratic_inverse_residual A G linear quadratic right)
  rw [← mul_assoc,actualLeft,one_mul,mul_add,mul_one] at identity
  exact eq_sub_of_add_eq identity.symm

end Algebra

theorem source_complement_inverse {R : Type*} [NormedRing R] [CompleteSpace R]
    (A G linear quadratic : R) (left : G*A=1) (right : A*G=1)
    (small : ‖G*(linear+quadratic)‖<1) :
    IsUnit (A+linear+quadratic) ∧
    Ring.inverse (A+linear+quadratic)=quadraticInverse G linear quadratic-
      Ring.inverse (A+linear+quadratic)*inverseResidual G linear quadratic := by
  have regular : IsUnit (A+linear+quadratic) := by
    simpa only [add_assoc] using BosonEffective.perturbation_regular A G (linear+quadratic) left right small
  exact ⟨regular,quadratic_inverse_exact A G linear quadratic _ right (Ring.inverse_mul_cancel _ regular)⟩

end
end SaturationMonoid.PhysicsCore.LowEnergy.LightKernel
