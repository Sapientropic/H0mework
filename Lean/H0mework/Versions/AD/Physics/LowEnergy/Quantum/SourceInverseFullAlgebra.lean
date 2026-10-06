import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceInverseVolumeAlgebra

set_option autoImplicit false
noncomputable section
namespace LowEnergy.InverseVolumeFullAlgebra
open InverseVolumeWardAlgebra
variable {R : Type*} [Ring R] [Algebra ℂ R]

/-- The coefficient is generated from the three source weights, before any source operator unfolds. -/
theorem source_weight (p g c : R →ₗ[ℂ] R) (γ a d : ℂ) (A : R)
    (hp : p A=a • A) (hg : g A=0) (hc : c A=d • A) :
    inverseWard p g c γ A=
      (4*a+γ*(a^2-3*a+2)*(d^3+12*d^2+44*d+48)) • A := by
  simp only [inverseWard,mixedPolynomial,affinePolynomial,inverseLocalPolynomial,
    hp,hg,hc,map_add,map_smul,map_zero,smul_zero,sub_zero]
  module

end LowEnergy.InverseVolumeFullAlgebra
