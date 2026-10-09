import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Calculus.Deriv.Star

/-! A real parameter differentiates the complex Hilbert adjoint in operator norm. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryCurrent
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

local instance : StarModule ℝ (E →L[ℂ] E) where
  star_smul r A := by
    change star (r • A)=r • star A
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ),star_smul,
      RCLike.real_smul_eq_coe_smul (K := ℂ)]
    simp

theorem adjoint_derivative (A : ℝ → E →L[ℂ] E) (t : ℝ) (d : E →L[ℂ] E)
    (differentiated : HasDerivAt A d t) :
    HasDerivAt (fun r => (A r).adjoint) d.adjoint t := by
  simpa only [ContinuousLinearMap.star_eq_adjoint] using! differentiated.star

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryCurrent
