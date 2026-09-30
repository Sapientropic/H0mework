import H0mework.Physics.LowEnergy.BosonEffective.Schur

/-! A faithful source equation bridge returns the effective propagator to all
original rows, including the independently generated Ward-source injection. -/
set_option autoImplicit false
open scoped Matrix
namespace SaturationMonoid.PhysicsCore.LowEnergy.BosonEffective
noncomputable section
variable {n b : Type*} [Fintype n] [Fintype b] [DecidableEq b]

theorem original_source_response (H : Matrix n n ℂ) (F J : Matrix n b ℂ)
    (S R : Matrix b b ℂ) (sourceBridge : H*F=J*S) (inverse : S*R=1) (source : b → ℂ) :
    H*ᵥ(F*ᵥ(R*ᵥsource))=J*ᵥsource := by
  rw [Matrix.mulVec_mulVec (R*ᵥsource) H F,sourceBridge,← Matrix.mulVec_mulVec (R*ᵥsource) J S,
    Matrix.mulVec_mulVec source S R,inverse,Matrix.one_mulVec]

omit [DecidableEq b] in
theorem original_source_remainder (H : Matrix n n ℂ) (F J : Matrix n b ℂ)
    (S R remainder : Matrix b b ℂ) (sourceBridge : H*F=J*S)
    (inverseRemainder : S*R=remainder) (source : b → ℂ) :
    H*ᵥ(F*ᵥ(R*ᵥsource))=J*ᵥ(remainder*ᵥsource) := by
  rw [Matrix.mulVec_mulVec (R*ᵥsource) H F,sourceBridge,← Matrix.mulVec_mulVec (R*ᵥsource) J S,
    Matrix.mulVec_mulVec source S R,inverseRemainder]

end
end SaturationMonoid.PhysicsCore.LowEnergy.BosonEffective
