import H0mework.Physics.Holonomic.AnholonomicSource

/-!
# Native first variation of the physical `II+` substitution

These two finite-coordinate maps are the dependency-light differential
grammar of `physicalIIPlusBivector e = ⋆ᵢ(e ∧ e)`.  They carry no source,
action, shell, stationarity, residual, or fixed-actual data.

The declarations retain their historical namespace so existing Stage-9
consumers keep the same fully qualified names while the definitions no longer
depend on the C3h105 source/action history chain.
-/

namespace SaturationMonoid.PhysicsCore.StageNineCartanTangentSimplicityResponse

open ProofFreeRicherAnholonomicSource

noncomputable section

set_option autoImplicit false

/-- The bilinear first variation of `e ∧ e` in the coframe direction
`tangent`. -/
def coframeWedgeTangent
    (coframe tangent : LorentzianCoframe) : PhysicalBivector :=
  fun internalPair spacetimePair =>
    tangent (pairFirst internalPair) (pairFirst spacetimePair) *
        coframe (pairSecond internalPair) (pairSecond spacetimePair) +
      coframe (pairFirst internalPair) (pairFirst spacetimePair) *
        tangent (pairSecond internalPair) (pairSecond spacetimePair) -
      tangent (pairFirst internalPair) (pairSecond spacetimePair) *
        coframe (pairSecond internalPair) (pairFirst spacetimePair) -
      coframe (pairFirst internalPair) (pairSecond spacetimePair) *
        tangent (pairSecond internalPair) (pairFirst spacetimePair)

/-- The native first variation `D II+(coframe)[tangent]`. -/
def physicalIIPlusCoframeTangent
    (coframe tangent : LorentzianCoframe) : PhysicalBivector :=
  internalBivectorDual (coframeWedgeTangent coframe tangent)

/-- Exact quadratic expansion of the native `II+` grammar along an affine
coframe path.  This is action-independent and keeps the genuine second-order
term visible. -/
theorem physicalIIPlusBivector_affine_expansion
    (coframe tangent : LorentzianCoframe) (parameter : ℝ) :
    physicalIIPlusBivector (coframe + parameter • tangent) =
      physicalIIPlusBivector coframe +
        parameter • physicalIIPlusCoframeTangent coframe tangent +
        parameter ^ 2 • physicalIIPlusBivector tangent := by
  funext internalPair spacetimePair
  fin_cases internalPair <;> fin_cases spacetimePair <;>
    simp [physicalIIPlusBivector, physicalIIPlusCoframeTangent,
      coframeWedgeTangent, coframeWedge, internalBivectorDual,
      lorentzianCoframeHodge, pairFirst, pairSecond,
      Matrix.add_apply, Matrix.smul_apply] <;>
    ring

end

end SaturationMonoid.PhysicsCore.StageNineCartanTangentSimplicityResponse
