import H0mework.Versions.R2.Arithmetic.RiemannSpectral.FourierFixedCompression

/-!
# Self-adjointness certificate for the Fourier-fixed compression

The explicit complex Hilbert adjoint of the bounded Fourier-fixed
multiplicative compression is itself.  This small boundary file keeps type
class normalization out of the main operator construction.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open scoped InnerProduct

noncomputable section

local instance evenCarrierComplete (radius : ℝ) :
    CompleteSpace (EvenBurnolPhysicalCarrier radius) := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace radius).isClosed.isComplete

local instance fixedCarrierInner (radius : ℝ) :
    InnerProductSpace ℂ (EvenBurnolFourierFixedCarrier radius) :=
  inferInstance

local instance fixedCarrierComplete (radius : ℝ) :
    CompleteSpace (EvenBurnolFourierFixedCarrier radius) := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolFourierFixedFace radius).isClosed.isComplete

theorem evenBurnolFourierFixedCompression_adjoint_eq
    (radius shift : ℝ) :
    (@ContinuousLinearMap.adjoint ℂ
      (EvenBurnolFourierFixedCarrier radius)
      (EvenBurnolFourierFixedCarrier radius)
      _ _ _ (fixedCarrierInner radius) (fixedCarrierInner radius)
      (fixedCarrierComplete radius) (fixedCarrierComplete radius))
        (evenBurnolFourierFixedCompression radius shift) =
      evenBurnolFourierFixedCompression radius shift := by
  apply ContinuousLinearMap.ext
  intro right
  apply ext_inner_left ℂ
  intro left
  calc
    inner ℂ left
        ((@ContinuousLinearMap.adjoint ℂ
          (EvenBurnolFourierFixedCarrier radius)
          (EvenBurnolFourierFixedCarrier radius)
          _ _ _ (fixedCarrierInner radius) (fixedCarrierInner radius)
          (fixedCarrierComplete radius) (fixedCarrierComplete radius))
            (evenBurnolFourierFixedCompression radius shift) right) =
      inner ℂ (evenBurnolFourierFixedCompression radius shift left) right :=
        @ContinuousLinearMap.adjoint_inner_right ℂ
          (EvenBurnolFourierFixedCarrier radius)
          (EvenBurnolFourierFixedCarrier radius)
          _ _ _ (fixedCarrierInner radius) (fixedCarrierInner radius)
          (fixedCarrierComplete radius) (fixedCarrierComplete radius)
          (evenBurnolFourierFixedCompression radius shift) left right
    _ = inner ℂ left
        (evenBurnolFourierFixedCompression radius shift right) :=
      evenBurnolFourierFixedCompression_symmetric radius shift left right

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
