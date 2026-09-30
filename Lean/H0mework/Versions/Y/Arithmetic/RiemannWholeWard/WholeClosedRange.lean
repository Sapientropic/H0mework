import H0mework.Versions.Y.Arithmetic.RiemannSourceGreen.FixedClosure
import H0mework.Versions.Y.Arithmetic.RiemannWholeWard.WardFunctionals

/-! The source Ward closes on the complete original fixed Pa face and reads the actual head. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

local instance : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete


theorem originalPa_fixed_finite_ward {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ k : Nat, observation.coordinate = -2 * (k + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (N : ℕ)
    (p : BurnolPaAmbientCarrier) (inside : p ∈ burnolCompactCoPoissonClosedRange)
    (fixed : evenFaceFourierEquiv burnolUnscaledCommonGapRadius p = p) :
    4 * contactBilinearRead (originalFiniteContactKernel observation nontrivial rightHalf N)
      (burnolTateReciprocalL2 (burnolMobiusSourceL2 p)) =
        originalFiniteSourceWard observation nontrivial rightHalf N ⟨p, inside⟩ := by
  let source := burnolTateReciprocalL2.comp
    (burnolMobiusSourceL2.comp burnolCompactCoPoissonClosedRange.toSubmodule.subtypeL)
  let left := (4 : ℂ) •
    ((contactBilinearRead (originalFiniteContactKernel observation nontrivial rightHalf N)).comp source)
  exact originalPa_fixed_clm_ext left
    (originalFiniteSourceWard observation nontrivial rightHalf N)
    (fun g hg => originalFiniteSourceWard_compact observation nontrivial rightHalf N g _ hg)
    p inside fixed

theorem original_head_finite_source_ward {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ k : Nat, observation.coordinate = -2 * (k + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (N : ℕ) :
    let B := burnolPaCombPairedPhysicalResponse observation nontrivial rightHalf 0
    let p := burnolCompactCoPoissonClosedRange.toSubmodule.starProjection B
    4 * contactBilinearRead (originalFiniteContactKernel observation nontrivial rightHalf N)
      (burnolTateReciprocalL2 (burnolMobiusSourceL2 p)) =
        originalFiniteSourceWard observation nontrivial rightHalf N
          ⟨p, Submodule.starProjection_apply_mem _ _⟩ :=
  originalPa_fixed_finite_ward observation nontrivial rightHalf N _
    (Submodule.starProjection_apply_mem _ _)
    (burnolPaProjectedHead_fourier_fixed observation nontrivial rightHalf)

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
