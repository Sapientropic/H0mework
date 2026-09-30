import H0mework.Versions.Y.Arithmetic.BurnolMellin.CompletedMellinPrimaryGenerator

/-!
# Exact Fourier-sibling boundary for the Burnol completed-Mellin vector

The primary compact-annulus generators are already annihilated at a zeta
zero.  This theorem identifies the sole additional equation needed for the
same Riesz vector to lie in the orthogonal complement of the full
Fourier-stable closed range: annihilation of the actual ordinary-`fourierL2`
siblings.  It neither assumes nor manufactures that intertwining law.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex
open scoped InnerProductSpace

noncomputable section

theorem burnolCompletedMellinRieszVector_mem_closedRange_orthogonal_iff
    (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    burnolCompletedMellinRieszVector coordinate ∈
        Submodule.orthogonal burnolCompactCoPoissonClosedRange.toSubmodule ↔
      ∀ source : burnolCompactAnnulusSource,
        burnolCompletedMellinEvaluator coordinate
          (evenFaceFourierEquiv burnolUnscaledCommonGapRadius
            (burnolCompactAdditivePhysicalState source)) = 0 := by
  constructor
  · intro orthogonal source
    have generatorMem := burnolCompactCoPoissonGenerator_mem_closedRange
      (source, 1)
    have pairing := ((Submodule.mem_orthogonal'
      burnolCompactCoPoissonClosedRange.toSubmodule
      (burnolCompletedMellinRieszVector coordinate)).mp orthogonal)
      (burnolCompactCoPoissonGenerator (source, 1)) generatorMem
    rw [burnolCompletedMellinRieszVector_readback] at pairing
    exact pairing
  · intro fourierZero
    rw [Submodule.mem_orthogonal']
    intro value membership
    rw [burnolCompletedMellinRieszVector_readback]
    have rangeLe : LinearMap.range burnolCompactCoPoissonLanding ≤
        (burnolCompletedMellinEvaluator coordinate).ker := by
      rintro _ ⟨input, rfl⟩
      change burnolCompletedMellinEvaluator coordinate
          (burnolCompactCoPoissonLanding input) = 0
      induction input using Finsupp.induction_linear with
      | zero => simp
      | add left right leftLaw rightLaw => simp [leftLaw, rightLaw]
      | single index coefficient =>
          rw [burnolCompactCoPoissonLanding_single, map_smul]
          rcases index with ⟨source, parity⟩
          fin_cases parity
          · simp [burnolCompactCoPoissonGenerator,
              burnolCompletedMellinEvaluator_compactAdditivePhysicalState_eq_zero
                source coordinate zero]
          · simp [burnolCompactCoPoissonGenerator, fourierZero source]
    have closureLe :
        (LinearMap.range burnolCompactCoPoissonLanding).topologicalClosure ≤
          (burnolCompletedMellinEvaluator coordinate).ker :=
      Submodule.topologicalClosure_minimal
        (LinearMap.range burnolCompactCoPoissonLanding) rangeLe
        (burnolCompletedMellinEvaluator coordinate).isClosed_ker
    apply closureLe
    exact membership

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
