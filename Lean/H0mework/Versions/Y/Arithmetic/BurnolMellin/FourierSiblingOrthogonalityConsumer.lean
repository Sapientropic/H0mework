import H0mework.Versions.Y.Arithmetic.BurnolMellin.HomogeneousFourierMellin
import H0mework.Versions.Y.Arithmetic.BurnolMellin.FourierSiblingComplementZero
import H0mework.Versions.Y.Arithmetic.BurnolMellin.CompletedMellinOrthogonalityBoundary

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex

noncomputable section

/-- A zeta zero annihilates every actual ordinary-Fourier sibling in the
compact-annulus source family.  The Gamma factor is removed only through its
strict positive-real-part nonvanishing theorem. -/
theorem riemannZeta_zero_burnolFourierSibling_completedEvaluator
    (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0)
    (source : burnolCompactAnnulusSource) :
    burnolCompletedMellinEvaluator coordinate
        (evenFaceFourierEquiv burnolUnscaledCommonGapRadius
          (burnolCompactAdditivePhysicalState source)) = 0 := by
  have homogeneous := burnolCompactAdditiveFourierHomogeneousIdentity
    source coordinate
  have complementZero := burnolCompactAdditiveMellinRead_one_sub_eq_zero
    source coordinate zero
  rw [complementZero, mul_zero] at homogeneous
  have gammaNonzero : Gammaℝ coordinate.value ≠ 0 :=
    Gammaℝ_ne_zero_of_re_pos
      (lt_trans (by norm_num) coordinate.rightHalf)
  exact (mul_eq_zero.mp homogeneous).resolve_left gammaNonzero

/-- Direct `P_a` consumer: after both source generators and their ordinary
Fourier siblings are annihilated, the completed-Mellin Riesz vector lies in
the orthogonal complement of the full Fourier-stable closed range. -/
theorem riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal
    (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    burnolCompletedMellinRieszVector coordinate ∈
      Submodule.orthogonal burnolCompactCoPoissonClosedRange.toSubmodule := by
  apply (burnolCompletedMellinRieszVector_mem_closedRange_orthogonal_iff
    coordinate zero).2
  intro source
  exact riemannZeta_zero_burnolFourierSibling_completedEvaluator
    coordinate zero source

end

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
