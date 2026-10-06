import Mathlib.Analysis.InnerProductSpace.Adjoint
import H0mework.Arithmetic.MuntzAction.CoPoissonMuntzGraphCokernelDilationNaturality
import H0mework.Arithmetic.RiemannGraph.ZeroRieszGraphOrthogonalState

/-!
# Zero-owned raw dilation adjoint eigenlaw

The already descended normalized relation action reconstructs the literal raw
dilation on the same graph cokernel.  Actual zero annihilation makes its
canonical quotient Riesz state, and then its relation-orthogonal
representative, an adjoint eigenvector with the exact quarter character.
This is not yet a contractive Sonine compression.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual

open SourceGeneratedFunctionalGraphCokernel
open SourceGeneratedHilbertCokernel
open SourceGeneratedFunctionalGraphPerfectification
open scoped InnerProductSpace

noncomputable section

/-- The literal (unnormalized) dilation on the generated relation quotient.
It is reconstructed from the already descended normalized action and its
source-generated character. -/
def rawCoPoissonMuntzGraphCokernelDilationAction
    (z : ℂ) (positiveZ : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (scale : ℝ) (positive : 0 < scale) :
    CoPoissonMuntzGraphCokernel z positiveZ belowHalf →L[ℂ]
      CoPoissonMuntzGraphCokernel z positiveZ belowHalf :=
  quarterDilationCharacter z scale •
    coPoissonMuntzGraphCokernelDilationAction
      z positiveZ belowHalf scale positive

@[simp] theorem rawCoPoissonMuntzGraphCokernelDilationAction_source
    (z : ℂ) (positiveZ : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (scale : ℝ) (positive : 0 < scale) (value : QuarterMellinL2Test z) :
    rawCoPoissonMuntzGraphCokernelDilationAction
        z positiveZ belowHalf scale positive
        (coPoissonMuntzGraphSourceMap z positiveZ belowHalf value) =
      coPoissonMuntzGraphSourceMap z positiveZ belowHalf
        (quarterDilationTestAction z scale positive value) := by
  rw [rawCoPoissonMuntzGraphCokernelDilationAction,
    smul_apply,
    coPoissonMuntzGraphCokernelDilationAction_source]
  change quarterDilationCharacter z scale •
      coPoissonMuntzGraphSourceMap z positiveZ belowHalf
        ((quarterDilationCharacter z scale)⁻¹ •
          quarterDilationTestAction z scale positive value) = _
  rw [map_smul, smul_smul,
    mul_inv_cancel₀ (quarterDilationCharacter_ne_zero z scale positive), one_smul]

theorem rawCoPoissonMuntzGraphCokernelDilationAction_functional_eigenlaw
    (z : ℂ) (positiveZ : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (annihilates :
      (quarterMellinL2Functional z).comp
        (coPoissonQuarterMellinConvergentMap z positiveZ belowHalf) = 0)
    (scale : ℝ) (positive : 0 < scale)
    (quotient : CoPoissonMuntzGraphCokernel z positiveZ belowHalf) :
    descendedFunctional
        (quarterMellinL2Feature z) (quarterMellinL2Functional z)
        (coPoissonQuarterMellinConvergentMap z positiveZ belowHalf) annihilates
        (rawCoPoissonMuntzGraphCokernelDilationAction
          z positiveZ belowHalf scale positive quotient) =
      quarterDilationCharacter z scale *
        descendedFunctional
          (quarterMellinL2Feature z) (quarterMellinL2Functional z)
          (coPoissonQuarterMellinConvergentMap z positiveZ belowHalf) annihilates
          quotient := by
  rw [rawCoPoissonMuntzGraphCokernelDilationAction,
    smul_apply, map_smul]
  congr 1
  exact (normalizedQuarterDilationRelationMorphism
    z positiveZ belowHalf scale positive).descendedFunctional_quotientMap
      annihilates annihilates quotient

theorem rawCoPoissonMuntzGraphCokernelDilationAction_adjoint_riesz_eigenlaw
    (z : ℂ) (positiveZ : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (annihilates :
      (quarterMellinL2Functional z).comp
        (coPoissonQuarterMellinConvergentMap z positiveZ belowHalf) = 0)
    (scale : ℝ) (positive : 0 < scale) :
    (rawCoPoissonMuntzGraphCokernelDilationAction
        z positiveZ belowHalf scale positive).adjoint
        (descendedRieszVector
          (quarterMellinL2Feature z) (quarterMellinL2Functional z)
          (coPoissonQuarterMellinConvergentMap z positiveZ belowHalf)
          annihilates) =
      star (quarterDilationCharacter z scale) •
        descendedRieszVector
          (quarterMellinL2Feature z) (quarterMellinL2Functional z)
          (coPoissonQuarterMellinConvergentMap z positiveZ belowHalf)
          annihilates := by
  apply ext_inner_right ℂ
  intro quotient
  rw [ContinuousLinearMap.adjoint_inner_left,
    descendedRieszVector_inner,
    rawCoPoissonMuntzGraphCokernelDilationAction_functional_eigenlaw,
    inner_smul_left]
  simp only [starRingEnd_apply, star_star, descendedRieszVector_inner]

/-- The actual relation-orthogonal compression obtained by transporting the
raw quotient action across the canonical quotient/orthogonal isometry.  This
is a genuine orthogonal compression, but its ambient graph action is not yet
the support-restricted Sonine unitary required for contractivity. -/
def rawCoPoissonMuntzRelationOrthogonalCompression
    (z : ℂ) (positiveZ : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (scale : ℝ) (positive : 0 < scale) :
    OrthogonalResidual
        (relationGraphMap
          (quarterMellinL2Feature z) (quarterMellinL2Functional z)
          (coPoissonQuarterMellinConvergentMap z positiveZ belowHalf)) →L[ℂ]
      OrthogonalResidual
        (relationGraphMap
          (quarterMellinL2Feature z) (quarterMellinL2Functional z)
          (coPoissonQuarterMellinConvergentMap z positiveZ belowHalf)) :=
  let relation := coPoissonQuarterMellinConvergentMap z positiveZ belowHalf
  let equivalence := quotientOrthogonalEquiv
    (relationGraphMap
      (quarterMellinL2Feature z) (quarterMellinL2Functional z) relation)
  equivalence.toContinuousLinearEquiv.toContinuousLinearMap.comp <|
    (rawCoPoissonMuntzGraphCokernelDilationAction
      z positiveZ belowHalf scale positive).comp
      equivalence.symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem rawCoPoissonMuntzRelationOrthogonalCompression_adjoint_riesz_eigenlaw
    (z : ℂ) (positiveZ : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (annihilates :
      (quarterMellinL2Functional z).comp
        (coPoissonQuarterMellinConvergentMap z positiveZ belowHalf) = 0)
    (scale : ℝ) (positive : 0 < scale) :
    let relation := coPoissonQuarterMellinConvergentMap z positiveZ belowHalf
    let relationMap := relationGraphMap
      (quarterMellinL2Feature z) (quarterMellinL2Functional z) relation
    let quotientState := descendedRieszVector
      (quarterMellinL2Feature z) (quarterMellinL2Functional z)
      relation annihilates
    let orthogonalState := quotientOrthogonalEquiv relationMap quotientState
    ContinuousLinearMap.adjoint (𝕜 := ℂ)
        (rawCoPoissonMuntzRelationOrthogonalCompression
          z positiveZ belowHalf scale positive) orthogonalState =
      star (quarterDilationCharacter z scale) • orthogonalState := by
  dsimp only
  let relation := coPoissonQuarterMellinConvergentMap z positiveZ belowHalf
  let relationMap := relationGraphMap
    (quarterMellinL2Feature z) (quarterMellinL2Functional z) relation
  let quotientState := descendedRieszVector
    (quarterMellinL2Feature z) (quarterMellinL2Functional z)
    relation annihilates
  let equivalence := quotientOrthogonalEquiv relationMap
  let relationSubmodule := (closedRange relationMap).toSubmodule
  apply ext_inner_right ℂ
  intro orthogonalValue
  rw [ContinuousLinearMap.adjoint_inner_left]
  change inner ℂ (equivalence quotientState)
      (equivalence
        (rawCoPoissonMuntzGraphCokernelDilationAction
          z positiveZ belowHalf scale positive
          (equivalence.symm orthogonalValue))) =
    inner ℂ (star (quarterDilationCharacter z scale) •
      equivalence quotientState) orthogonalValue
  have quotientEigen :=
    rawCoPoissonMuntzGraphCokernelDilationAction_adjoint_riesz_eigenlaw
      z positiveZ belowHalf annihilates scale positive
  calc
    _ = inner ℂ quotientState
        (rawCoPoissonMuntzGraphCokernelDilationAction
          z positiveZ belowHalf scale positive
          (equivalence.symm orthogonalValue)) := by
      exact (Submodule.inner_quotient_eq relationSubmodule quotientState
        (rawCoPoissonMuntzGraphCokernelDilationAction
          z positiveZ belowHalf scale positive
          (equivalence.symm orthogonalValue))).symm
    _ = inner ℂ
        ((rawCoPoissonMuntzGraphCokernelDilationAction
          z positiveZ belowHalf scale positive).adjoint quotientState)
        (equivalence.symm orthogonalValue) := by
      rw [ContinuousLinearMap.adjoint_inner_left]
    _ = inner ℂ
        (star (quarterDilationCharacter z scale) • quotientState)
        (equivalence.symm orthogonalValue) := by rw [quotientEigen]
    _ = inner ℂ
        (equivalence
          (star (quarterDilationCharacter z scale) • quotientState))
        (equivalence (equivalence.symm orthogonalValue)) := by
      exact Submodule.inner_quotient_eq relationSubmodule
        (star (quarterDilationCharacter z scale) • quotientState)
        (equivalence.symm orthogonalValue)
    _ = _ := by
      rw [equivalence.map_smul, equivalence.apply_symm_apply]

namespace CenteredGram

theorem selectedRawRelationOrthogonalCompression_adjoint_eigenlaw
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : ℝ) (positive : 0 < scale) :
    ContinuousLinearMap.adjoint (𝕜 := ℂ)
      (rawCoPoissonMuntzRelationOrthogonalCompression
        (selectedCoPoissonMuntzParameter observation)
        (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
        (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial)
        scale positive)
        (selectedRieszOrthogonalRepresentative observation nontrivial) =
      star (quarterDilationCharacter
        (selectedCoPoissonMuntzParameter observation) scale) •
        selectedRieszOrthogonalRepresentative observation nontrivial := by
  exact rawCoPoissonMuntzRelationOrthogonalCompression_adjoint_riesz_eigenlaw
    (selectedCoPoissonMuntzParameter observation)
    (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
    (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial)
    (selectedZero_quarterMellinL2Functional_comp_coPoissonQuarterMellinConvergentMap_eq_zero
      observation nontrivial)
    scale positive

theorem reversalRawRelationOrthogonalCompression_adjoint_eigenlaw
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : ℝ) (positive : 0 < scale) :
    ContinuousLinearMap.adjoint (𝕜 := ℂ)
      (rawCoPoissonMuntzRelationOrthogonalCompression
        (reversalCoPoissonMuntzParameter observation)
        (reversalCoPoissonMuntzParameter_re_pos observation nontrivial)
        (reversalCoPoissonMuntzParameter_re_lt_half observation nontrivial)
        scale positive)
        (reversalRieszOrthogonalRepresentative observation nontrivial) =
      star (quarterDilationCharacter
        (reversalCoPoissonMuntzParameter observation) scale) •
        reversalRieszOrthogonalRepresentative observation nontrivial := by
  exact rawCoPoissonMuntzRelationOrthogonalCompression_adjoint_riesz_eigenlaw
    (reversalCoPoissonMuntzParameter observation)
    (reversalCoPoissonMuntzParameter_re_pos observation nontrivial)
    (reversalCoPoissonMuntzParameter_re_lt_half observation nontrivial)
    (reversalZero_quarterMellinL2Functional_comp_coPoissonQuarterMellinConvergentMap_eq_zero
      observation nontrivial)
    scale positive

end CenteredGram

end

end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

