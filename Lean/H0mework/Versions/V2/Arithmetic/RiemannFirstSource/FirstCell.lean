import H0mework.Versions.V2.Arithmetic.MobiusSource.ActionProjection
import H0mework.Versions.V2.Arithmetic.RiemannFirstSource.ThetaPairing
import H0mework.Versions.V2.Arithmetic.RiemannFirstSource.SignedOrbit

/-! The exact-order Pa projection consumes its two actual source fields in the original signed-boundary equation. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann

open Complex MeasureTheory Set
open ClozelGeneralizedDual
open ClozelGeneralizedDual.BurnolPhysicalState
open scoped InnerProductSpace Topology
noncomputable section

local notation "Ambient" => EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius

local instance firstCellActionAmbientComplete : CompleteSpace Ambient := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

/-- The signed boundary integral is now read on the actual `P_a` projection
through the two source-generated first-cell corrections.  The only action
transfer used here is the signed orbit of the same normalized compact
source; no stability premise for arbitrary `P_a` values is supplied. -/
theorem burnolAnalyticComplementExactOrder_pairedBoundary_firstCellSourceRead
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re)
    (shift : ℝ) (nonnegative : 0 ≤ shift)
    (bounded : shift ≤ Real.log (16 / 9 : ℝ)) :
    let z := observation.coordinate / 2
    let sourceValue := burnolAnalyticComplementCompletionSource
      observation nontrivial
    let predecessor :=
      generatedRiemannXiZeroOrder owner observation.coordinate - 1
    let previous := quarterFeatureCompletionRightResolventIterate
      z predecessor sourceValue
    let state := burnolAnalyticComplementExactOrderPhysicalState
      observation nontrivial
    let projection := burnolCompactCoPoissonClosedRange.toSubmodule.starProjection state
    let source := burnolAnalyticComplementNormalizedSource observation
    let inverseBoundary : Ambient :=
      positiveMellinQuarterRightResolventCharacter z (-shift) •
        burnolSourceFeatureCompletionPhysicalMap z
          (quarterCompletionRightResolventSignedBoundary z previous (-shift))
    let forwardBoundary : Ambient :=
      positiveMellinQuarterRightResolventCharacter z shift •
        burnolSourceFeatureCompletionPhysicalMap z
          (quarterCompletionRightResolventSignedBoundary z previous shift)
    inner ℂ (burnolCompactAdditivePhysicalState source : BurnolL2)
        ((pairedBurnolMultiplicativeDilation (shift / 2) (projection : BurnolL2) -
            (1 / 2 : ℂ) •
              (burnolFirstCellCorrectionField (shift / 2) projection +
                fourierL2 (burnolFirstCellCorrectionField (shift / 2)
                  (evenFaceFourierEquiv burnolUnscaledCommonGapRadius projection)))) -
          pairedMellinTranslationCharacter observation.coordinate
            (shift / 2) • (projection : BurnolL2)) =
      ∫ x : ℝ, (1 / 2 : ℂ) *
        (inner ℂ (burnolCompactCoPoissonThetaRaw source x)
            ((inverseBoundary : BurnolL2) x) +
          inner ℂ (burnolCompactCoPoissonThetaRaw source x)
            ((forwardBoundary : BurnolL2) x)) := by
  dsimp only
  let state := burnolAnalyticComplementExactOrderPhysicalState
    observation nontrivial
  let projection := burnolCompactCoPoissonClosedRange.toSubmodule.starProjection state
  let source := burnolAnalyticComplementNormalizedSource observation
  let test := burnolCompactAdditivePhysicalState source
  let action := burnolPairedAmbientCompression (shift / 2)
  let character := pairedMellinTranslationCharacter observation.coordinate (shift / 2)
  have testMem : test ∈ burnolCompactCoPoissonClosedRange := by
    simpa only [test, source, burnolCompactCoPoissonGenerator,
      Fin.isValue, ↓reduceIte] using
      burnolCompactCoPoissonGenerator_mem_closedRange (source, (0 : Fin 2))
  have movedTestMem : action test ∈ burnolCompactCoPoissonClosedRange := by
    simpa only [action, test, source] using
      burnolAnalyticSource_pairedCompression_mem
        observation nontrivial shift nonnegative bounded
  have baseNormal : inner ℂ test projection = inner ℂ test state :=
    burnolCompactCoPoissonClosedRange.toSubmodule
      |>.inner_orthogonalProjectionOnto_eq_of_mem_left ⟨test, testMem⟩ state
  have movedNormal : inner ℂ (action test) projection =
      inner ℂ (action test) state :=
    burnolCompactCoPoissonClosedRange.toSubmodule
      |>.inner_orthogonalProjectionOnto_eq_of_mem_left
        ⟨action test, movedTestMem⟩ state
  have actionNormal : inner ℂ test (action projection) =
      inner ℂ test (action state) := by
    calc
      _ = inner ℂ (action test) projection :=
        (burnolPairedAmbientCompression_symmetric
          (shift / 2) test projection).symm
      _ = inner ℂ (action test) state := movedNormal
      _ = inner ℂ test (action state) :=
        burnolPairedAmbientCompression_symmetric (shift / 2) test state
  have characterNormal : inner ℂ test (character • projection) =
      inner ℂ test (character • state) := by
    calc
      _ = character * inner ℂ test projection :=
        inner_smul_right (𝕜 := ℂ) test projection character
      _ = character * inner ℂ test state := congrArg (character * ·) baseNormal
      _ = _ := (inner_smul_right (𝕜 := ℂ) test state character).symm
  have transferred : inner ℂ test (action projection - character • projection) =
      inner ℂ test (action state - character • state) := by
    rw [inner_sub_right, inner_sub_right, actionNormal, characterNormal]
  have logCompare : Real.log (16 / 9 : ℝ) ≤ 2 * Real.log 2 := by
    calc
      Real.log (16 / 9 : ℝ) ≤ Real.log 4 :=
        Real.log_le_log (by norm_num) (by norm_num)
      _ = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 * 2 by norm_num,
          Real.log_mul (by norm_num) (by norm_num)]
        ring
  have halfNonnegative : 0 ≤ shift / 2 := by positivity
  have halfSmall : shift / 2 ≤ Real.log 2 := by linarith
  have sourceFormula := burnolFirstCellPairedProjection_formula
    (shift / 2) halfNonnegative halfSmall projection
  have boundary :=
    burnolAnalyticComplementExactOrder_pairedSignedBoundary_concretePairing
      observation nontrivial rightHalf shift source
  rw [← sourceFormula]
  change inner ℂ test (action projection - character • projection) = _
  rw [transferred]
  simpa only [state, source, test, action, character] using boundary

end
end NoIslandNoMagic.CanonicalRiemann
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
