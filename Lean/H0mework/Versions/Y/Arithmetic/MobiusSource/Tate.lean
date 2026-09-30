import H0mework.Versions.Y.Arithmetic.MellinTateSource.Isometry
import H0mework.Versions.Y.Arithmetic.MobiusSource.WindowClosedRange

/-! The complete original Pa face has one extracted source; its Fourier face is the actual Tate reciprocal. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set
open scoped InnerProductSpace ENNReal
noncomputable section
local notation "Ambient" => EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius
local notation "q" => (1 / 4 : ℝ)

/-- The same finite Möbius extraction, now regarded as a full-line `L²`
source rather than as an independently chosen representative. -/
def burnolMobiusSourceL2 : Ambient →L[ℂ] BurnolL2 :=
  (burnolRadiusZeroExtension 4).comp burnolMobiusWindowSourceRead

private theorem tateReciprocal_compactGenerator
    (source : burnolCompactAnnulusSource) :
    burnolTateReciprocalL2
        (burnolMobiusSourceL2 (burnolCompactAdditivePhysicalState source)) =
      burnolMobiusSourceL2
        (evenFaceFourierEquiv burnolUnscaledCommonGapRadius
          (burnolCompactAdditivePhysicalState source)) := by
  let reciprocal := burnolCompactTateReciprocalSource source
  have sourceRead :
      (burnolMobiusSourceL2 (burnolCompactAdditivePhysicalState source) :
        ℝ → ℂ) =ᵐ[volume] reciprocal.1 := by
    have generated := burnolMobiusSourceExtension_compact_coeFn source
    filter_upwards [generated] with x hx
    exact hx.trans (burnolCompactTateReciprocalSchwartz_apply source x).symm
  have pulled := burnolTateReciprocalRaw_ae_congr
    (Lp.memLp (burnolMobiusSourceL2
      (burnolCompactAdditivePhysicalState source)))
    (reciprocal.1.memLp 2 (volume : Measure ℝ)) sourceRead
  have fourierState :
      evenFaceFourierEquiv burnolUnscaledCommonGapRadius
          (burnolCompactAdditivePhysicalState source) =
        burnolCompactAdditivePhysicalState reciprocal := by
    apply Subtype.ext
    exact burnolCompactFourierL2_eq_reciprocalL2 source
  have targetRead :
      (burnolMobiusSourceL2
          (evenFaceFourierEquiv burnolUnscaledCommonGapRadius
            (burnolCompactAdditivePhysicalState source)) : ℝ → ℂ) =ᵐ[volume]
        source.1 := by
    rw [fourierState]
    simpa only [burnolMobiusSourceL2, ContinuousLinearMap.comp_apply,
      reciprocal, funext (burnolCompactTateReciprocalSource_additiveSource source)] using
      burnolMobiusSourceExtension_compact_coeFn reciprocal
  apply Lp.ext
  filter_upwards [burnolTateReciprocalL2_coeFn
      (burnolMobiusSourceL2 (burnolCompactAdditivePhysicalState source)),
    pulled, targetRead] with x htate hpulled htarget
  rw [htate, hpulled, htarget]
  rw [← burnolCompactTateReciprocalSource_additiveSource source x]
  by_cases hx : x = 0
  · simp [burnolTateReciprocalRaw, burnolCompactAdditiveSource, hx]
  · simp [burnolTateReciprocalRaw, burnolCompactAdditiveSource,
      reciprocal, hx]

/-- Fourier on the entire original Pa face is the actual Tate reciprocal
of its single extracted source. No shifted range membership is supplied. -/
theorem burnolMobiusSource_fourier (value : Ambient)
    (inPa : value ∈ burnolCompactCoPoissonClosedRange) :
    burnolMobiusSourceL2 (evenFaceFourierEquiv burnolUnscaledCommonGapRadius value) =
      burnolTateReciprocalL2 (burnolMobiusSourceL2 value) := by
  let left := burnolTateReciprocalL2.comp burnolMobiusSourceL2
  let right := burnolMobiusSourceL2.comp
    (evenFaceFourierEquiv burnolUnscaledCommonGapRadius).toContinuousLinearEquiv.toContinuousLinearMap
  let equation := (left - right).ker
  have generatorEq (index : BurnolCompactCoPoissonGeneratorIndex) :
      left (burnolCompactCoPoissonGenerator index) =
        right (burnolCompactCoPoissonGenerator index) := by
    rcases index with ⟨source, parity⟩
    fin_cases parity
    · exact tateReciprocal_compactGenerator source
    · change burnolTateReciprocalL2
        (burnolMobiusSourceL2
          (evenFaceFourierEquiv burnolUnscaledCommonGapRadius
            (burnolCompactAdditivePhysicalState source))) =
        burnolMobiusSourceL2
          (evenFaceFourierEquiv burnolUnscaledCommonGapRadius
            (evenFaceFourierEquiv burnolUnscaledCommonGapRadius
              (burnolCompactAdditivePhysicalState source)))
      rw [← tateReciprocal_compactGenerator source,
        burnolTateReciprocalL2_involutive]
      exact (congrArg burnolMobiusSourceL2
        (evenFaceFourier_involutive burnolUnscaledCommonGapRadius
          (burnolCompactAdditivePhysicalState source))).symm
  have sourceEq (input : BurnolCompactCoPoissonLinearSource) :
      left (burnolCompactCoPoissonLanding input) =
        right (burnolCompactCoPoissonLanding input) := by
    induction input using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | single index coefficient =>
        rw [burnolCompactCoPoissonLanding_single, map_smul, map_smul, generatorEq]
  have rangeLe : LinearMap.range burnolCompactCoPoissonLanding ≤ equation := by
    rintro _ ⟨input, rfl⟩
    change left (burnolCompactCoPoissonLanding input) -
      right (burnolCompactCoPoissonLanding input) = 0
    rw [sourceEq, sub_self]
  have closed : IsClosed (equation : Set Ambient) := by
    change IsClosed {input : Ambient | left input - right input = 0}
    exact isClosed_eq (left.continuous.sub right.continuous) continuous_const
  have closedLe := (LinearMap.range burnolCompactCoPoissonLanding).topologicalClosure_minimal
    rangeLe closed
  have actual := closedLe inPa
  change left value - right value = 0 at actual
  exact (sub_eq_zero.mp actual).symm

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
