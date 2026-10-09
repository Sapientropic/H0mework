import H0mework.Versions.V2.Arithmetic.RiemannNativeCurrent.WeylPairing
import H0mework.Versions.V2.Arithmetic.RiemannNativeCurrent.OriginalHead
import H0mework.Versions.V2.Arithmetic.RiemannBandResponse.Spectral

/-! The entire Laplace family of the original head coupling factors through the same extracted source. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

local instance : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

open SourceGeneratedCompressedUnitaryDefectPort

theorem burnolPaResolvent_source_laplace (probe : BurnolCompletedMellinCoordinate)
    (p : BurnolPaAmbientCarrier) (inPa : p ∈ burnolCompactCoPoissonClosedRange)
    (left : BurnolPaOrthogonalCarrier) :
    (∫ h : ℝ in Ioi 0, positiveMellinQuarterRightResolventWeight (probe.value / 2) h *
      inner ℂ (left : BurnolL2) (burnolMultiplicativeDilation (-h / 2) (p : BurnolL2))) =
    -burnolPaResolventSourceCoefficient probe p *
      inner ℂ (left : BurnolL2) (burnolUnitTailResponse probe 4) := by
  have rq : 1 / 4 < (probe.value / 2).re := by
    rw [Complex.div_re]; norm_num; linarith [probe.rightHalf]
  have response := burnolPaResolvent_source_pairing probe p inPa left
  have integral : inner ℂ (left : BurnolL2)
      (burnolDirectRightResolvent (probe.value / 2) (p : BurnolL2)) =
      -(∫ h : ℝ in Ioi 0, positiveMellinQuarterRightResolventWeight (probe.value / 2) h *
        inner ℂ (left : BurnolL2) (burnolMultiplicativeDilation (-h / 2) (p : BurnolL2))) := by
    unfold burnolDirectRightResolvent
    rw [inner_neg_right, ← integral_inner
      (burnolDirectRightResolventIntegrand_integrableOn _ rq _) (left : BurnolL2)]
    congr 1
    apply integral_congr_ae
    filter_upwards with h
    simp only [burnolDirectRightResolventIntegrand, inner_smul_right]
  rw [integral] at response
  linear_combination -response

private theorem paired_inner (h : ℝ) (left right : BurnolPaAmbientCarrier) :
    inner ℂ left (burnolPairedAmbientCompression h right) =
      (1 / 2 : ℂ) * (inner ℂ (left : BurnolL2) (burnolMultiplicativeDilation h (right : BurnolL2)) +
        inner ℂ (left : BurnolL2) (burnolMultiplicativeDilation (-h) (right : BurnolL2))) := by
  change inner ℂ left ((1 / 2 : ℂ) •
    (evenBurnolMultiplicativeCompression burnolUnscaledCommonGapRadius h right +
      evenBurnolMultiplicativeCompression burnolUnscaledCommonGapRadius (-h) right)) = _
  rw [inner_smul_right (𝕜 := ℂ) (E := BurnolPaAmbientCarrier), inner_add_right]
  congr 1
  exact congrArg₂ (fun a b : ℂ => a + b)
    (compression_inner_right_readback (evenBurnolClosedFace burnolUnscaledCommonGapRadius)
      (burnolMultiplicativeDilation h).toLinearIsometry left right)
    (compression_inner_right_readback (evenBurnolClosedFace burnolUnscaledCommonGapRadius)
      (burnolMultiplicativeDilation (-h)).toLinearIsometry left right)

theorem burnolPairedAmbientCompression_inner_fixed (h : ℝ) (left right : BurnolPaAmbientCarrier)
    (leftFixed : evenFaceFourierEquiv burnolUnscaledCommonGapRadius left = left)
    (rightFixed : evenFaceFourierEquiv burnolUnscaledCommonGapRadius right = right) :
    inner ℂ left (burnolPairedAmbientCompression h right) =
      inner ℂ (left : BurnolL2) (burnolMultiplicativeDilation (-h) (right : BurnolL2)) := by
  have lf : fourierL2 (left : BurnolL2) = left := congrArg Subtype.val leftFixed
  have rf : fourierL2 (right : BurnolL2) = right := congrArg Subtype.val rightFixed
  have inverse : inner ℂ (left : BurnolL2) (burnolMultiplicativeDilation h (right : BurnolL2)) =
      inner ℂ (left : BurnolL2) (burnolMultiplicativeDilation (-h) (right : BurnolL2)) := by
    calc
      _ = inner ℂ (fourierL2 (left : BurnolL2))
        (fourierL2 (burnolMultiplicativeDilation h (right : BurnolL2))) :=
          (fourierL2.inner_map_map _ _).symm
      _ = _ := by rw [lf, fourierL2_burnolMultiplicativeDilation, rf]
  rw [paired_inner, inverse]
  ring

theorem burnolPaProjectedHead_fourier_fixed {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    let B := burnolPaCombPairedPhysicalResponse observation nontrivial rightHalf 0
    evenFaceFourierEquiv burnolUnscaledCommonGapRadius
      (burnolCompactCoPoissonClosedRange.toSubmodule.starProjection B) =
      burnolCompactCoPoissonClosedRange.toSubmodule.starProjection B := by
  let B := burnolPaCombPairedPhysicalResponse observation nontrivial rightHalf 0
  let F := evenFaceFourierEquiv burnolUnscaledCommonGapRadius
  let P := burnolCompactCoPoissonClosedRange.toSubmodule.starProjection
  let Q := burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
  have bf : F B = B := by
    have twice (value : BurnolPaAmbientCarrier) : F (F value) = value :=
      evenFaceFourier_involutive burnolUnscaledCommonGapRadius value
    unfold B burnolPaCombPairedPhysicalResponse
    rw [map_smul, map_add]
    change (1 / 2 : ℂ) • (F _ + F (F _)) = _
    rw [twice]
    congr 1
    exact add_comm _ _
  have qf := congrArg (fun value : SourceGeneratedHilbertCokernel.OrthogonalResidual
      burnolCompactCoPoissonLanding => (value : BurnolPaAmbientCarrier))
    (burnolCompactCoPoissonActionSquare.orthogonalAction_residual B)
  change F (Q B) = Q (F B) at qf
  rw [bf] at qf
  have split : P B = B - Q B := by
    change P B = B - burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection B
    rw [Submodule.starProjection_orthogonal_val]
    abel
  change F (P B) = P B
  rw [split, map_sub, bf, qf]

theorem burnolPaHeadCoupling_laplace_source {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (probe : BurnolCompletedMellinCoordinate) :
    let B := burnolPaCombPairedPhysicalResponse observation nontrivial rightHalf 0
    let p := burnolCompactCoPoissonClosedRange.toSubmodule.starProjection B
    let Z : BurnolPaOrthogonalCarrier := burnolZeroOwnedUnitFourierPaState observation nontrivial rightHalf
    (∫ h : ℝ in Ioi 0, positiveMellinQuarterRightResolventWeight (probe.value / 2) h *
      inner ℂ (Z : BurnolPaAmbientCarrier) (burnolPairedAmbientCompression (h / 2) p)) =
    -burnolPaResolventSourceCoefficient probe p *
      inner ℂ (Z : BurnolL2) (burnolUnitTailResponse probe 4) := by
  dsimp only
  rw [← burnolPaResolvent_source_laplace probe _ (Submodule.starProjection_apply_mem _ _)]
  apply integral_congr_ae
  filter_upwards with h
  congr 1
  rw [burnolPairedAmbientCompression_inner_fixed _ _ _
    (burnolZeroOwnedUnitFourierPaState_fixed observation nontrivial rightHalf)
    (burnolPaProjectedHead_fourier_fixed observation nontrivial rightHalf)]
  rw [neg_div]

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
