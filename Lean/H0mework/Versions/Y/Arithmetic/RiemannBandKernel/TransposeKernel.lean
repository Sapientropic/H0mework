import H0mework.Versions.Y.Arithmetic.RiemannBandKernel.Sampling
import H0mework.Versions.Y.Arithmetic.RiemannBandKernel.TransposeCompact

/-! The generated annular kernel reads the complete original Pa source, not only its compact generators. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex Filter FourierTransform MeasureTheory Set
open scoped ENNReal InnerProductSpace SchwartzMap Topology
noncomputable section

def burnolPaSamplingKernel (value : BurnolL2) : BurnolL2 :=
  ∑' n : ℕ, burnolAnnulusSamplingL2 value n

private theorem compactSource_annulus (source : burnolCompactAnnulusSource) {x : ℝ}
    (outside : x ∉ burnolSamplingAnnulus) : burnolCompactAdditiveSource source x = 0 := by
  have same : (burnolCompactTateReciprocalSource source).1 x =
      burnolCompactAdditiveSource source x := burnolCompactTateReciprocalSchwartz_apply source x
  rw [← same]
  by_cases inner : |x| ≤ (1 / 4 : ℝ)
  · exact (burnolCompactTateReciprocalSource source).2.2.1 x inner
  · exact (burnolCompactTateReciprocalSource source).2.2.2 x (by
      by_contra below
      exact outside ⟨lt_of_not_ge inner, (lt_of_not_ge below).le⟩)

private theorem samplingTerm_inner (value : BurnolL2) (source : burnolCompactAnnulusSource) (n : ℕ) :
    inner ℂ (burnolAnnulusSamplingL2 value n)
      (burnolMobiusSourceL2 (burnolCompactAdditivePhysicalState source)) =
        ∫ x : ℝ, star (value ((n + 1 : ℕ) * x)) * burnolCompactAdditiveSource source x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [burnolAnnulusSamplingL2_coeFn value n,
    burnolMobiusSourceExtension_compact_coeFn source] with x sampleAt sourceAt
  change (burnolMobiusSourceL2 (burnolCompactAdditivePhysicalState source)) x =
    burnolCompactAdditiveSource source x at sourceAt
  rw [sampleAt, sourceAt]
  simp only [RCLike.inner_apply, burnolAnnulusSamplingRaw]
  by_cases inside : x ∈ burnolSamplingAnnulus
  · rw [Set.indicator_of_mem inside]
    simp only [Nat.cast_add, Nat.cast_one, Complex.star_def]
    ring
  · rw [Set.indicator_of_notMem inside, compactSource_annulus source inside]
    simp

theorem burnolPaSamplingKernel_compact_inner (value : BurnolL2)
    (moment : MemLp (fun x : ℝ => (x : ℂ) * value x) 2 volume)
    (source : burnolCompactAnnulusSource) :
    inner ℂ (burnolPaSamplingKernel value)
      (burnolMobiusSourceL2 (burnolCompactAdditivePhysicalState source)) =
        ∑' n : ℕ, ∫ x : ℝ, star (value ((n + 1 : ℕ) * x)) *
          burnolCompactAdditiveSource source x := by
  have sourceRead := (innerSLFlip ℂ
    (burnolMobiusSourceL2 (burnolCompactAdditivePhysicalState source))).map_tsum
      (burnolAnnulusSamplingL2_summable value moment)
  change inner ℂ (burnolPaSamplingKernel value)
    (burnolMobiusSourceL2 (burnolCompactAdditivePhysicalState source)) =
    ∑' n : ℕ, inner ℂ (burnolAnnulusSamplingL2 value n)
      (burnolMobiusSourceL2 (burnolCompactAdditivePhysicalState source)) at sourceRead
  rw [sourceRead]
  exact tsum_congr (samplingTerm_inner value source)

theorem burnolPaSamplingKernel_compact (value : BurnolL2) (integrable : Integrable value)
    (moment : MemLp (fun x : ℝ => (x : ℂ) * value x) 2 volume)
    (source : burnolCompactAnnulusSource) :
    inner ℂ value (burnolCompactAdditiveL2 source) =
      inner ℂ (burnolPaSamplingKernel value)
        (burnolMobiusSourceL2 (burnolCompactAdditivePhysicalState source)) +
      burnolConstantGapCoefficient burnolUnscaledCommonGapRadius
        (burnolCompactAdditivePhysicalState source) * star (∫ x : ℝ, value x) := by
  rw [burnolPaSamplingKernel_compact_inner value moment source, burnolCompactSource_inner_transpose value integrable source,
    burnolCompactGapCoefficient,
    burnolCompactAdditiveCoSum_eq_neg_normalization_of_abs_le_quarter source (by norm_num)]
  ring

theorem burnolPaSamplingKernel_fullPa (value : BurnolL2) (integrable : Integrable value)
    (moment : MemLp (fun x : ℝ => (x : ℂ) * value x) 2 volume)
    (p : BurnolPaAmbientCarrier) (inPa : p ∈ burnolCompactCoPoissonClosedRange) :
    inner ℂ value (p : BurnolL2) =
      inner ℂ (burnolPaSamplingKernel value) (burnolMobiusSourceL2 p) +
        burnolConstantGapCoefficient burnolUnscaledCommonGapRadius p *
          star (∫ x : ℝ, value x) := by
  let left : BurnolPaAmbientCarrier →L[ℂ] ℂ :=
    (innerSL ℂ value).comp
      (Submodule.subtypeL (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule)
  let right : BurnolPaAmbientCarrier →L[ℂ] ℂ :=
    (innerSL ℂ (burnolPaSamplingKernel value)).comp burnolMobiusSourceL2 +
      star (∫ x : ℝ, value x) • burnolConstantGapCoefficient burnolUnscaledCommonGapRadius
  let equation := (left - right).ker
  have compactEq (source : burnolCompactAnnulusSource) :
      left (burnolCompactAdditivePhysicalState source) =
        right (burnolCompactAdditivePhysicalState source) := by
    change inner ℂ value (burnolCompactAdditiveL2 source) =
      inner ℂ (burnolPaSamplingKernel value) (burnolMobiusSourceL2 (burnolCompactAdditivePhysicalState source)) +
        star (∫ x : ℝ, value x) *
          burnolConstantGapCoefficient burnolUnscaledCommonGapRadius (burnolCompactAdditivePhysicalState source)
    rw [burnolPaSamplingKernel_compact value integrable moment source]
    ring
  have generatorEq (index : BurnolCompactCoPoissonGeneratorIndex) :
      left (burnolCompactCoPoissonGenerator index) = right (burnolCompactCoPoissonGenerator index) := by
    rcases index with ⟨source, parity⟩
    fin_cases parity
    · exact compactEq source
    · have same : burnolCompactCoPoissonGenerator (source, (1 : Fin 2)) =
          burnolCompactAdditivePhysicalState (burnolCompactTateReciprocalSource source) := by
        apply Subtype.ext
        exact burnolCompactFourierL2_eq_reciprocalL2 source
      change left (burnolCompactCoPoissonGenerator (source, (1 : Fin 2))) =
        right (burnolCompactCoPoissonGenerator (source, (1 : Fin 2)))
      rw [same]
      exact compactEq (burnolCompactTateReciprocalSource source)
  have sourceEq (input : BurnolCompactCoPoissonLinearSource) :
      left (burnolCompactCoPoissonLanding input) = right (burnolCompactCoPoissonLanding input) := by
    induction input using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | single index coefficient =>
        rw [burnolCompactCoPoissonLanding_single, map_smul, map_smul, generatorEq]
  have rangeLe : LinearMap.range burnolCompactCoPoissonLanding ≤ equation := by
    rintro _ ⟨input, rfl⟩
    change left (burnolCompactCoPoissonLanding input) - right (burnolCompactCoPoissonLanding input) = 0
    rw [sourceEq, sub_self]
  have closed : IsClosed (equation : Set BurnolPaAmbientCarrier) := by
    change IsClosed {input | left input - right input = 0}
    exact isClosed_eq (left.continuous.sub right.continuous) continuous_const
  have actual := (LinearMap.range burnolCompactCoPoissonLanding).topologicalClosure_minimal
    rangeLe closed inPa
  change left p - right p = 0 at actual
  have answer := sub_eq_zero.mp actual
  change inner ℂ value (p : BurnolL2) =
    inner ℂ (burnolPaSamplingKernel value) (burnolMobiusSourceL2 p) +
      star (∫ x : ℝ, value x) * burnolConstantGapCoefficient burnolUnscaledCommonGapRadius p at answer
  rw [answer]
  ring

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
