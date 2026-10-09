import H0mework.Versions.V2.Arithmetic.RemainderSource.RemainderCompact
import H0mework.Versions.V2.Arithmetic.RemainderSource.RemainderAction

/-! The original whole Pa closed range directly consumes the actual source action. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set
open scoped InnerProductSpace
noncomputable section
local notation "Ambient" => EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius

private theorem l2_bilinear_symm (left right : BurnolL2) :
    inner ℂ (star left) right = inner ℂ (star right) left := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star left, Lp.coeFn_star right] with x hl hr
  rw [hl, hr]
  simp only [RCLike.inner_apply, Pi.star_apply, starRingEnd_apply, star_star]
  exact mul_comm _ _

private def l2TestRead (test : SchwartzMap ℝ ℂ) : BurnolL2 →L[ℂ] ℂ :=
  innerSL ℂ (star (test.toLp 2 volume))

private theorem l2TestRead_integral (test : SchwartzMap ℝ ℂ) (value : BurnolL2) :
    l2TestRead test value = ∫ x : ℝ, test x * value x := by
  change inner ℂ (star (test.toLp 2 volume)) value = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star (test.toLp 2 volume), test.coeFn_toLp 2 volume]
    with x hstar htest
  rw [hstar, Pi.star_apply, htest]
  simp only [RCLike.inner_apply, starRingEnd_apply, star_star]
  exact mul_comm _ _

/-- The original whole closed Pa carrier is represented by the action of
its recovered ν on the unchanged integer-comb remainder. -/
theorem burnolRemainderSourceRead_Pa (value : Ambient)
    (inPa : value ∈ burnolCompactCoPoissonClosedRange) (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead (burnolMobiusSourceL2 value) test =
      ∫ x : ℝ, test x * (value : BurnolL2) x := by
  let left := ((1 / 2 : ℂ) • innerSL ℂ (star (burnolRemainderL2Kernel test))).comp
    burnolMobiusSourceL2
  let right := (l2TestRead test).comp
    (Submodule.subtypeL (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule)
  have compactEq (source : burnolCompactAnnulusSource) :
      left (burnolCompactAdditivePhysicalState source) =
        right (burnolCompactAdditivePhysicalState source) := by
    change (1 / 2 : ℂ) * inner ℂ (star (burnolRemainderL2Kernel test))
      (burnolMobiusSourceL2 (burnolCompactAdditivePhysicalState source)) = _
    rw [l2_bilinear_symm]
    change burnolRemainderSourceRead
      (burnolMobiusSourceL2 (burnolCompactAdditivePhysicalState source)) test =
        l2TestRead test (burnolCompactAdditiveL2 source)
    rw [burnolRemainderSourceRead_compact, l2TestRead_integral]
    apply integral_congr_ae
    filter_upwards [burnolCompactAdditiveL2_coeFn source] with x hx
    rw [hx]
  have generatorEq (index : BurnolCompactCoPoissonGeneratorIndex) :
      left (burnolCompactCoPoissonGenerator index) =
        right (burnolCompactCoPoissonGenerator index) := by
    rcases index with ⟨source, parity⟩
    fin_cases parity
    · exact compactEq source
    · have sameSource : burnolCompactCoPoissonGenerator (source, (1 : Fin 2)) =
          burnolCompactAdditivePhysicalState (burnolCompactTateReciprocalSource source) := by
        apply Subtype.ext
        exact burnolCompactFourierL2_eq_reciprocalL2 source
      change left (burnolCompactCoPoissonGenerator (source, (1 : Fin 2))) =
        right (burnolCompactCoPoissonGenerator (source, (1 : Fin 2)))
      rw [sameSource]
      exact compactEq (burnolCompactTateReciprocalSource source)
  have sourceEq (input : BurnolCompactCoPoissonLinearSource) :
      left (burnolCompactCoPoissonLanding input) =
        right (burnolCompactCoPoissonLanding input) := by
    induction input using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | single index coefficient =>
        rw [burnolCompactCoPoissonLanding_single, map_smul, map_smul, generatorEq]
  let equation := (left - right).ker
  have rangeLe : LinearMap.range burnolCompactCoPoissonLanding ≤ equation := by
    rintro _ ⟨input, rfl⟩
    change left (burnolCompactCoPoissonLanding input) -
      right (burnolCompactCoPoissonLanding input) = 0
    rw [sourceEq, sub_self]
  have closed : IsClosed (equation : Set Ambient) := by
    change IsClosed {input : Ambient | left input - right input = 0}
    exact isClosed_eq (left.continuous.sub right.continuous) continuous_const
  have actual := (LinearMap.range burnolCompactCoPoissonLanding).topologicalClosure_minimal
    rangeLe closed inPa
  change left value - right value = 0 at actual
  have equality := sub_eq_zero.mp actual
  change (1 / 2 : ℂ) * inner ℂ (star (burnolRemainderL2Kernel test))
    (burnolMobiusSourceL2 value) = l2TestRead test (value : BurnolL2) at equality
  rw [l2_bilinear_symm, l2TestRead_integral] at equality
  exact equality

private theorem schwartzDilation_toLp (shift : ℝ) (test : SchwartzMap ℝ ℂ) :
    (burnolRemainderSchwartzDilation shift test).toLp 2 volume =
      burnolMultiplicativeDilation shift (test.toLp 2 volume) := by
  have qmp : Measure.QuasiMeasurePreserving (fun x : ℝ => Real.exp shift * x)
      volume volume := by
    simpa only [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
        (r := Real.exp shift) (Real.exp_ne_zero shift))
  apply Lp.ext
  filter_upwards [(burnolRemainderSchwartzDilation shift test).coeFn_toLp 2 volume,
    burnolMultiplicativeDilation_coeFn shift (test.toLp 2 volume),
    qmp.ae (test.coeFn_toLp 2 volume)] with x hleft hright htest
  rw [hleft, hright]
  unfold burnolL2RawNormalizedDilation
  rw [htest]
  rfl

/-- The evolved source realizes the actual evolved Pa value on every
Schwartz measurement; shifted Pa membership is not an input. -/
theorem burnolRemainderSourceRead_Pa_action (shift : ℝ) (value : Ambient)
    (inPa : value ∈ burnolCompactCoPoissonClosedRange) (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead (burnolMultiplicativeDilation shift
        (burnolMobiusSourceL2 value)) test =
      ∫ x : ℝ, test x * burnolMultiplicativeDilation shift (value : BurnolL2) x := by
  rw [burnolRemainderSourceRead_dilation]
  calc
    _ = l2TestRead (burnolRemainderSchwartzDilation (-shift) test) (value : BurnolL2) := by
      rw [l2TestRead_integral]
      exact burnolRemainderSourceRead_Pa value inPa _
    _ = l2TestRead test (burnolMultiplicativeDilation shift (value : BurnolL2)) := by
      change inner ℂ (star ((burnolRemainderSchwartzDilation (-shift) test).toLp 2 volume))
        (value : BurnolL2) = _
      rw [schwartzDilation_toLp, burnolMultiplicativeDilation_star,
        (burnolMultiplicativeDilation (-shift)).inner_map_eq_flip,
        ← burnolMultiplicativeDilation_neg_eq_symm (-shift), neg_neg]
      rfl
    _ = _ := l2TestRead_integral _ _

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
