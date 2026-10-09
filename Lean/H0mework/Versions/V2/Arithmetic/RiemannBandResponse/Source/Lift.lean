import H0mework.Versions.V2.Arithmetic.RiemannBandResponse.Class
import H0mework.Arithmetic.MellinTateSource.FourierRead
import Mathlib.Topology.MetricSpace.Completion

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CombSource
open Complex MeasureTheory Set Filter
open NoIslandNoMagic.CanonicalRiemann
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open SourceGeneratedComplexFeaturePerfectification
open scoped InnerProductSpace Topology
noncomputable section

/-- The already existing completion map remains isometric. -/
theorem completion_isometry (z : ℂ) :
    Isometry (quarterMellinFeatureCompletionEvenAdditive z) := by
  change Isometry (UniformSpace.Completion.extension
    (quarterMellinFeatureRangeEvenAdditiveIsometry z))
  exact (quarterMellinFeatureRangeEvenAdditiveIsometry z).isometry.completion_extension

/-- Tate transports the actual Fourier-smoothed backing source through the
original compiler, with its original comb coefficient. -/
theorem smoothed_comb_mem_range (pulse : ContDiffBump (0 : ℝ)) (n : Nat)
    (innerMargin : (1 / 4 : ℝ) ≤
      Real.exp (-Real.log (1 + burnolPaCombSourceWidth n) - pulse.rOut))
    (outerMargin : Real.exp (-Real.log 1 + pulse.rOut) ≤ 4)
    (z : ℂ) (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ)) :
    ((n : ℂ) + 2) • fourierL2
      (burnolReciprocalStepSmoothedValue pulse
        (burnolReciprocalStepWaveL2 1 (1 + burnolPaCombSourceWidth n)
          (by norm_num) (by linarith [(burnolPaCombSourceWidth_bounds n).1]))) ∈
      Set.range (quarterMellinFeatureCompletionEvenAdditive z) := by
  let smooth := burnolReciprocalStepAnnulusSmoothedSource pulse 1
    (1 + burnolPaCombSourceWidth n) innerMargin outerMargin
  let source := burnolCompactTateReciprocalSource
    (burnolCompactTateReciprocalSource smooth)
  let value := burnolSourceQuarterCompletionValue source z positive belowHalf
  have compiled : quarterMellinFeatureCompletionEvenAdditive z value =
      (2 : ℂ) • (burnolCompactAdditivePhysicalState source : BurnolL2) := by
    unfold value burnolSourceQuarterCompletionValue burnolSourceQuarterRelation
    rw [quarterMellinFeatureCompletionEvenAdditive_source,
      compactQuarterMellinAdditiveEvenRechart_eq]
    rfl
  refine ⟨(((n : ℂ) + 2) / 2) • value, ?_⟩
  rw [map_smul, compiled,
    burnolReciprocalStepSmoothedValue_generator pulse 1
      (1 + burnolPaCombSourceWidth n) (by norm_num)
      (by linarith [(burnolPaCombSourceWidth_bounds n).1])
      (by linarith [(burnolPaCombSourceWidth_bounds n).2]) innerMargin outerMargin]
  change (((n : ℂ) + 2) / 2) • ((2 : ℂ) • burnolCompactAdditiveL2 source) =
    ((n : ℂ) + 2) • fourierL2
      (burnolCompactAdditiveL2 (burnolCompactTateReciprocalSource smooth))
  rw [burnolCompactFourierL2_eq_reciprocalL2]
  dsimp only [source]
  module

/-- Each actual raw comb forcing is in this same completion map's range.
The receipt is generated from the backing tests' L² smoothing closure,
not from its separate Pa-membership theorem. -/
theorem actual_comb_mem_range (n : Nat) (z : ℂ)
    (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ)) :
    (burnolPaCombApproximation n : BurnolL2) ∈
      Set.range (quarterMellinFeatureCompletionEvenAdditive z) := by
  have closed : IsClosed (Set.range (quarterMellinFeatureCompletionEvenAdditive z)) :=
    (completion_isometry z).isClosedEmbedding.isClosed_range
  rw [← closed.closure_eq]
  apply Metric.mem_closure_iff.mpr
  intro ε εpos
  let upper := 1 + burnolPaCombSourceWidth n
  have ordered : 1 ≤ upper := by dsimp only [upper]; linarith [(burnolPaCombSourceWidth_bounds n).1]
  have upperPositive : 0 < upper := lt_of_lt_of_le (by norm_num) ordered
  have upperStrict : upper < 4 := by dsimp only [upper]; linarith [(burnolPaCombSourceWidth_bounds n).2]
  let wave := burnolReciprocalStepWaveL2 1 upper (by norm_num) ordered
  let coefficient : ℂ := (n : ℂ) + 2
  let tolerance := ε / (‖coefficient‖ + 1)
  have tolerancePositive : 0 < tolerance := div_pos εpos (by positivity)
  obtain ⟨δ, δpos, close⟩ := Metric.continuousAt_iff.mp
    (burnolMultiplicativeDilation_stronglyContinuous wave).continuousAt tolerance tolerancePositive
  have lowerRoom : 0 < Real.log 1 - Real.log (1 / 4 : ℝ) :=
    sub_pos.mpr (Real.log_lt_log (by norm_num) (by norm_num))
  have upperRoom : 0 < Real.log 4 - Real.log upper :=
    sub_pos.mpr (Real.log_lt_log upperPositive upperStrict)
  let room := min δ (min (Real.log 1 - Real.log (1 / 4 : ℝ))
    (Real.log 4 - Real.log upper))
  have roomPositive : 0 < room := lt_min δpos (lt_min lowerRoom upperRoom)
  let pulse : ContDiffBump (0 : ℝ) := ⟨room / 4, room / 2, by positivity, by linarith⟩
  have within : pulse.rOut ≤ room := by change room / 2 ≤ room; linarith
  have small : pulse.rOut < δ :=
    lt_of_lt_of_le (by change room / 2 < room; linarith) (min_le_left _ _)
  have hLower : pulse.rOut ≤ Real.log 1 - Real.log (1 / 4 : ℝ) :=
    within.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hUpper : pulse.rOut ≤ Real.log 4 - Real.log upper :=
    within.trans ((min_le_right _ _).trans (min_le_right _ _))
  have reciprocalLog : Real.log (1 / 4 : ℝ) = -Real.log 4 := by
    rw [one_div, Real.log_inv]
  have innerMargin : (1 / 4 : ℝ) ≤ Real.exp (-Real.log upper - pulse.rOut) := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 1 / 4), Real.exp_le_exp, reciprocalLog]
    linarith
  have outerMargin : Real.exp (-Real.log 1 + pulse.rOut) ≤ 4 := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 4), Real.exp_le_exp]
    rw [reciprocalLog] at hLower
    linarith
  let smooth := burnolReciprocalStepSmoothedValue pulse wave
  refine ⟨coefficient • fourierL2 smooth, ?_, ?_⟩
  · exact smoothed_comb_mem_range pulse n innerMargin outerMargin z positive belowHalf
  · have bound : dist smooth wave ≤ tolerance := by
      have native := pulse.dist_normed_convolution_le (μ := (volume : Measure ℝ))
        (burnolMultiplicativeDilation_stronglyContinuous wave).aestronglyMeasurable
        (x₀ := (0 : ℝ)) (ε := tolerance) (fun h inBall =>
          (close ((Metric.mem_ball.mp inBall).trans small)).le)
      simpa only [smooth, burnolReciprocalStepSmoothedValue,
        burnolMultiplicativeDilation_zero] using native
    have actual : (burnolPaCombApproximation n : BurnolL2) =
        coefficient • fourierL2 wave := by
      rw [burnolPaCombApproximation_raw,
        burnolReciprocalStepNativeWave_eq 1 upper (by norm_num) ordered]
    rw [actual, dist_comm]
    calc
      dist (coefficient • fourierL2 smooth) (coefficient • fourierL2 wave) =
          ‖coefficient‖ * dist smooth wave := by
        simp only [dist_eq_norm, ← smul_sub, norm_smul, ← map_sub, fourierL2.norm_map]
      _ ≤ ‖coefficient‖ * tolerance := mul_le_mul_of_nonneg_left bound (norm_nonneg _)
      _ < ε := by
        have denominator : ‖coefficient‖ + 1 ≠ 0 := by positivity
        have paid : (‖coefficient‖ + 1) * tolerance = ε := by
          dsimp only [tolerance]
          field_simp
        nlinarith

/-- Inverse on the actual image of the existing isometric completion map. -/
def actualCombLift (n : Nat) (z : ℂ)
    (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ)) :
    HilbertAmbient (quarterMellinL2Feature z) :=
  (Equiv.ofInjective (quarterMellinFeatureCompletionEvenAdditive z)
    (completion_isometry z).injective).symm
      ⟨(burnolPaCombApproximation n : BurnolL2), actual_comb_mem_range n z positive belowHalf⟩

theorem actualCombLift_readback (n : Nat) (z : ℂ)
    (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ)) :
    quarterMellinFeatureCompletionEvenAdditive z (actualCombLift n z positive belowHalf) =
      (burnolPaCombApproximation n : BurnolL2) := by
  exact congrArg Subtype.val
    ((Equiv.ofInjective (quarterMellinFeatureCompletionEvenAdditive z)
      (completion_isometry z).injective).apply_symm_apply
        ⟨(burnolPaCombApproximation n : BurnolL2), actual_comb_mem_range n z positive belowHalf⟩)

/-- The lifted source's first actual completion action is exactly the
original raw comb response, with no change of B, observation, or resolvent. -/
theorem actualCombLift_resolvent_readback {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ k : Nat, observation.coordinate = -2 * (k + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (n : Nat) :
    quarterMellinFeatureCompletionEvenAdditive (selectedCoPoissonMuntzParameter observation)
      (quarterFeatureCompletionRightResolvent (selectedCoPoissonMuntzParameter observation)
        (actualCombLift n (selectedCoPoissonMuntzParameter observation)
          (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
          (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial))) =
      (burnolPaCombPhysicalResponse observation nontrivial rightHalf n : BurnolL2) := by
  have rightQuarter : 1 / 4 < (selectedCoPoissonMuntzParameter observation).re := by
    change 1 / 4 < (observation.coordinate / 2).re
    rw [Complex.div_re]
    norm_num
    linarith
  rw [quarterMellinFeatureCompletionEvenAdditive_rightResolvent_eq_direct _ rightQuarter,
    actualCombLift_readback]
  rfl


end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CombSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
