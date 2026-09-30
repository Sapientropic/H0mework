import H0mework.Versions.Y.Arithmetic.RiemannUnitShell.HarmonicRealization

/-! Source-generated Fourier-fixed Pa band tests read both the counted and harmonic faces in the same Gram kernel. -/

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

local instance : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

/-- One original counted band and its actual Fourier sibling, in the original physical carrier. -/
def burnolPaFourierBandProbe (lower upper : ℝ) (lowerStrict : (1 / 4 : ℝ) < lower)
    (ordered : lower ≤ upper) (bounded : upper < 4) : BurnolPaAmbientCarrier :=
  let point := burnolReciprocalStepPhysicalState lower upper lowerStrict ordered bounded.le
  (1 / 2 : ℂ) • (point + evenFaceFourierEquiv burnolUnscaledCommonGapRadius point)

def burnolPaFourierBandProbeRaw (lower upper x : ℝ) : ℂ :=
  (1 / 2 : ℂ) * (burnolReciprocalStepWaveRaw lower upper x + burnolHarmonicStepWaveRaw lower upper x)

theorem burnolPaFourierBandProbe_mem (lower upper : ℝ) (lowerStrict : (1 / 4 : ℝ) < lower)
    (ordered : lower ≤ upper) (bounded : upper < 4) :
    burnolPaFourierBandProbe lower upper lowerStrict ordered bounded ∈ burnolCompactCoPoissonClosedRange := by
  have point := burnolReciprocalStepWave_memPa lower upper lowerStrict ordered bounded
  exact burnolCompactCoPoissonClosedRange.toSubmodule.smul_mem _
    (burnolCompactCoPoissonClosedRange.toSubmodule.add_mem point
      (burnolCompactCoPoissonActionSquare.toIsometricSquare.target_mem_closedRange point))

theorem burnolPaFourierBandProbe_fourier_fixed (lower upper : ℝ) (lowerStrict : (1 / 4 : ℝ) < lower)
    (ordered : lower ≤ upper) (bounded : upper < 4) :
    evenFaceFourierEquiv burnolUnscaledCommonGapRadius
      (burnolPaFourierBandProbe lower upper lowerStrict ordered bounded) =
        burnolPaFourierBandProbe lower upper lowerStrict ordered bounded := by
  let point := burnolReciprocalStepPhysicalState lower upper lowerStrict ordered bounded.le
  have twice := evenFaceFourier_involutive burnolUnscaledCommonGapRadius point
  change evenFaceFourierEquiv burnolUnscaledCommonGapRadius
    (evenFaceFourierEquiv burnolUnscaledCommonGapRadius point) = point at twice
  change evenFaceFourierEquiv burnolUnscaledCommonGapRadius
    ((1 / 2 : ℂ) • (point + evenFaceFourierEquiv burnolUnscaledCommonGapRadius point)) =
      (1 / 2 : ℂ) • (point + evenFaceFourierEquiv burnolUnscaledCommonGapRadius point)
  rw [map_smul, map_add, twice]
  module

theorem burnolPaFourierBandProbe_coeFn (lower upper : ℝ) (lowerStrict : (1 / 4 : ℝ) < lower)
    (ordered : lower ≤ upper) (bounded : upper < 4) :
    ((burnolPaFourierBandProbe lower upper lowerStrict ordered bounded : BurnolL2) : ℝ → ℂ) =ᵐ[volume]
      burnolPaFourierBandProbeRaw lower upper := by
  let point := burnolReciprocalStepPhysicalState lower upper lowerStrict ordered bounded.le
  have pointRaw : ((point : BurnolL2) : ℝ → ℂ) =ᵐ[volume] burnolReciprocalStepWaveRaw lower upper :=
    (burnolReciprocalStepWave_memLp lower upper (lt_trans (by norm_num) lowerStrict) ordered).coeFn_toLp
  have fourierRaw := burnolReciprocalStepFourier_coeFn lower upper lowerStrict ordered bounded.le
  rw [burnolReciprocalStepNativeWave_eq lower upper (lt_trans (by norm_num) lowerStrict) ordered] at fourierRaw
  change (fourierL2 (point : BurnolL2) : ℝ → ℂ) =ᵐ[volume] burnolHarmonicStepWaveRaw lower upper at fourierRaw
  filter_upwards [Lp.coeFn_smul (1 / 2 : ℂ) ((point : BurnolL2) + fourierL2 (point : BurnolL2)),
    Lp.coeFn_add (point : BurnolL2) (fourierL2 (point : BurnolL2)), pointRaw, fourierRaw]
      with x smulAt addAt countAt harmonicAt
  change ((1 / 2 : ℂ) • ((point : BurnolL2) + fourierL2 (point : BurnolL2)) : BurnolL2) x = _
  rw [smulAt]
  change (1 / 2 : ℂ) * ((point : BurnolL2) + fourierL2 (point : BurnolL2) : BurnolL2) x = _
  rw [addAt]
  change (1 / 2 : ℂ) * ((point : BurnolL2) x + fourierL2 (point : BurnolL2) x) = _
  rw [countAt, harmonicAt]
  rfl

theorem burnolPaFourierBandProbe_gram (a b c d : ℝ) (aStrict : (1 / 4 : ℝ) < a) (ab : a ≤ b) (bBound : b < 4)
    (cStrict : (1 / 4 : ℝ) < c) (cd : c ≤ d) (dBound : d < 4) :
    inner ℂ (burnolPaFourierBandProbe a b aStrict ab bBound) (burnolPaFourierBandProbe c d cStrict cd dBound) =
      ∫ x : ℝ, star (burnolPaFourierBandProbeRaw a b x) * burnolPaFourierBandProbeRaw c d x := by
  change inner ℂ (burnolPaFourierBandProbe a b aStrict ab bBound : BurnolL2)
    (burnolPaFourierBandProbe c d cStrict cd dBound : BurnolL2) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [burnolPaFourierBandProbe_coeFn a b aStrict ab bBound,
    burnolPaFourierBandProbe_coeFn c d cStrict cd dBound] with x left right
  rw [left, right, RCLike.inner_apply, starRingEnd_apply, mul_comm]
end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
