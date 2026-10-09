import H0mework.Versions.V2.Arithmetic.RiemannBandKernel.Band
import H0mework.Versions.V2.Arithmetic.RiemannBandResponse.Approximation

/-! Every actual native forcing orbit has its finite harmonic profile; its Pa-band pairing keeps the full orbit. -/

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

local instance : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

def burnolPaCombOrbitRaw (n : ℕ) (shift x : ℝ) : ℂ :=
  (Real.exp (shift / 2) : ℂ) * (((n : ℂ) + 2) *
    burnolHarmonicStepWaveRaw 1 (1 + burnolPaCombSourceWidth n) (Real.exp shift * x))

theorem burnolPaCombApproximation_coeFn (n : ℕ) :
    ((burnolPaCombApproximation n : BurnolL2) : ℝ → ℂ) =ᵐ[volume]
      fun x => ((n : ℂ) + 2) * burnolHarmonicStepWaveRaw 1 (1 + burnolPaCombSourceWidth n) x := by
  rw [burnolPaCombApproximation_raw]
  have profile := burnolReciprocalStepFourier_coeFn 1 (1 + burnolPaCombSourceWidth n) (by norm_num)
    (by linarith [(burnolPaCombSourceWidth_bounds n).1])
    (by linarith [(burnolPaCombSourceWidth_bounds n).2])
  filter_upwards [Lp.coeFn_smul ((n : ℂ) + 2)
    (fourierL2 (burnolReciprocalStepNativeWave 1 (1 + burnolPaCombSourceWidth n))), profile]
      with x smulAt rawAt
  rw [smulAt]
  change ((n : ℂ) + 2) * _ = _
  rw [rawAt]

/-- The entire original L² orbit is read; it is not truncated to shifts preserving Pa. -/
theorem burnolPaCombOrbit_coeFn (n : ℕ) (shift : ℝ) :
    (burnolMultiplicativeDilation shift (burnolPaCombApproximation n : BurnolL2) : ℝ → ℂ) =ᵐ[volume]
      burnolPaCombOrbitRaw n shift := by
  have qmp := Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
    (r := Real.exp shift) (Real.exp_ne_zero _)
  have pulled : ∀ᵐ x : ℝ ∂volume, (burnolPaCombApproximation n : BurnolL2) (Real.exp shift * x) =
      ((n : ℂ) + 2) * burnolHarmonicStepWaveRaw 1 (1 + burnolPaCombSourceWidth n) (Real.exp shift * x) := by
    simpa only [smul_eq_mul] using qmp.ae (burnolPaCombApproximation_coeFn n)
  filter_upwards [burnolMultiplicativeDilation_coeFn shift (burnolPaCombApproximation n : BurnolL2),
    pulled] with x dilationAt sourceAt
  rw [dilationAt]
  change (Real.exp (shift / 2) : ℂ) * (burnolPaCombApproximation n : BurnolL2) (Real.exp shift * x) = _
  rw [sourceAt]
  rfl

theorem burnolPaFourierBandProbe_orbit_inner (a b : ℝ) (aStrict : (1 / 4 : ℝ) < a)
    (ordered : a ≤ b) (bounded : b < 4) (n : ℕ) (shift : ℝ) :
    inner ℂ (burnolPaFourierBandProbe a b aStrict ordered bounded : BurnolL2)
      (burnolMultiplicativeDilation shift (burnolPaCombApproximation n : BurnolL2)) =
      ∫ x : ℝ, star (burnolPaFourierBandProbeRaw a b x) * burnolPaCombOrbitRaw n shift x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [burnolPaFourierBandProbe_coeFn a b aStrict ordered bounded,
    burnolPaCombOrbit_coeFn n shift] with x probeAt sourceAt
  rw [probeAt, sourceAt, RCLike.inner_apply, starRingEnd_apply, mul_comm]
end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
