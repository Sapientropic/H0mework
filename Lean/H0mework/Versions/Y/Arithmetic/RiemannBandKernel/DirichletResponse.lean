import H0mework.Versions.Y.Arithmetic.RiemannUnitFourier.Realization
import H0mework.Versions.Y.Arithmetic.RiemannBandKernel.Head

/-! The original band action eliminates the Bochner integral from every native Pa forcing response. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section
local instance : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

theorem burnolUnitTailResponse_scaledInverse_coeFn (coordinate : BurnolCompletedMellinCoordinate)
    (upper : ℝ) (positive : 0 < upper) :
    ((Real.sqrt upper : ℂ) • burnolMultiplicativeDilation (-Real.log upper)
      (burnolUnitTailResponse coordinate 1) : BurnolL2) =ᵐ[volume]
        fun x : ℝ => burnolUnitTailDirichletRaw coordinate.value 1 (x / upper) := by
  let value := burnolUnitTailResponse coordinate 1
  have qmp := Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
    (r := Real.exp (-Real.log upper)) (Real.exp_ne_zero _)
  have pulled : ∀ᵐ x : ℝ ∂volume, value (Real.exp (-Real.log upper) * x) =
      burnolUnitTailDirichletRaw coordinate.value 1 (Real.exp (-Real.log upper) * x) := by
    simpa only [smul_eq_mul] using qmp.ae
      (burnolUnitTailResponse_coeFn coordinate 1 (by norm_num) (by norm_num))
  filter_upwards [Lp.coeFn_smul (Real.sqrt upper : ℂ)
    (burnolMultiplicativeDilation (-Real.log upper) value),
    burnolMultiplicativeDilation_coeFn (-Real.log upper) value, pulled] with x smulAt dilationAt rawAt
  rw [smulAt]
  change (Real.sqrt upper : ℂ) * burnolMultiplicativeDilation (-Real.log upper) value x = _
  rw [dilationAt]
  unfold burnolL2RawNormalizedDilation
  rw [rawAt]
  have root : Real.sqrt upper = Real.exp (Real.log upper / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos positive]
    congr 1
    ring
  have amplitude : Real.sqrt upper * Real.exp (-Real.log upper / 2) = 1 := by
    rw [root, ← Real.exp_add, show Real.log upper / 2 + -Real.log upper / 2 = 0 by ring, Real.exp_zero]
  rw [← mul_assoc, ← Complex.ofReal_mul, amplitude, Complex.ofReal_one, one_mul,
    Real.exp_neg, Real.exp_log positive, inv_mul_eq_div]

def burnolPaCombResponseDirichletRaw (coordinate : ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  ((n : ℂ) + 2) / (coordinate / 2) *
    (burnolUnitTailDirichletRaw coordinate 1 (x / (1 + burnolPaCombSourceWidth n)) -
      burnolUnitTailDirichletRaw coordinate 1 x -
        burnolHarmonicStepWaveRaw 1 (1 + burnolPaCombSourceWidth n) x)

theorem burnolPaCombResolvent_coeFn (coordinate : BurnolCompletedMellinCoordinate) (n : ℕ) :
    (burnolDirectRightResolvent (coordinate.value / 2)
      (burnolPaCombApproximation n : BurnolL2) : ℝ → ℂ) =ᵐ[volume]
        burnolPaCombResponseDirichletRaw coordinate.value n := by
  let b := 1 + burnolPaCombSourceWidth n
  let V := burnolUnitTailResponse coordinate 1
  let band := fourierL2 (burnolReciprocalStepNativeWave 1 b)
  let scaled := (Real.sqrt b : ℂ) • burnolMultiplicativeDilation (-Real.log b) V
  have positive : 0 < b := by dsimp only [b]; linarith [(burnolPaCombSourceWidth_bounds n).1]
  have zNe : coordinate.value / 2 ≠ 0 := by
    intro zero
    have realPart := congrArg Complex.re zero
    rw [Complex.div_re] at realPart
    norm_num at realPart
    linarith [coordinate.rightHalf]
  have action := congrArg (fun value : BurnolL2 => (coordinate.value / 2)⁻¹ • value)
    (burnolPaBandResolvent_action coordinate b)
  rw [inv_smul_smul₀ zNe] at action
  have generated : burnolDirectRightResolvent (coordinate.value / 2)
      (burnolPaCombApproximation n : BurnolL2) =
        (((n : ℂ) + 2) / (coordinate.value / 2)) • (scaled - V - band) := by
    rw [burnolPaCombApproximation_raw, burnolDirectRightResolvent_smul]
    change ((n : ℂ) + 2) • burnolDirectRightResolvent (coordinate.value / 2) band = _
    rw [action, smul_smul]
    rfl
  rw [generated]
  have rawBand := burnolReciprocalStepFourier_coeFn 1 b (by norm_num)
    (by dsimp only [b]; linarith [(burnolPaCombSourceWidth_bounds n).1])
    (by dsimp only [b]; linarith [(burnolPaCombSourceWidth_bounds n).2])
  filter_upwards [Lp.coeFn_smul (((n : ℂ) + 2) / (coordinate.value / 2)) (scaled - V - band),
    Lp.coeFn_sub (scaled - V) band, Lp.coeFn_sub scaled V,
    burnolUnitTailResponse_scaledInverse_coeFn coordinate b positive,
    burnolUnitTailResponse_coeFn coordinate 1 (by norm_num) (by norm_num), rawBand]
      with x smulAt outerAt innerAt scaledAt valueAt bandAt
  rw [smulAt]
  change (((n : ℂ) + 2) / (coordinate.value / 2)) * (scaled - V - band : BurnolL2) x = _
  rw [outerAt]
  change (((n : ℂ) + 2) / (coordinate.value / 2)) * ((scaled - V : BurnolL2) x - band x) = _
  rw [innerAt]
  change (((n : ℂ) + 2) / (coordinate.value / 2)) * (scaled x - V x - band x) = _
  rw [scaledAt, valueAt, bandAt]
  rfl

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
