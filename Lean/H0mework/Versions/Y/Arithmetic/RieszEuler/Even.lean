import H0mework.Versions.Y.Arithmetic.RieszEuler.GapEulerFourier
import H0mework.Versions.Y.Arithmetic.RieszEuler.Scalar
import H0mework.Versions.Y.Arithmetic.TruncatedFourier.Overlap

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszSource.GapEuler

open Complex FourierTransform MeasureTheory
open scoped FourierTransform
noncomputable section

def evenPart : TemperedDistribution ℝ ℂ →L[ℂ] TemperedDistribution ℝ ℂ :=
  (1 / 2 : ℂ) • (ContinuousLinearMap.id ℂ (TemperedDistribution ℝ ℂ) +
    (fourierCLM ℂ (TemperedDistribution ℝ ℂ)).comp
      (fourierCLM ℂ (TemperedDistribution ℝ ℂ)))

theorem evenPart_euler (value : TemperedDistribution ℝ ℂ) :
    evenPart (euler value) = euler (evenPart value) := by
  simp only [evenPart, smul_apply, add_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply, fourierCLM_apply, map_smul, map_add,
    euler_fourier, FourierTransform.fourier_neg, neg_neg]

theorem evenPart_lp (value : BurnolL2) :
    evenPart (value : TemperedDistribution ℝ ℂ) =
      (burnolAmbientEvenPart value : TemperedDistribution ℝ ℂ) := by
  simp only [evenPart, smul_apply, add_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply, fourierCLM_apply, Lp.fourier_toTemperedDistribution_eq]
  change (1 / 2 : ℂ) • ((value : TemperedDistribution ℝ ℂ) +
    (fourierL2 (fourierL2 value) : TemperedDistribution ℝ ℂ)) = _
  rw [fourierL2_fourierL2]
  change _ = Lp.toTemperedDistributionCLM ℂ volume 2 ((1 / 2 : ℂ) • (value + reflectL2 value))
  rw [map_smul, map_add]
  rfl

private theorem fourier_twice_delta (point : ℝ) :
    𝓕 (𝓕 (TemperedDistribution.delta point)) = TemperedDistribution.delta (-point) := by
  ext test
  simp only [TemperedDistribution.fourier_apply, TemperedDistribution.delta_apply]
  have inverse : (𝓕⁻ (𝓕 test) : SchwartzMap ℝ ℂ) = test :=
    FourierTransform.fourierInv_fourier_eq test
  have source := congrArg (fun f : SchwartzMap ℝ ℂ => f (-point)) inverse
  rw [SchwartzMap.fourierInv_apply_eq] at source
  change (𝓕 (𝓕 test)) (-(-point)) = test (-point) at source
  simpa only [neg_neg] using source

theorem evenPart_delta (point : ℝ) :
    evenPart (TemperedDistribution.delta point) =
      (1 / 2 : ℂ) • (TemperedDistribution.delta point + TemperedDistribution.delta (-point)) := by
  simp only [evenPart, smul_apply, add_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply, fourierCLM_apply, fourier_twice_delta]

theorem evenPart_gap (radius : ℝ) :
    evenPart (burnolAmbientGapRieszVector radius : TemperedDistribution ℝ ℂ) =
      (burnolAmbientGapRieszVector radius : TemperedDistribution ℝ ℂ) := by
  rw [evenPart_lp]
  have reflected : reflectL2 (burnolAmbientGapRieszVector radius) =
      burnolAmbientGapRieszVector radius := by
    unfold burnolAmbientGapRieszVector
    rw [map_smul]
    congr 1
    change reflectL2 (burnolRadiusZeroExtension radius (intervalConstant radius)) =
      burnolRadiusZeroExtension radius (intervalConstant radius)
    rw [burnolRadiusZeroExtension_reflect, reflectRestricted_intervalConstant]
  have same : burnolAmbientEvenPart (burnolAmbientGapRieszVector radius) =
      burnolAmbientGapRieszVector radius := by
    unfold burnolAmbientEvenPart
    rw [reflected]
    module
  rw [same]

def edge (radius : ℝ) : TemperedDistribution ℝ ℂ :=
  (radius : ℂ) • (TemperedDistribution.delta radius + TemperedDistribution.delta (-radius)) -
    ((2 * radius : ℝ) : ℂ) • (burnolAmbientGapRieszVector radius : TemperedDistribution ℝ ℂ)

theorem even_gapTail_euler (radius : ℝ) (positive : 0 < radius)
    (coordinate : BurnolCompletedMellinCoordinate) :
    let source := (burnolAmbientEvenPart
      (burnolRadiusAmbientCompletedMellinKernelFormula radius positive coordinate) :
        TemperedDistribution ℝ ℂ)
    euler source + (star coordinate.value - 1 / 2) • source =
      (-star coordinate.value * gapMean radius coordinate) • edge radius := by
  dsimp only
  let c := gapMean radius coordinate
  let z := star coordinate.value
  let p := (radius : ℂ) ^ (-star coordinate.value)
  have primitive : (1 - z) * c = (1 / 2 : ℂ) * p :=
    gapMean_primitive radius positive coordinate
  have total : star (burnolRadiusMellinGapMoment radius coordinate.value) =
      (2 * (radius : ℂ)) * c := by
    dsimp only [c, gapMean]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr positive.ne']
  have endpoint : (radius : ℂ) / 2 * p - (radius : ℂ) * c =
      -z * c * (radius : ℂ) := by
    linear_combination -(radius : ℂ) * primitive
  have source := congrArg evenPart (gapTail_euler radius positive coordinate)
  simp only [map_sub, map_smul, map_add, evenPart_euler, evenPart_delta, evenPart_gap,
    neg_neg] at source
  simp only [evenPart_lp] at source
  change euler _ - (1 / 2 - z) • _ =
    (-(radius : ℂ) * c) • ((1 / 2 : ℂ) •
      (TemperedDistribution.delta (-radius) + TemperedDistribution.delta radius)) +
    ((radius : ℂ) * (p - c)) • ((1 / 2 : ℂ) •
      (TemperedDistribution.delta radius + TemperedDistribution.delta (-radius))) +
    (z * star (burnolRadiusMellinGapMoment radius coordinate.value)) •
      (burnolAmbientGapRieszVector radius : TemperedDistribution ℝ ℂ) at source
  rw [total] at source
  have reduced : euler (burnolAmbientEvenPart
      (burnolRadiusAmbientCompletedMellinKernelFormula radius positive coordinate) :
        TemperedDistribution ℝ ℂ) -
      (1 / 2 - z) • (burnolAmbientEvenPart
        (burnolRadiusAmbientCompletedMellinKernelFormula radius positive coordinate) :
          TemperedDistribution ℝ ℂ) =
    ((radius : ℂ) / 2 * p - (radius : ℂ) * c) • TemperedDistribution.delta radius +
    ((radius : ℂ) / 2 * p - (radius : ℂ) * c) • TemperedDistribution.delta (-radius) +
    (z * (2 * (radius : ℂ)) * c) •
      (burnolAmbientGapRieszVector radius : TemperedDistribution ℝ ℂ) := by
    rw [source]
    module
  rw [endpoint] at reduced
  change euler _ + (z - 1 / 2) • _ = (-z * c) • edge radius
  rw [show z - 1 / 2 = -(1 / 2 - z) by ring]
  calc
    _ = euler _ - (1 / 2 - z) • _ := by module
    _ = _ := reduced.trans (by unfold edge; push_cast; module)

end
end OriginalRieszSource.GapEuler
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
