import H0mework.Versions.V2.Arithmetic.MellinProjection.Distribution

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszSource.GapEuler

open Complex Filter MeasureTheory Set
open scoped ENNReal Topology
noncomputable section

def position : TemperedDistribution ℝ ℂ →L[ℂ] TemperedDistribution ℝ ℂ :=
  TemperedDistribution.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ))

def euler : TemperedDistribution ℝ ℂ →L[ℂ] TemperedDistribution ℝ ℂ :=
  position.comp (TemperedDistribution.derivCLM ℂ) +
    (1 / 2 : ℂ) • ContinuousLinearMap.id ℂ (TemperedDistribution ℝ ℂ)

theorem position_delta (point : ℝ) :
    position (TemperedDistribution.delta point) =
      (point : ℂ) • TemperedDistribution.delta point := by
  ext test
  have growth : (fun x : ℝ => (x : ℂ)).HasTemperateGrowth := by fun_prop
  simp only [position, TemperedDistribution.smulLeftCLM_apply_apply,
    TemperedDistribution.delta_apply, SchwartzMap.smulLeftCLM_apply growth,
    smul_apply, smul_eq_mul]

private theorem nextHalf (coordinate : BurnolCompletedMellinCoordinate) :
    1 / 2 < (coordinate.value + 1).re := by
  simp only [Complex.add_re, Complex.one_re]
  linarith [coordinate.rightHalf]

theorem position_tail_next (radius : ℝ) (positive : 0 < radius)
    (coordinate : BurnolCompletedMellinCoordinate) :
    position (burnolRadiusMellinTailKernelL2 radius positive (coordinate.value + 1)
      (nextHalf coordinate) : TemperedDistribution ℝ ℂ) =
      (burnolRadiusMellinTailKernelL2 radius positive coordinate.value
        coordinate.rightHalf : TemperedDistribution ℝ ℂ) := by
  ext test
  have growth : (fun x : ℝ => (x : ℂ)).HasTemperateGrowth := by fun_prop
  rw [position, TemperedDistribution.smulLeftCLM_apply_apply,
    burnolMellinTail_tempered_apply, burnolMellinTail_tempered_apply]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x member
  have nonzero : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (ne_of_gt (positive.trans member))
  have power : -star (coordinate.value + 1) = -star coordinate.value - 1 := by
    simp only [star_add, star_one]
    ring
  rw [SchwartzMap.smulLeftCLM_apply growth, power,
    Complex.cpow_sub _ _ nonzero, Complex.cpow_one]
  simp only [smul_eq_mul]
  field_simp

theorem gapTail_euler (radius : ℝ) (positive : 0 < radius)
    (coordinate : BurnolCompletedMellinCoordinate) :
    let moment := star (burnolRadiusMellinGapMoment radius coordinate.value)
    let mean := moment * (((2 * radius : ℝ) : ℂ)⁻¹)
    let source := (burnolRadiusAmbientCompletedMellinKernelFormula radius positive coordinate :
      TemperedDistribution ℝ ℂ)
    euler source - (1 / 2 - star coordinate.value) • source =
      (-(radius : ℂ) * mean) • TemperedDistribution.delta (-radius) +
      ((radius : ℂ) * ((radius : ℂ) ^ (-star coordinate.value) - mean)) •
        TemperedDistribution.delta radius +
      (star coordinate.value * moment) •
        (burnolAmbientGapRieszVector radius : TemperedDistribution ℝ ℂ) := by
  dsimp only
  have split :
      (burnolRadiusAmbientCompletedMellinKernelFormula radius positive coordinate :
        TemperedDistribution ℝ ℂ) =
      star (burnolRadiusMellinGapMoment radius coordinate.value) •
        (burnolAmbientGapRieszVector radius : TemperedDistribution ℝ ℂ) +
      (burnolRadiusMellinTailKernelL2 radius positive coordinate.value
        coordinate.rightHalf : TemperedDistribution ℝ ℂ) := by
    change Lp.toTemperedDistributionCLM ℂ volume 2 (_ + _) = _
    rw [map_add, map_smul]
    rfl
  unfold euler
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    smul_apply, ContinuousLinearMap.id_apply]
  rw [burnolGapTail_distribution_derivative radius positive coordinate]
  rw [map_sub, map_add, map_smul, map_smul, map_smul,
    position_delta, position_delta, position_tail_next]
  rw [split]
  simp only [Complex.ofReal_neg]
  module

end
end OriginalRieszSource.GapEuler
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
