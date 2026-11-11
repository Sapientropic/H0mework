import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.Probe.Window.Realization
import H0mework.Versions.R7e4da746.Arithmetic.RemainderSource.Recovery

/-! Full source recovery identifies the window's generated physical and arithmetic faces. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

private theorem even_tail (coordinate : BurnolCompletedMellinCoordinate) (radius : ℝ)
    (positive : 0 < radius) :
    reflectL2 (burnolRadiusNormalizedUnitTail coordinate radius positive) =
      burnolRadiusNormalizedUnitTail coordinate radius positive := by
  unfold burnolRadiusNormalizedUnitTail
  rw [map_neg, map_add, reflectL2_reflectL2, add_comm]

theorem fullPowerShell_source (coordinate : BurnolCompletedMellinCoordinate) :
    burnolMobiusSourceL2 (fullPowerShellState coordinate) =
      burnolRadiusNormalizedUnitTail coordinate (1 / 4) (by norm_num) -
        burnolNormalizedFirstSourceUnitTail coordinate := by
  let shell := fullPowerShellState coordinate
  let tail := burnolRadiusNormalizedUnitTail coordinate (1 / 4) (by norm_num) -
    burnolNormalizedFirstSourceUnitTail coordinate
  have tailEven : reflectL2 tail = tail := by
    change reflectL2 (burnolRadiusNormalizedUnitTail coordinate (1 / 4) (by norm_num) -
      burnolRadiusNormalizedUnitTail coordinate 4 (by norm_num)) = _
    rw [map_sub, even_tail, even_tail]
    rfl
  have tailGap : (tail : ℝ → ℂ) =ᵐ[volume.restrict (symmetricInterval (1 / 4 : ℝ))] fun _ => 0 := by
    filter_upwards [ae_restrict_of_ae (Lp.coeFn_sub
        (burnolRadiusNormalizedUnitTail coordinate (1 / 4) (by norm_num))
        (burnolNormalizedFirstSourceUnitTail coordinate)),
      ae_restrict_of_ae (burnolRadiusUnitTail_coeFn coordinate (1 / 4) (by norm_num)),
      ae_restrict_of_ae (burnolNormalizedFirstSourceUnitTail_coeFn coordinate),
      ae_restrict_mem (measurableSet_symmetricInterval (1 / 4 : ℝ))] with x subRead low high hx
    have bound : |x| ≤ (1 / 4 : ℝ) := abs_le.mpr (by simpa only [symmetricInterval, mem_Icc] using hx)
    change tail x = _
    rw [subRead, Pi.sub_apply, low, high]
    simp only [burnolNormalizedFirstSourceUnitTailRaw, if_neg (not_lt.mpr bound),
      if_neg (show ¬(4 : ℝ) < |x| by linarith), sub_self]
  apply sub_eq_zero.mp
  apply burnolRemainderSourceRead_faithful (burnolMobiusSourceL2 shell - tail)
  · rw [map_sub, burnolMobiusSourceL2_even, tailEven]
  · filter_upwards [ae_restrict_of_ae (Lp.coeFn_sub (burnolMobiusSourceL2 shell) tail),
      burnolMobiusSourceL2_innerGap shell, tailGap] with x subRead sourceRead tailRead
    rw [subRead, Pi.sub_apply, sourceRead, tailRead, sub_self]
  · intro test
    have actual := fullPowerShell_realizes coordinate test
    simp only [Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistribution_apply, smul_eq_mul] at actual
    rw [← burnolRemainderSourceReadCLM_apply, map_sub,
      burnolRemainderSourceReadCLM_apply, burnolRemainderSourceReadCLM_apply,
      burnolRemainderSourceRead_Pa shell (fullPowerShellState_mem coordinate) test]
    change (∫ x : ℝ, test x * (shell : BurnolL2) x) - burnolRemainderSourceRead tail test = 0
    rw [actual, sub_self]

theorem secondWindowPhysical_source (coordinate : BurnolCompletedMellinCoordinate)
    (p : burnolCompactCoPoissonClosedRange.toSubmodule) :
    burnolMobiusSourceL2 (secondWindowPhysical coordinate p) = sourceSecondWindow coordinate p := by
  let C := burnolPaSourceCorrection coordinate p
  have paired := burnolMobiusSource_fourier C (burnolPaSourceCorrection_mem coordinate p)
  unfold secondWindowPhysical
  rw [map_smul, map_sub, map_add, map_smul, fullPowerShell_source]
  change (2 / (2 * coordinate.value - 1) : ℂ) •
    (burnolMobiusSourceL2 C +
      burnolMobiusSourceL2 (evenFaceFourierEquiv burnolUnscaledCommonGapRadius C) -
      burnolPaResolventSourceCoefficient coordinate p •
        (burnolRadiusNormalizedUnitTail coordinate (1 / 4) (by norm_num) -
          burnolNormalizedFirstSourceUnitTail coordinate)) = _
  rw [paired]
  rfl

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
