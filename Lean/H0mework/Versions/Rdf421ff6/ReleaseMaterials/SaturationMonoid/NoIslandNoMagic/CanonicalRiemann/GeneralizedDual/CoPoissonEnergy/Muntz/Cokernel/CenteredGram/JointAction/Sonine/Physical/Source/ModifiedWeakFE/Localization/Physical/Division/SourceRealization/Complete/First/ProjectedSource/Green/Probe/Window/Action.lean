import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.Probe.Window.Realization
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Weyl.RealProbe
import H0mework.Versions.V2.Arithmetic.RiemannUnitFourier.Realization

/-! Bounded source-mechanism calculation for the actual free-probe physical window. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

theorem fullPowerShellState_eq_tail_sub (coordinate : BurnolCompletedMellinCoordinate) :
    (fullPowerShellState coordinate : BurnolL2) =
      burnolUnitTailResponse coordinate (1 / 4) - burnolUnitTailResponse coordinate 4 := by
  apply LinearMap.ker_eq_bot.mp
    (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ) (μ := volume))
  ext test
  change (Lp.toTemperedDistributionCLM ℂ volume 2
    (fullPowerShellState coordinate : BurnolL2)) test =
      (Lp.toTemperedDistributionCLM ℂ volume 2
        (burnolUnitTailResponse coordinate (1 / 4) - burnolUnitTailResponse coordinate 4)) test
  have read := fullPowerShell_realizes coordinate test
  rw [← burnolRemainderSourceReadCLM_apply, map_sub,
    burnolRemainderSourceReadCLM_apply, burnolRemainderSourceReadCLM_apply,
    burnolUnitTailResponse_realizes coordinate (1 / 4) (by norm_num) (by norm_num),
    burnolOriginalUnitTail_realizes] at read
  simpa only [map_sub, sub_apply] using read.symm

theorem secondWindowPhysical_raw_action (coordinate : BurnolCompletedMellinCoordinate)
    (p : burnolCompactCoPoissonClosedRange.toSubmodule) :
    (secondWindowPhysical coordinate p : BurnolL2) =
      (2 / (2 * coordinate.value - 1) : ℂ) •
        (burnolDirectRightResolvent (coordinate.value / 2) (p : BurnolL2) +
          fourierL2 (burnolDirectRightResolvent (coordinate.value / 2) (p : BurnolL2)) -
          burnolPaResolventSourceCoefficient coordinate p •
            (burnolUnitTailResponse coordinate (1 / 4) +
              fourierL2 (burnolUnitTailResponse coordinate 4))) := by
  let C := burnolPaSourceCorrection coordinate p
  let M := burnolPaResolventSourceCoefficient coordinate p
  have raw : (C : BurnolL2) =
      burnolDirectRightResolvent (coordinate.value / 2) (p : BurnolL2) -
        M • burnolUnitTailResponse coordinate 4 := rfl
  change (2 / (2 * coordinate.value - 1) : ℂ) •
    ((C : BurnolL2) + fourierL2 (C : BurnolL2) -
      M • (fullPowerShellState coordinate : BurnolL2)) = _
  rw [raw, fullPowerShellState_eq_tail_sub, map_sub, map_smul]
  dsimp only [M]
  module

theorem secondWindowPhysical_three_quarter_pairing
    (p : burnolCompactCoPoissonClosedRange.toSubmodule)
    (fixed : evenFaceFourierEquiv burnolUnscaledCommonGapRadius
      (p : BurnolPaAmbientCarrier) = p) :
    let z : BurnolCompletedMellinCoordinate := ⟨(3 / 4 : ℂ), by norm_num, by norm_num⟩
    inner ℂ (p : BurnolL2) (secondWindowPhysical z p : BurnolL2) =
      -(‖burnolDirectRightResolvent (3 / 8) (p : BurnolL2)‖ : ℂ) ^ 2 -
        4 * burnolPaResolventSourceCoefficient z p *
          inner ℂ (p : BurnolL2)
            (burnolUnitTailResponse z (1 / 4) + fourierL2 (burnolUnitTailResponse z 4)) := by
  intro z
  have pf : fourierL2 (p : BurnolL2) = p := congrArg Subtype.val fixed
  have readF (v : BurnolL2) : inner ℂ (p : BurnolL2) (fourierL2 v) =
      inner ℂ (p : BurnolL2) v := by
    have same := fourierL2.inner_map_map (p : BurnolL2) v
    rw [pf] at same
    exact same
  have diagonal := burnolDirectRightResolvent_realDiagonal (3 / 8) (by norm_num)
    (p : BurnolL2) pf
  norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat] at diagonal
  rw [secondWindowPhysical_raw_action]
  change inner ℂ (p : BurnolL2) ((2 / (2 * (3 / 4 : ℂ) - 1)) •
    (burnolDirectRightResolvent ((3 / 4 : ℂ) / 2) (p : BurnolL2) +
      fourierL2 (burnolDirectRightResolvent ((3 / 4 : ℂ) / 2) (p : BurnolL2)) -
      burnolPaResolventSourceCoefficient z p •
        (burnolUnitTailResponse z (1 / 4) + fourierL2 (burnolUnitTailResponse z 4)))) = _
  rw [show ((3 / 4 : ℂ) / 2) = 3 / 8 by norm_num,
    inner_smul_right, inner_sub_right, inner_add_right, inner_smul_right, readF, diagonal]
  ring

theorem sourceWindowBoundary_dirichlet_read (coordinate : BurnolCompletedMellinCoordinate)
    (p : burnolCompactCoPoissonClosedRange.toSubmodule)
    (fixed : evenFaceFourierEquiv burnolUnscaledCommonGapRadius
      (p : BurnolPaAmbientCarrier) = p) :
    inner ℂ (p : BurnolL2)
      (burnolUnitTailResponse coordinate (1 / 4) + fourierL2 (burnolUnitTailResponse coordinate 4)) =
      ∫ x : ℝ, star ((p : BurnolL2) x) *
        (burnolUnitTailDirichletRaw coordinate.value (1 / 4) x +
          burnolUnitTailDirichletRaw coordinate.value 4 x) := by
  have pf : fourierL2 (p : BurnolL2) = p := congrArg Subtype.val fixed
  have same := fourierL2.inner_map_map (p : BurnolL2) (burnolUnitTailResponse coordinate 4)
  rw [pf] at same
  rw [inner_add_right, same, ← inner_add_right, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [burnolUnitTailResponse_coeFn coordinate (1 / 4) (by norm_num) (by norm_num),
    burnolUnitTailResponse_coeFn coordinate 4 (by norm_num) (by norm_num),
    Lp.coeFn_add (burnolUnitTailResponse coordinate (1 / 4)) (burnolUnitTailResponse coordinate 4)]
    with x low high add
  rw [add, Pi.add_apply, low, high, RCLike.inner_apply, starRingEnd_apply, mul_comm]

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
