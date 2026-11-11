import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.Probe.Window.Action
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.Probe.Window.Recovery
import H0mework.Versions.V2.Arithmetic.RiemannNativeCurrent.UnitResponseAction

/-! Closed-radius actual Pa shells and their Fourier siblings for the same-source finite action. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

local instance : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

private theorem closedShell_inPa (coordinate : BurnolCompletedMellinCoordinate)
    (radius : ℝ) (admitted : radius ∈ Icc (1 / 4 : ℝ) 4) :
    burnolUnitTailResponse coordinate radius - burnolUnitTailResponse coordinate 4 ∈
      burnolOriginalPaInL2 := by
  rcases admitted with ⟨lower, upper⟩
  rcases eq_or_lt_of_le lower with atQuarter | aboveQuarter
  · rw [← atQuarter, ← fullPowerShellState_eq_tail_sub]
    exact Submodule.mem_map.mpr
      ⟨fullPowerShellState coordinate, fullPowerShellState_mem coordinate, rfl⟩
  rcases lt_or_eq_of_le upper with belowFour | atFour
  · rw [burnolUnitTailResponse_shell coordinate radius aboveQuarter belowFour]
    exact burnolUnitPowerShellWave_originalPa coordinate radius aboveQuarter belowFour
  · rw [atFour, sub_self]
    exact Submodule.zero_mem _

/-- The closed shell is the original difference of actual unit responses. -/
def closedShellState (coordinate : BurnolCompletedMellinCoordinate)
    (radius : ℝ) (admitted : radius ∈ Icc (1 / 4 : ℝ) 4) : BurnolPaAmbientCarrier :=
  ⟨burnolUnitTailResponse coordinate radius - burnolUnitTailResponse coordinate 4, by
    rcases Submodule.mem_map.mp (closedShell_inPa coordinate radius admitted) with
      ⟨value, _, same⟩
    rw [← same]
    exact value.property⟩

theorem closedShellState_mem (coordinate : BurnolCompletedMellinCoordinate)
    (radius : ℝ) (admitted : radius ∈ Icc (1 / 4 : ℝ) 4) :
    closedShellState coordinate radius admitted ∈ burnolCompactCoPoissonClosedRange := by
  rcases Submodule.mem_map.mp (closedShell_inPa coordinate radius admitted) with
    ⟨value, belongs, same⟩
  have exactState : value = closedShellState coordinate radius admitted := Subtype.ext same
  exact exactState ▸ belongs

theorem closedShellState_eq_tail_sub (coordinate : BurnolCompletedMellinCoordinate)
    (radius : ℝ) (admitted : radius ∈ Icc (1 / 4 : ℝ) 4) :
    (closedShellState coordinate radius admitted : BurnolL2) =
      burnolUnitTailResponse coordinate radius - burnolUnitTailResponse coordinate 4 := rfl

theorem closedShellState_four (coordinate : BurnolCompletedMellinCoordinate) :
    closedShellState coordinate 4 (by norm_num) = 0 := by
  apply Subtype.ext
  exact sub_self _

theorem closedShellState_quarter (coordinate : BurnolCompletedMellinCoordinate) :
    closedShellState coordinate (1 / 4) (by norm_num) = fullPowerShellState coordinate := by
  apply Subtype.ext
  exact (fullPowerShellState_eq_tail_sub coordinate).symm

private theorem closedShell_realizes (coordinate : BurnolCompletedMellinCoordinate)
    (radius : ℝ) (admitted : radius ∈ Icc (1 / 4 : ℝ) 4)
    (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead
      (burnolRadiusNormalizedUnitTail coordinate radius (lt_of_lt_of_le (by norm_num) admitted.1) -
        burnolNormalizedFirstSourceUnitTail coordinate) test =
      (Lp.toTemperedDistributionCLM ℂ volume 2
        (closedShellState coordinate radius admitted : BurnolL2)) test := by
  have positive : 0 < radius := lt_of_lt_of_le (by norm_num) admitted.1
  have bounded : radius⁻¹ ≤ 4 := by
    simpa only [one_div, inv_inv] using
      (inv_le_inv₀ positive (by norm_num : (0 : ℝ) < 1 / 4)).mpr admitted.1
  rw [← burnolRemainderSourceReadCLM_apply, map_sub,
    burnolRemainderSourceReadCLM_apply, burnolRemainderSourceReadCLM_apply,
    burnolUnitTailResponse_realizes coordinate radius positive bounded,
    burnolOriginalUnitTail_realizes, closedShellState_eq_tail_sub, map_sub, sub_apply]

private theorem closedShell_tail_even (coordinate : BurnolCompletedMellinCoordinate)
    (radius : ℝ) (positive : 0 < radius) :
    reflectL2 (burnolRadiusNormalizedUnitTail coordinate radius positive) =
      burnolRadiusNormalizedUnitTail coordinate radius positive := by
  unfold burnolRadiusNormalizedUnitTail
  rw [map_neg, map_add, reflectL2_reflectL2, add_comm]

/-- Faithful remainder recovery reads the source of the generated physical shell. -/
theorem closedShellState_source (coordinate : BurnolCompletedMellinCoordinate)
    (radius : ℝ) (admitted : radius ∈ Icc (1 / 4 : ℝ) 4) :
    burnolMobiusSourceL2 (closedShellState coordinate radius admitted) =
      burnolRadiusNormalizedUnitTail coordinate radius (lt_of_lt_of_le (by norm_num) admitted.1) -
        burnolNormalizedFirstSourceUnitTail coordinate := by
  let positive : 0 < radius := lt_of_lt_of_le (by norm_num) admitted.1
  let shell := closedShellState coordinate radius admitted
  let tail := burnolRadiusNormalizedUnitTail coordinate radius positive -
    burnolNormalizedFirstSourceUnitTail coordinate
  have tailEven : reflectL2 tail = tail := by
    change reflectL2 (burnolRadiusNormalizedUnitTail coordinate radius positive -
      burnolRadiusNormalizedUnitTail coordinate 4 (by norm_num)) = _
    rw [map_sub, closedShell_tail_even, closedShell_tail_even]
    rfl
  have tailGap : (tail : ℝ → ℂ) =ᵐ[volume.restrict (symmetricInterval (1 / 4 : ℝ))]
      fun _ => 0 := by
    filter_upwards [ae_restrict_of_ae (Lp.coeFn_sub
        (burnolRadiusNormalizedUnitTail coordinate radius positive)
        (burnolNormalizedFirstSourceUnitTail coordinate)),
      ae_restrict_of_ae (burnolRadiusUnitTail_coeFn coordinate radius positive),
      ae_restrict_of_ae (burnolNormalizedFirstSourceUnitTail_coeFn coordinate),
      ae_restrict_mem (measurableSet_symmetricInterval (1 / 4 : ℝ))]
      with x subRead low high hx
    have bound : |x| ≤ (1 / 4 : ℝ) := abs_le.mpr hx
    change tail x = _
    rw [subRead, Pi.sub_apply, low, high]
    simp only [burnolNormalizedFirstSourceUnitTailRaw,
      if_neg (not_lt.mpr (bound.trans admitted.1)),
      if_neg (show ¬(4 : ℝ) < |x| by linarith), sub_self]
  apply sub_eq_zero.mp
  apply burnolRemainderSourceRead_faithful (burnolMobiusSourceL2 shell - tail)
  · rw [map_sub, burnolMobiusSourceL2_even, tailEven]
  · filter_upwards [ae_restrict_of_ae (Lp.coeFn_sub (burnolMobiusSourceL2 shell) tail),
      burnolMobiusSourceL2_innerGap shell, tailGap] with x subRead sourceRead tailRead
    rw [subRead, Pi.sub_apply, sourceRead, tailRead, sub_self]
  · intro test
    have actual := closedShell_realizes coordinate radius admitted test
    simp only [Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistribution_apply,
      smul_eq_mul] at actual
    rw [← burnolRemainderSourceReadCLM_apply, map_sub,
      burnolRemainderSourceReadCLM_apply, burnolRemainderSourceReadCLM_apply,
      burnolRemainderSourceRead_Pa shell (closedShellState_mem coordinate radius admitted) test]
    change (∫ x : ℝ, test x * (shell : BurnolL2) x) -
      burnolRemainderSourceRead tail test = 0
    rw [actual, sub_self]

/-- The negative Fourier sibling is generated from the same closed shell. -/
def negativeFourierShellState (coordinate : BurnolCompletedMellinCoordinate)
    (radius : ℝ) (admitted : radius ∈ Icc (1 / 4 : ℝ) 4) : BurnolPaAmbientCarrier :=
  -evenFaceFourierEquiv burnolUnscaledCommonGapRadius (closedShellState coordinate radius admitted)

theorem negativeFourierShellState_mem (coordinate : BurnolCompletedMellinCoordinate)
    (radius : ℝ) (admitted : radius ∈ Icc (1 / 4 : ℝ) 4) :
    negativeFourierShellState coordinate radius admitted ∈ burnolCompactCoPoissonClosedRange :=
  burnolCompactCoPoissonClosedRange.toSubmodule.neg_mem
    (burnolCompactCoPoissonActionSquare.toIsometricSquare.target_mem_closedRange
      (closedShellState_mem coordinate radius admitted))

theorem negativeFourierShellState_source (coordinate : BurnolCompletedMellinCoordinate)
    (radius : ℝ) (admitted : radius ∈ Icc (1 / 4 : ℝ) 4) :
    burnolMobiusSourceL2 (negativeFourierShellState coordinate radius admitted) =
      -burnolTateReciprocalL2
        (burnolRadiusNormalizedUnitTail coordinate radius (lt_of_lt_of_le (by norm_num) admitted.1) -
          burnolNormalizedFirstSourceUnitTail coordinate) := by
  rw [negativeFourierShellState, map_neg,
    burnolMobiusSource_fourier _ (closedShellState_mem coordinate radius admitted),
    closedShellState_source]

theorem negativeFourierShellState_eq_response (coordinate : BurnolCompletedMellinCoordinate)
    (radius : ℝ) (admitted : radius ∈ Icc (1 / 4 : ℝ) 4) :
    (negativeFourierShellState coordinate radius admitted : BurnolL2) =
      -fourierL2 (burnolUnitTailResponse coordinate radius -
        burnolUnitTailResponse coordinate 4) := rfl

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
