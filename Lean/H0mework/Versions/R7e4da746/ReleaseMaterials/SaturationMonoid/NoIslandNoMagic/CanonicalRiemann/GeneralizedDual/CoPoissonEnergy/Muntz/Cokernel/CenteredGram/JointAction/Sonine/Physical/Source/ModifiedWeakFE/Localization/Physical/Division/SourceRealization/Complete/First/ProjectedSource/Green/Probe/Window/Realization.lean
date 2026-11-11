import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.Probe.Window.PowerShell

/-! The generated source window and its actual Pa wave are one remainder-action occurrence. -/

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

def secondWindowPhysical (coordinate : BurnolCompletedMellinCoordinate)
    (p : burnolCompactCoPoissonClosedRange.toSubmodule) : BurnolPaAmbientCarrier :=
  let C := burnolPaSourceCorrection coordinate p
  (2 / (2 * coordinate.value - 1) : ℂ) •
    (C + evenFaceFourierEquiv burnolUnscaledCommonGapRadius C -
      burnolPaResolventSourceCoefficient coordinate p • fullPowerShellState coordinate)

theorem secondWindowPhysical_mem (coordinate : BurnolCompletedMellinCoordinate)
    (p : burnolCompactCoPoissonClosedRange.toSubmodule) :
    secondWindowPhysical coordinate p ∈ burnolCompactCoPoissonClosedRange := by
  let Pa := burnolCompactCoPoissonClosedRange.toSubmodule
  have correction := burnolPaSourceCorrection_mem coordinate p
  exact Pa.smul_mem _ (Pa.sub_mem (Pa.add_mem correction
    (burnolCompactCoPoissonActionSquare.toIsometricSquare.target_mem_closedRange correction))
      (Pa.smul_mem _ (fullPowerShellState_mem coordinate)))

theorem secondWindowPhysical_realizes (coordinate : BurnolCompletedMellinCoordinate)
    (p : burnolCompactCoPoissonClosedRange.toSubmodule) (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead (sourceSecondWindow coordinate p) test =
      (Lp.toTemperedDistributionCLM ℂ volume 2 (secondWindowPhysical coordinate p : BurnolL2)) test := by
  let C := burnolPaSourceCorrection coordinate p
  let F := evenFaceFourierEquiv burnolUnscaledCommonGapRadius
  let M := burnolPaResolventSourceCoefficient coordinate p
  let factor : ℂ := 2 / (2 * coordinate.value - 1)
  let shell := fullPowerShellState coordinate
  let tail := burnolRadiusNormalizedUnitTail coordinate (1 / 4) (by norm_num) -
    burnolNormalizedFirstSourceUnitTail coordinate
  let read := burnolRemainderSourceReadCLM test
  have standard (value : BurnolPaAmbientCarrier) (inside : value ∈ burnolCompactCoPoissonClosedRange) :
      read (burnolMobiusSourceL2 value) =
        (Lp.toTemperedDistributionCLM ℂ volume 2 (value : BurnolL2)) test := by
    simpa only [read, burnolRemainderSourceReadCLM_apply, Lp.toTemperedDistributionCLM_apply,
      Lp.toTemperedDistribution_apply, smul_eq_mul] using burnolRemainderSourceRead_Pa value inside test
  have inside : C ∈ burnolCompactCoPoissonClosedRange := burnolPaSourceCorrection_mem coordinate p
  have fInside : F C ∈ burnolCompactCoPoissonClosedRange :=
    burnolCompactCoPoissonActionSquare.toIsometricSquare.target_mem_closedRange inside
  have paired : burnolMobiusSourceL2 (F C) = burnolTateReciprocalL2 (burnolMobiusSourceL2 C) :=
    burnolMobiusSource_fourier C inside
  have shellRead : read tail = (Lp.toTemperedDistributionCLM ℂ volume 2 (shell : BurnolL2)) test := by
    simpa only [read, burnolRemainderSourceReadCLM_apply, tail, shell] using
      fullPowerShell_realizes coordinate test
  rw [← burnolRemainderSourceReadCLM_apply]
  change read (factor • (burnolMobiusSourceL2 C +
    burnolTateReciprocalL2 (burnolMobiusSourceL2 C) - M • tail)) =
      (Lp.toTemperedDistributionCLM ℂ volume 2
        (factor • ((C : BurnolL2) + (F C : BurnolL2) - M • (shell : BurnolL2)))) test
  rw [← paired, map_smul, map_sub, map_add, map_smul, standard C inside, standard (F C) fInside, shellRead]
  simp only [map_smul, map_sub, map_add, smul_apply, sub_apply, add_apply, smul_eq_mul]

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
