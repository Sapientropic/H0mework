import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.MovingInput.Wave
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Unit.ConjugateLow

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.MovingInput.Top
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalKSourceResolventReconstruction OriginalKFiniteOrderRelease
open OriginalKFiniteOrderRelease.UnitPowerSource
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.MovingInput.Wave OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Unit.ConjugateLow
open OriginalKCrossParameterRAdjointSource.PaNativePortSource
open OriginalKCrossParameterRAdjointSource.SharedOutsideSource
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Prime.KSourceEnergy
open scoped Topology InnerProductSpace
local notation "order" => generatedRiemannXiZeroOrder ActualAnalyticOwner
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "K" => burnolCompletedMellinRieszVector

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => order observation.coordinate
include nontrivial

/-- The original full m-power consumer reads the actual two-source wave and its complete Unit fee. -/
theorem actual_original_wave_top_source (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    inner ℂ (sourceKernelCombo c)
      (CombSource.Division.rawIterate observation half.down m (originalPaPair c h : BurnolL2)) =
        feedbackCoefficient observation half *
          (2 * ∫ t : ℝ in Icc (1/4 : ℝ) 4, (t : ℂ)^(-(c).value) *
            jointInput c observation.mathlibZero h t) := by
  let input := originalPairInput c h nonnegative bounded
  have source := actual_Pa_power_source observation nontrivial half input.val input.property
  change inner ℂ (sourceKernelCombo c)
    (CombSource.Division.rawIterate observation half.down m (originalPaPair c h : BurnolL2)) =
      feedbackCoefficient observation half * burnolPaResolventSourceCoefficient c (originalPaPair c h) at source
  have fee := actual_original_pair_port c observation.mathlibZero h nonnegative bounded 0
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one] at fee
  change burnolPaResolventSourceCoefficient c (originalPaPair c h) = _ at fee
  rw [fee] at source
  exact source

/-- The independently generated conjugate Fourier zero reads this same acted whole field. -/
theorem actual_original_wave_conjugate_top_zero (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    inner ℂ (fourierL2 (K (barC c) : BurnolL2))
      (CombSource.Division.rawIterate observation half.down m (originalPaPair c h : BurnolL2)) = 0 := by
  let input := originalPairInput c h nonnegative bounded
  exact actual_conjugate_FK_Pa_power_low observation nontrivial half input.val input.property m le_rfl

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.MovingInput.Top
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
