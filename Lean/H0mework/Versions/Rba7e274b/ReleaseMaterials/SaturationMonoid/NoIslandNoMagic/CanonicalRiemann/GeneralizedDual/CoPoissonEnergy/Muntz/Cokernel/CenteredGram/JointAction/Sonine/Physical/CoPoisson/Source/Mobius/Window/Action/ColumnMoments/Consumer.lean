import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ColumnMoments.ResponsePullback
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalColumnMomentSource
open Complex MeasureTheory
open scoped InnerProductSpace
open OriginalRieszSource
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
namespace Prior
export FiniteMobiusResolventFlux.Prior (coordinate coordinate_value originalK)
end Prior

def sourceBandPrice (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) (h : ℝ) : ℂ :=
  OriginalPrimitiveRankBalance.reverseMassCoefficient coordinate value*bandMass coordinate h+
    OriginalPrimitiveRankBalance.reversePowerCoefficient coordinate value*bandPower coordinate h

theorem original_reverse_band_source (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
    OriginalPrimitiveRankBalance.twoMomentPrice coordinate value h=sourceBandPrice coordinate value h := by
  unfold OriginalPrimitiveRankBalance.twoMomentPrice sourceBandPrice
  rw [original_mass_source coordinate h nonnegative bounded,original_power_source coordinate h nonnegative bounded]

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat,observation.coordinate=-2*(n+1))
variable (half : CenteredGram.IntegralGraphJointAction.OriginalKCombCalculation.Half observation)

def generatedCompleteRead (h : ℝ) : ℂ := generatedContactRead observation nontrivial half h-
  FiniteMobiusResolventFlux.sourceA observation*
    sourceBandPrice (Prior.coordinate observation nontrivial half) (fourierL2 (Prior.originalK observation nontrivial half)) h

 theorem original_complete_action_read (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
    OriginalPrimitiveRankBalance.completeDefectRead observation nontrivial half h=generatedCompleteRead observation nontrivial half h := by
  unfold OriginalPrimitiveRankBalance.completeDefectRead generatedCompleteRead
  rw [original_primitive_contact_action,original_reverse_band_source _ _ _ nonnegative bounded]

 theorem original_correction_band_action (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
    OriginalRieszFinitePairing.CoPoisson.correctionRead (Prior.coordinate observation nontrivial half) h=
      -(OriginalRieszFiniteColumns.firstSourceRead (Prior.coordinate observation nontrivial half) h
          (burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half))+
        OriginalRieszFiniteColumns.firstSourceRead (Prior.coordinate observation nontrivial half) (-h)
          (burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half))+
        generatedCompleteRead observation nontrivial half h) := by
  rw [OriginalPrimitiveRankBalance.original_correction_two_moments _ _ _ _ nonnegative bounded,
    original_complete_action_read _ _ _ _ nonnegative bounded]

 theorem original_fixed_residual_band_action :
    -burnolPaFixedShiftResidual (Prior.coordinate observation nontrivial half)
      (by rw [Prior.coordinate_value];exact observation.mathlibZero)=
      (pairedMellinTranslationCharacter observation.coordinate (Real.log stageZeroSonineQ)-
        pairedMellinTranslationCharacter (star observation.coordinate) (Real.log stageZeroSonineQ))*
          OriginalRieszFinitePairing.kernelSelfSource (Prior.coordinate observation nontrivial half)-
      (1/2:ℂ)*star
        (OriginalRieszFiniteColumns.firstSourceRead (Prior.coordinate observation nontrivial half) (Real.log stageZeroSonineQ)
          (burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half))+
        OriginalRieszFiniteColumns.firstSourceRead (Prior.coordinate observation nontrivial half) (-(Real.log stageZeroSonineQ))
          (burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half))+
        generatedCompleteRead observation nontrivial half (Real.log stageZeroSonineQ)) := by
  have nonnegative : 0≤Real.log stageZeroSonineQ := by
    apply Real.log_nonneg
    exact Real.one_le_sqrt.mpr (by norm_num)
  have bounded := (le_abs_self (Real.log stageZeroSonineQ)).trans OriginalRieszFiniteColumns.fixedShift_small
  rw [OriginalPrimitiveRankBalance.original_fixed_residual_two_moments,
    original_complete_action_read _ _ _ _ nonnegative bounded]

end OriginalColumnMomentSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
