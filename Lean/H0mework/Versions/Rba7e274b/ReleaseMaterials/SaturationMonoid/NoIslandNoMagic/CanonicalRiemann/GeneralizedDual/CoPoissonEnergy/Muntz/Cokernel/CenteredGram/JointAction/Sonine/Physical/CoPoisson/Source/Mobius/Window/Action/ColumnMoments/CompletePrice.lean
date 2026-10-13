import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ColumnMoments.VolterraPrice
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ColumnMoments.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalColumnMomentSource
open Complex MeasureTheory
open scoped InnerProductSpace
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat,observation.coordinate=-2*(n+1))
variable (half : CenteredGram.IntegralGraphJointAction.OriginalKCombCalculation.Half observation)

def sourceContactPrice (h : ℝ) : ℂ :=
  -inner ℂ (Paid.pairedColumn (Prior.coordinate observation nontrivial half) h)
    (S.D (FiniteMobiusResolventFlux.S.contactCorrection (Prior.coordinate observation nontrivial half)))-
  (1/2:ℂ)*(generatedResponseRead (Prior.coordinate observation nontrivial half) h+
    inner ℂ (Paid.pairedColumn (Prior.coordinate observation nontrivial half) h)
      (S.Rplus (star observation.coordinate/2) (etaRemainingSource (Prior.coordinate observation nontrivial half))))+
  inner ℂ (Paid.pairedColumn (Prior.coordinate observation nontrivial half) h)
    (S.inverseAction (observation.coordinate/2) (star observation.coordinate/2) (contactFluxSource observation nontrivial half))

def completeSourcePrice (h : ℝ) : ℂ := sourceContactPrice observation nontrivial half h-
  FiniteMobiusResolventFlux.sourceA observation*
    sourceBandPrice (Prior.coordinate observation nontrivial half) (fourierL2 (Prior.originalK observation nontrivial half)) h

-- The actual Volterra action, finite inventory, endpoint beta and means are consumed by the original complete price.
theorem original_complete_source_price (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
    OriginalPrimitiveRankBalance.completeDefectRead observation nontrivial half h=completeSourcePrice observation nontrivial half h := by
  rw [original_complete_action_read _ _ _ _ nonnegative bounded]
  unfold generatedCompleteRead completeSourcePrice generatedContactRead sourceContactPrice
  have coordinate := Prior.coordinate_value observation nontrivial half
  have right : 1/4<(star observation.coordinate/2).re := by rw [Complex.div_re];norm_num [Complex.star_def];linarith [half.down]
  have source := original_eta_Rplus_action (Prior.coordinate observation nontrivial half) (star observation.coordinate/2) right
  rw [source,inner_add_right]
  have price := original_Rplus_response_read (Prior.coordinate observation nontrivial half) h nonnegative bounded
  rw [coordinate] at price
  rw [price]

 theorem original_correction_source_price (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
    OriginalRieszFinitePairing.CoPoisson.correctionRead (Prior.coordinate observation nontrivial half) h=
      -(OriginalRieszFiniteColumns.firstSourceRead (Prior.coordinate observation nontrivial half) h
          (burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half))+
        OriginalRieszFiniteColumns.firstSourceRead (Prior.coordinate observation nontrivial half) (-h)
          (burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half))+
        completeSourcePrice observation nontrivial half h) := by
  rw [OriginalPrimitiveRankBalance.original_correction_two_moments _ _ _ _ nonnegative bounded,
    original_complete_source_price _ _ _ _ nonnegative bounded]

 theorem original_fixed_residual_source_price :
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
        completeSourcePrice observation nontrivial half (Real.log stageZeroSonineQ)) := by
  have nonnegative : 0≤Real.log stageZeroSonineQ := by apply Real.log_nonneg;exact Real.one_le_sqrt.mpr (by norm_num)
  have bounded := (le_abs_self (Real.log stageZeroSonineQ)).trans OriginalRieszFiniteColumns.fixedShift_small
  rw [OriginalPrimitiveRankBalance.original_fixed_residual_two_moments,
    original_complete_source_price _ _ _ _ nonnegative bounded]

end OriginalColumnMomentSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
