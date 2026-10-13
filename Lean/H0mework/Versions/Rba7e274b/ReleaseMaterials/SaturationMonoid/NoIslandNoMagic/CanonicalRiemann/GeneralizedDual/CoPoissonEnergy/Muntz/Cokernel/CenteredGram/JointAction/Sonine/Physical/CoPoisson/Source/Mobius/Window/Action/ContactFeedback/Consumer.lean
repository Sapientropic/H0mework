import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ContactFeedback.Group
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalContactFeedbackSource
open Complex MeasureTheory
open scoped InnerProductSpace
open OriginalRieszSource
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
namespace Prior
export OriginalFourierMobiusReturnSource.Prior (coordinate coordinate_value originalK)
end Prior
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat,observation.coordinate=-2*(n+1))
variable (half : CenteredGram.IntegralGraphJointAction.OriginalKCombCalculation.Half observation)

def completeContactPrice (h : ℝ) : ℂ :=
  -inner ℂ (OriginalColumnMomentSource.Paid.pairedColumn (Prior.coordinate observation nontrivial half) h)
    (Paid.D (FiniteMobiusResolventFlux.S.contactCorrection (Prior.coordinate observation nontrivial half)))-
  (1/2:ℂ)*(OriginalColumnMomentSource.generatedResponseRead (Prior.coordinate observation nontrivial half) h+
    inner ℂ (OriginalColumnMomentSource.Paid.pairedColumn (Prior.coordinate observation nontrivial half) h)
      (generatedContactAction (Prior.coordinate observation nontrivial half)))+
  inner ℂ (OriginalColumnMomentSource.Paid.pairedColumn (Prior.coordinate observation nontrivial half) h)
    (OriginalColumnMomentSource.S.inverseAction (observation.coordinate/2) (star observation.coordinate/2)
      (OriginalColumnMomentSource.contactFluxSource observation nontrivial half))-
  FiniteMobiusResolventFlux.sourceA observation*
    OriginalColumnMomentSource.sourceBandPrice (Prior.coordinate observation nontrivial half)
      (fourierL2 (Prior.originalK observation nontrivial half)) h

theorem original_complete_contact_price (h : ℝ) :
    OriginalFourierMobiusReturnSource.completeFourierReturnPrice observation nontrivial half h=completeContactPrice observation nontrivial half h := by
  unfold OriginalFourierMobiusReturnSource.completeFourierReturnPrice completeContactPrice
  rw [original_complete_contact_action]

theorem original_correction_contact_price (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
    OriginalRieszFinitePairing.CoPoisson.correctionRead (Prior.coordinate observation nontrivial half) h=
      -(OriginalRieszFiniteColumns.firstSourceRead (Prior.coordinate observation nontrivial half) h
          (burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half))+
        OriginalRieszFiniteColumns.firstSourceRead (Prior.coordinate observation nontrivial half) (-h)
          (burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half))+
        completeContactPrice observation nontrivial half h) := by
  rw [OriginalFourierMobiusReturnSource.original_correction_fourier_return_price _ _ _ _ nonnegative bounded,original_complete_contact_price]

theorem original_fixed_residual_contact_price :
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
        completeContactPrice observation nontrivial half (Real.log stageZeroSonineQ)) := by
  rw [OriginalFourierMobiusReturnSource.original_fixed_residual_fourier_return_price,original_complete_contact_price]

end OriginalContactFeedbackSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
