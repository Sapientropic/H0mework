import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.JointFlux.Joint
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalJointFluxSource
open Complex MeasureTheory
open scoped InnerProductSpace
open OriginalRieszSource
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat,observation.coordinate=-2*(n+1))
variable (half : CenteredGram.IntegralGraphJointAction.OriginalKCombCalculation.Half observation)

def completeJointFluxPrice (h : ℝ) : ℂ :=
  -OriginalFourierPrimitiveActionSource.sourceContactPrice (Prior.coordinate observation nontrivial half) h-
  (1/2:ℂ)*(OriginalColumnMomentSource.generatedResponseRead (Prior.coordinate observation nontrivial half) h-
    (2:ℂ)*inner ℂ (OriginalPrimitiveRankBalance.pairedColumn (Prior.coordinate observation nontrivial half) h)
      (burnolTateReciprocalL2 (Paid.M (OriginalContactFeedbackSource.sourceField (Prior.coordinate observation nontrivial half))))+
    YMeanCoefficient (Prior.coordinate observation nontrivial half)*inner ℂ
      (OriginalPrimitiveRankBalance.pairedColumn (Prior.coordinate observation nontrivial half) h) (burnolTateReciprocalL2 (Paid.box 4))-
    (2:ℂ)*inner ℂ (OriginalPrimitiveRankBalance.pairedColumn (Prior.coordinate observation nontrivial half) h)
      (Paid.D (OriginalReturnResponseSource.correctedReturn (Prior.coordinate observation nontrivial half)))-
    ErFluxPrice (Prior.coordinate observation nontrivial half) h-
    (2*(star (Prior.coordinate observation nontrivial half).value-1/2)*Kernel.beta (Prior.coordinate observation nontrivial half))*
      OriginalPrimitiveActionSource.primitiveReturnPrice (Prior.coordinate observation nontrivial half) h)+
  contactJointPrice observation nontrivial half h-
  FiniteMobiusResolventFlux.sourceA observation*OriginalColumnMomentSource.sourceBandPrice
    (Prior.coordinate observation nontrivial half) (fourierL2 (Prior.originalK observation nontrivial half)) h

theorem original_complete_joint_flux_price (h : ℝ) :
    OriginalFourierPrimitiveActionSource.completeFPContactPrice observation nontrivial half h=completeJointFluxPrice observation nontrivial half h := by
  unfold OriginalFourierPrimitiveActionSource.completeFPContactPrice completeJointFluxPrice
  unfold OriginalContactFeedbackSource.generatedCombinedReturn OriginalReturnResponseSource.generatedReturnDefect
  simp only [map_sub,map_smul,inner_add_right,inner_sub_right,inner_neg_right,inner_smul_right]
  rw [original_Y_flux_price,original_Er_flux_price,original_contact_joint_price]
  ring

theorem original_correction_joint_flux_price (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
    OriginalRieszFinitePairing.CoPoisson.correctionRead (Prior.coordinate observation nontrivial half) h=
      -(OriginalRieszFiniteColumns.firstSourceRead (Prior.coordinate observation nontrivial half) h
          (burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half))+
        OriginalRieszFiniteColumns.firstSourceRead (Prior.coordinate observation nontrivial half) (-h)
          (burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half))+
        completeJointFluxPrice observation nontrivial half h) := by
  rw [OriginalFourierPrimitiveActionSource.original_correction_FP_contact_price _ _ _ _ nonnegative bounded,
    original_complete_joint_flux_price]

theorem original_fixed_residual_joint_flux_price :
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
        completeJointFluxPrice observation nontrivial half (Real.log stageZeroSonineQ)) := by
  rw [OriginalFourierPrimitiveActionSource.original_fixed_residual_FP_contact_price,original_complete_joint_flux_price]
end OriginalJointFluxSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
