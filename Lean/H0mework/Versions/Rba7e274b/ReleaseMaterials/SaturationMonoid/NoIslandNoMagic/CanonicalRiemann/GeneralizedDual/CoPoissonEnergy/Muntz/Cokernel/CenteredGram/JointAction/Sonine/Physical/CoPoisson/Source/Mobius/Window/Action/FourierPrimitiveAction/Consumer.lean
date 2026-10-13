import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.FourierPrimitiveAction.Price
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalFourierPrimitiveActionSource
open Complex MeasureTheory
open scoped InnerProductSpace
open OriginalRieszSource
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
namespace Prior
export OriginalPrimitiveActionSource.Prior (coordinate coordinate_value originalK)
end Prior
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat,observation.coordinate=-2*(n+1))
variable (half : CenteredGram.IntegralGraphJointAction.OriginalKCombCalculation.Half observation)

def completeFPContactPrice (h : ℝ) : ℂ :=
  -sourceContactPrice (Prior.coordinate observation nontrivial half) h-
  (1/2:ℂ)*(OriginalColumnMomentSource.generatedResponseRead (Prior.coordinate observation nontrivial half) h+
    inner ℂ (OriginalColumnMomentSource.Paid.pairedColumn (Prior.coordinate observation nontrivial half) h)
      (-(burnolTateReciprocalL2 (OriginalContactFeedbackSource.generatedCombinedReturn (Prior.coordinate observation nontrivial half)))+
        OriginalReturnResponseSource.generatedReturnDefect (Prior.coordinate observation nontrivial half))-
    (2*(star (Prior.coordinate observation nontrivial half).value-1/2)*Kernel.beta (Prior.coordinate observation nontrivial half))*
      OriginalPrimitiveActionSource.primitiveReturnPrice (Prior.coordinate observation nontrivial half) h)+
  inner ℂ (OriginalColumnMomentSource.Paid.pairedColumn (Prior.coordinate observation nontrivial half) h)
    (OriginalColumnMomentSource.S.inverseAction (observation.coordinate/2) (star observation.coordinate/2)
      (OriginalColumnMomentSource.contactFluxSource observation nontrivial half))-
  FiniteMobiusResolventFlux.sourceA observation*OriginalColumnMomentSource.sourceBandPrice
    (Prior.coordinate observation nontrivial half) (fourierL2 (Prior.originalK observation nontrivial half)) h

theorem original_complete_FP_contact_price (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
    OriginalPrimitiveActionSource.completePrimitivePrice observation nontrivial half h=completeFPContactPrice observation nontrivial half h := by
  unfold OriginalPrimitiveActionSource.completePrimitivePrice completeFPContactPrice
  rw [original_contact_source_price _ _ nonnegative bounded]

theorem original_correction_FP_contact_price (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
    OriginalRieszFinitePairing.CoPoisson.correctionRead (Prior.coordinate observation nontrivial half) h=
      -(OriginalRieszFiniteColumns.firstSourceRead (Prior.coordinate observation nontrivial half) h
          (burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half))+
        OriginalRieszFiniteColumns.firstSourceRead (Prior.coordinate observation nontrivial half) (-h)
          (burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half))+
        completeFPContactPrice observation nontrivial half h) := by
  rw [OriginalPrimitiveActionSource.original_correction_primitive_price _ _ _ _ nonnegative bounded,
    original_complete_FP_contact_price _ _ _ _ nonnegative bounded]

theorem original_fixed_residual_FP_contact_price :
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
        completeFPContactPrice observation nontrivial half (Real.log stageZeroSonineQ)) := by
  rw [OriginalPrimitiveActionSource.original_fixed_residual_primitive_price,
    original_complete_FP_contact_price _ _ _ _
      (by apply Real.log_nonneg;change 1≤Real.sqrt 3;exact Real.one_le_sqrt.mpr (by norm_num))
      ((le_abs_self _).trans OriginalRieszFiniteColumns.fixedShift_small)]
end OriginalFourierPrimitiveActionSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
