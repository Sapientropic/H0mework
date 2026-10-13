import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.CoupledPrice
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalInverseReturnActionSource
open Complex MeasureTheory
open scoped InnerProductSpace
open OriginalRieszSource OriginalJointFluxSource
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat,observation.coordinate=-2*(n+1))
variable (half : CenteredGram.IntegralGraphJointAction.OriginalKCombCalculation.Half observation)
def completeInverseReturnPrice (h : ℝ) : ℂ :=
  -OriginalFourierPrimitiveActionSource.sourceContactPrice (Prior.coordinate observation nontrivial half) h-
  (1/2:ℂ)*(OriginalColumnMomentSource.generatedResponseRead (Prior.coordinate observation nontrivial half) h+
    YMeanCoefficient (Prior.coordinate observation nontrivial half)*inner ℂ
      (OriginalPrimitiveRankBalance.pairedColumn (Prior.coordinate observation nontrivial half) h) (burnolTateReciprocalL2 (OriginalJointFluxSource.Paid.box 4))-
    ErFluxPrice (Prior.coordinate observation nontrivial half) h-
    (2*(star (Prior.coordinate observation nontrivial half).value-1/2)*Kernel.beta (Prior.coordinate observation nontrivial half))*
      OriginalPrimitiveActionSource.primitiveReturnPrice (Prior.coordinate observation nontrivial half) h)+
  coupledReturnSourcePrice (Prior.coordinate observation nontrivial half) h+
  contactJointPrice observation nontrivial half h-
  FiniteMobiusResolventFlux.sourceA observation*OriginalColumnMomentSource.sourceBandPrice
    (Prior.coordinate observation nontrivial half) (fourierL2 (Prior.originalK observation nontrivial half)) h

theorem original_complete_inverse_return_price (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
    OriginalJointFluxSource.completeJointFluxPrice observation nontrivial half h=completeInverseReturnPrice observation nontrivial half h := by
  have source:=original_coupled_return_source_price (Prior.coordinate observation nontrivial half) h nonnegative bounded
  unfold OriginalJointFluxSource.completeJointFluxPrice completeInverseReturnPrice
  linear_combination source

theorem original_correction_inverse_return_price (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
    OriginalRieszFinitePairing.CoPoisson.correctionRead (Prior.coordinate observation nontrivial half) h=
      -(OriginalRieszFiniteColumns.firstSourceRead (Prior.coordinate observation nontrivial half) h
          (burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half))+
        OriginalRieszFiniteColumns.firstSourceRead (Prior.coordinate observation nontrivial half) (-h)
          (burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half))+
        completeInverseReturnPrice observation nontrivial half h) := by
  rw [OriginalJointFluxSource.original_correction_joint_flux_price _ _ _ _ nonnegative bounded,
    original_complete_inverse_return_price _ _ _ _ nonnegative bounded]

theorem original_fixed_residual_inverse_return_price :
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
        completeInverseReturnPrice observation nontrivial half (Real.log stageZeroSonineQ)) := by
  rw [OriginalJointFluxSource.original_fixed_residual_joint_flux_price,original_complete_inverse_return_price _ _ _ _
    (by apply Real.log_nonneg;change 1≤Real.sqrt 3;exact Real.one_le_sqrt.mpr (by norm_num))
    ((le_abs_self _).trans OriginalRieszFiniteColumns.fixedShift_small)]
end OriginalInverseReturnActionSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
