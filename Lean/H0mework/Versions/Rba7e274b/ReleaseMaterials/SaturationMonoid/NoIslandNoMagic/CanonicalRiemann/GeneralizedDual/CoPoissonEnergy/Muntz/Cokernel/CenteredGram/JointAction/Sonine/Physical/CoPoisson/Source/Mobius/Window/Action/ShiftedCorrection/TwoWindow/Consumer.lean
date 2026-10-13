import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.TwoWindow.Price
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalTwoWindowInverseForcing
open Complex MeasureTheory OriginalInverseReturnActionSource OriginalJointFluxSource
open scoped InnerProductSpace
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : CenteredGram.IntegralGraphJointAction.OriginalKCombCalculation.Half observation)

-- The complete old first/source/contact price consumes the independently generated source action.
theorem original_complete_forcing_action_price (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
    OriginalRieszFiniteColumns.firstSourceRead (Prior.coordinate observation nontrivial half) h
        (burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half))+
      OriginalRieszFiniteColumns.firstSourceRead (Prior.coordinate observation nontrivial half) (-h)
        (burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half))+
      completeInverseReturnPrice observation nontrivial half h=
      -forcingPrice (Prior.coordinate observation nontrivial half) h := by
  have generated:=OriginalRieszFinitePairing.CoPoisson.sourcePair_correction
    (Prior.coordinate observation nontrivial half)
    (by rw [Prior.coordinate_value];exact observation.mathlibZero) h nonnegative bounded
  rw [original_source_pair_forcing_price,original_correction_inverse_return_price _ _ _ _ nonnegative bounded] at generated
  linear_combination generated

theorem original_correction_forcing_action_price (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
    OriginalRieszFinitePairing.CoPoisson.correctionRead (Prior.coordinate observation nontrivial half) h=
      forcingPrice (Prior.coordinate observation nontrivial half) h := by
  rw [← OriginalRieszFinitePairing.CoPoisson.sourcePair_correction
    (Prior.coordinate observation nontrivial half)
    (by rw [Prior.coordinate_value];exact observation.mathlibZero) h nonnegative bounded,
    original_source_pair_forcing_price]

theorem original_fixed_residual_forcing_action_price :
    -burnolPaFixedShiftResidual (Prior.coordinate observation nontrivial half)
      (by rw [Prior.coordinate_value];exact observation.mathlibZero)=
      (pairedMellinTranslationCharacter observation.coordinate (Real.log stageZeroSonineQ)-
        pairedMellinTranslationCharacter (star observation.coordinate) (Real.log stageZeroSonineQ))*
          OriginalRieszFinitePairing.kernelSelfSource (Prior.coordinate observation nontrivial half)+
        (1/2:ℂ)*star (forcingPrice (Prior.coordinate observation nontrivial half) (Real.log stageZeroSonineQ)) := by
  rw [original_fixed_residual_inverse_return_price,original_complete_forcing_action_price _ _ _ _
    (by apply Real.log_nonneg;change 1≤Real.sqrt 3;exact Real.one_le_sqrt.mpr (by norm_num))
    ((le_abs_self _).trans OriginalRieszFiniteColumns.fixedShift_small),star_neg]
  ring

end OriginalTwoWindowInverseForcing
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
