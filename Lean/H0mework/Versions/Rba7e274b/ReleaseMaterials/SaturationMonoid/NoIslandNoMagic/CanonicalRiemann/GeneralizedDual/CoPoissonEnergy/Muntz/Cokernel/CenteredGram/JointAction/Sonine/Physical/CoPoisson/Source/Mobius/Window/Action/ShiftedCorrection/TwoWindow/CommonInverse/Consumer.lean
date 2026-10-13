import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.TwoWindow.CommonInverse.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalCommonInverseForcing
open Complex MeasureTheory OriginalInverseReturnActionSource OriginalJointFluxSource
open scoped InnerProductSpace
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : CenteredGram.IntegralGraphJointAction.OriginalKCombCalculation.Half observation)

theorem original_complete_common_inverse_price (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
    OriginalRieszFiniteColumns.firstSourceRead (Prior.coordinate observation nontrivial half) h
        (burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half))+
      OriginalRieszFiniteColumns.firstSourceRead (Prior.coordinate observation nontrivial half) (-h)
        (burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half))+
      completeInverseReturnPrice observation nontrivial half h=
      -(generatedJointSource (Prior.coordinate observation nontrivial half) h nonnegative).price := by
  rw [generated_joint_source_price]
  exact OriginalTwoWindowInverseForcing.original_complete_forcing_action_price observation nontrivial half h nonnegative bounded

theorem original_fixed_residual_common_inverse_price :
    -burnolPaFixedShiftResidual (Prior.coordinate observation nontrivial half)
      (by rw [Prior.coordinate_value];exact observation.mathlibZero)=
      (pairedMellinTranslationCharacter observation.coordinate (Real.log stageZeroSonineQ)-
        pairedMellinTranslationCharacter (star observation.coordinate) (Real.log stageZeroSonineQ))*
          OriginalRieszFinitePairing.kernelSelfSource (Prior.coordinate observation nontrivial half)+
        (1/2:ℂ)*star ((generatedJointSource (Prior.coordinate observation nontrivial half)
          (Real.log stageZeroSonineQ)
          (by apply Real.log_nonneg;change 1≤Real.sqrt 3;exact Real.one_le_sqrt.mpr (by norm_num))).price) := by
  rw [generated_joint_source_price]
  exact OriginalTwoWindowInverseForcing.original_fixed_residual_forcing_action_price observation nontrivial half

end OriginalCommonInverseForcing
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
