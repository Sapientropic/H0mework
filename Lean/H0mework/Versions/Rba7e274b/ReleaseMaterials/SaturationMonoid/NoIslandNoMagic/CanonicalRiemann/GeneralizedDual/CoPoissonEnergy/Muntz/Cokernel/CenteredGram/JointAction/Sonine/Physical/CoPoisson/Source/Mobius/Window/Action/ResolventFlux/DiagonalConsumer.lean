import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ResolventFlux.RankedForcing
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace FiniteMobiusResolventFlux
open Complex MeasureTheory
open scoped InnerProductSpace
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat,observation.coordinate=-2*(n+1))
variable (half : CenteredGram.IntegralGraphJointAction.OriginalKCombCalculation.Half observation)

-- This consumes the original physical residual, the complete columns, and the source-built vector.
theorem original_fixed_residual_ranked :
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
        inner ℂ (burnolAnnulusSamplingL2 (OriginalRieszFiniteColumns.fourierColumn (Prior.coordinate observation nontrivial half) (Real.log stageZeroSonineQ)) 0+
          burnolAnnulusSamplingL2 (OriginalRieszFiniteColumns.fourierColumn (Prior.coordinate observation nontrivial half) (-(Real.log stageZeroSonineQ))) 0)
          (rankedSourceDefect observation nontrivial half)) := by
  have zero : riemannZeta (Prior.coordinate observation nontrivial half).value=0 := by
    rw [Prior.coordinate_value]
    exact observation.mathlibZero
  have source := OriginalRieszFinitePairing.CoPoisson.fixed_correction (Prior.coordinate observation nontrivial half) zero
  have nonnegative : 0≤Real.log stageZeroSonineQ := by
    apply Real.log_nonneg
    change 1≤Real.sqrt 3
    exact Real.one_le_sqrt.mpr (by norm_num)
  have bounded : Real.log stageZeroSonineQ≤Real.log 2 := (le_abs_self _).trans OriginalRieszFiniteColumns.fixedShift_small
  rw [original_correction_ranked observation nontrivial half _ nonnegative bounded,star_neg,Prior.coordinate_value] at source
  simpa only [mul_neg,sub_eq_add_neg] using source

end FiniteMobiusResolventFlux
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
