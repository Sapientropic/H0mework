import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.PrimitiveRank.TwoMoments
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ResolventFlux.DiagonalConsumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPrimitiveRankBalance
open Complex MeasureTheory
open scoped InnerProductSpace
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
namespace Prior
export FiniteMobiusResolventFlux.Prior (coordinate coordinate_value originalK)
end Prior
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat,observation.coordinate=-2*(n+1))
variable (half : CenteredGram.IntegralGraphJointAction.OriginalKCombCalculation.Half observation)

def primitiveRead (h : ℝ) : ℂ := inner ℂ (pairedColumn (Prior.coordinate observation nontrivial half) h)
  (inverseAction (observation.coordinate/2) (star observation.coordinate/2) (Source.D (Source.primitiveSource observation nontrivial half)))

def completeDefectRead (h : ℝ) : ℂ := primitiveRead observation nontrivial half h-Source.sourceA observation*
  twoMomentPrice (Prior.coordinate observation nontrivial half) (fourierL2 (Prior.originalK observation nontrivial half)) h

theorem original_defect_two_moments (h : ℝ) :
    inner ℂ (pairedColumn (Prior.coordinate observation nontrivial half) h)
      (Source.rankedSourceDefect observation nontrivial half)=completeDefectRead observation nontrivial half h := by
  rw [original_rank_defect_read]
  have source := reverse_source_two_moments (Prior.coordinate observation nontrivial half)
    (fourierL2 (Prior.originalK observation nontrivial half)) h
  rw [Prior.coordinate_value] at source
  rw [source]
  rfl

-- Every physical source term remains; only the source-proved rank-action inputs are removed.
theorem original_correction_two_moments (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
    OriginalRieszFinitePairing.CoPoisson.correctionRead (Prior.coordinate observation nontrivial half) h=
      -(OriginalRieszFiniteColumns.firstSourceRead (Prior.coordinate observation nontrivial half) h
          (burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half))+
        OriginalRieszFiniteColumns.firstSourceRead (Prior.coordinate observation nontrivial half) (-h)
          (burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half))+
        completeDefectRead observation nontrivial half h) := by
  have source := FiniteMobiusResolventFlux.original_correction_ranked observation nontrivial half h nonnegative bounded
  change _=-(OriginalRieszFiniteColumns.firstSourceRead _ _ _+
    OriginalRieszFiniteColumns.firstSourceRead _ _ _+inner ℂ (pairedColumn (Prior.coordinate observation nontrivial half) h)
    (Source.rankedSourceDefect observation nontrivial half)) at source
  rw [original_defect_two_moments] at source
  exact source

 theorem original_fixed_residual_two_moments :
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
        completeDefectRead observation nontrivial half (Real.log stageZeroSonineQ)) := by
  have source := FiniteMobiusResolventFlux.original_fixed_residual_ranked observation nontrivial half
  change _=(_)- (1/2:ℂ)*star
    (OriginalRieszFiniteColumns.firstSourceRead _ _ _+OriginalRieszFiniteColumns.firstSourceRead _ _ _+
      inner ℂ (pairedColumn (Prior.coordinate observation nontrivial half) (Real.log stageZeroSonineQ))
      (Source.rankedSourceDefect observation nontrivial half)) at source
  rw [original_defect_two_moments] at source
  exact source

end OriginalPrimitiveRankBalance
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
