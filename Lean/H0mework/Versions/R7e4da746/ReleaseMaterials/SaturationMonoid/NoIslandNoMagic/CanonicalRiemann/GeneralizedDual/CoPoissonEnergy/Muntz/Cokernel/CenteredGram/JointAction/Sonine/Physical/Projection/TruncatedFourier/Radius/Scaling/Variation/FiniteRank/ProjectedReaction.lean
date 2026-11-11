import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.TruncatedFourier.Radius.Scaling.Variation.FiniteRank.SineQualification
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace FixedWindowFourierReaction
open Complex MeasureTheory Set
open scoped InnerProductSpace

theorem projected_reaction (r : ℝ) (f : H) : Q (rawReaction r (Q f)) = centeredReaction r f := by
  unfold rawReaction centeredReaction
  simp only [smul_apply,sub_apply,InnerProductSpace.rankOne_apply,map_smul,map_sub]
  have pair (x y : H) : inner ℂ x (Q y)=inner ℂ (Q x) y := (Q_symmetric x y).symm
  rw [pair,pair]

theorem centered_finite_complete (q r : ℝ) (f : H) : finiteReaction q r f =
    (∫ t : ℝ in q..r,centeredReaction t f)-
      (1/2 : ℂ) • (InnerProductSpace.rankOne ℂ (p r) (p r) f-InnerProductSpace.rankOne ℂ (p q) (p q) f) := by
  unfold finiteReaction
  rw [← Q.intervalIntegral_comp_comm ((reaction_continuous (Q f)).intervalIntegrable q r)]
  simp only [projected_reaction]

theorem original_source_centered_reaction (coordinate : BurnolCompletedMellinCoordinate) (r : ℝ) :
    centeredReaction r (originalB coordinate) = (r:ℂ) •
      (InnerProductSpace.rankOne ℂ (Q (c r)) (Q (c r)) (originalB coordinate)) := by
  unfold centeredReaction
  simp only [smul_apply,sub_apply,InnerProductSpace.rankOne_apply]
  rw [sine_mean_zero,original_source_sine_zero,zero_smul,sub_zero]

theorem original_inverse_complete_reaction (coordinate : BurnolCompletedMellinCoordinate) (r : ℝ) (positive : 0<r) :
    originalB coordinate-centeredSquare r (originalB coordinate) = originalForcing coordinate-
      ((∫ t : ℝ in (1/4:ℝ)..r,(t:ℂ) •
          (InnerProductSpace.rankOne ℂ (Q (c t)) (Q (c t)) (originalB coordinate)))-
       (1/2 : ℂ) • (InnerProductSpace.rankOne ℂ (p r) (p r) (originalB coordinate)-
         InnerProductSpace.rankOne ℂ (p (1/4)) (p (1/4)) (originalB coordinate))) := by
  rw [original_inverse_finite_reaction coordinate r positive,centered_finite_complete]
  simp only [original_source_centered_reaction]

end FixedWindowFourierReaction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
