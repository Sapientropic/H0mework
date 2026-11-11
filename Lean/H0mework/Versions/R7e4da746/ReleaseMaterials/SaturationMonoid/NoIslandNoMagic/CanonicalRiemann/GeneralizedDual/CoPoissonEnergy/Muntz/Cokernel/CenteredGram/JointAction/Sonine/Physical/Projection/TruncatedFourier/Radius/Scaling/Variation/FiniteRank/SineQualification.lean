import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.TruncatedFourier.Radius.Scaling.Variation.FiniteRank.EvenSource
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace FixedWindowFourierReaction
open Complex MeasureTheory Set
open scoped InnerProductSpace

theorem sine_odd (r : ℝ) : reflectRestricted 1 (s r) = -s r := by
  have reflectedRaw := (negMeasurePreserving_restrict 1).quasiMeasurePreserving.ae_eq (s_coe r)
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (s r) (negMeasurePreserving_restrict 1),
    reflectedRaw,s_coe r,Lp.coeFn_neg (s r)] with x reflected raw direct negative
  change (reflectRestricted 1 (s r) : ℝ→ℂ) x = (s r : ℝ→ℂ) (-x) at reflected
  change (s r : ℝ→ℂ) (-x) = sineRaw r (-x) at raw
  rw [reflected,raw,negative]
  simp only [Pi.neg_apply,direct,sineRaw]
  rw [show 2*Real.pi*r^2*(-x)=-(2*Real.pi*r^2*x) by ring,Real.sin_neg]
  push_cast
  ring

theorem sine_even_pair_zero (r : ℝ) (x : H) (fixed : reflectRestricted 1 x = x) : inner ℂ (s r) x = 0 := by
  have pair := (reflectRestricted 1).inner_map_map (s r) x
  rw [sine_odd,fixed,inner_neg_left] at pair
  linear_combination -1/2 * pair

theorem sine_mean_zero (r : ℝ) : Q (s r) = s r := by
  have orthogonal := sine_even_pair_zero r e (reflectRestricted_intervalConstant 1)
  have reversed : inner ℂ e (s r) = 0 := by
    rw [← inner_conj_symm]
    rw [orthogonal]
    simp
  rw [Q_read]
  simp only [InnerProductSpace.rankOne_apply,reversed,zero_smul,smul_zero,sub_zero]

theorem original_source_sine_zero (coordinate : BurnolCompletedMellinCoordinate) (r : ℝ) :
    inner ℂ (s r) (originalB coordinate) = 0 := sine_even_pair_zero r _ (original_source_even coordinate)

end FixedWindowFourierReaction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
