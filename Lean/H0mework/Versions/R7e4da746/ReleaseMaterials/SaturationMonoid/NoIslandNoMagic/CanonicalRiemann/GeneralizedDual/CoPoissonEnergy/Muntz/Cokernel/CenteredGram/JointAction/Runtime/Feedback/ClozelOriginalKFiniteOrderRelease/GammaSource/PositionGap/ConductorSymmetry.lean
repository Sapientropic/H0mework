import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ConductorMoments

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.ConductorJet

open BurnolPhysicalState Filter
open OriginalGamma.Source.RelativeConductorGapReadback OriginalGamma.Source.WeightedRadialKernel
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.CutPower
open scoped InnerProductSpace Topology

open private conductor_unique from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ConductorBranches
open private right_quarter from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResolventConductor
open private gamma_pair_dilation from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.RelativeConductorGapReadback
open private gamma_pair_fourier from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.KGammaSource

local notation "R" => burnolDirectRightResolventCLM
local notation "G" => gammaR
local notation "D" => burnolMultiplicativeDilation
local notation "χ" => positiveMellinQuarterRightResolventCharacter
local notation "boundary" => burnolDirectRightResolventSignedBoundary

private def boundaryPreimage (c : BurnolCompletedMellinCoordinate) (h : ℝ) (x : BurnolL2) : BurnolL2 :=
  h⁻¹ • (D (-h/2) x - χ (c.value/2) h • x)

private theorem boundary_preimage_even (c : BurnolCompletedMellinCoordinate) (h : ℝ) (x : BurnolL2)
    (even : reflectL2 x = x) : reflectL2 (boundaryPreimage c h x) = boundaryPreimage c h x := by
  simp only [boundaryPreimage, RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul, map_sub,
    reflectL2_burnolMultiplicativeDilation, even]

private theorem boundary_preimage_graph (c : BurnolCompletedMellinCoordinate) (h : ℝ) (x g : BurnolL2)
    (paid : GammaPair x g) : GammaPair (boundaryPreimage c h x) (boundaryPreimage c h g) := by
  intro test
  simp only [boundaryPreimage, RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_right,
    inner_sub_right, paid test, gamma_pair_dilation _ _ _ paid test]

private theorem boundary_range_slope (c : BurnolCompletedMellinCoordinate) (h : ℝ) (x : BurnolL2) :
    R c (boundaryPreimage c h x) = χ (c.value/2) h • slope (boundary (c.value/2) x) 0 h := by
  have commute : R c (D (-h/2) x) = D (-h/2) (R c x) :=
    burnolDirectRightResolvent_dilation _ _ _
  have written : D (-h/2) (R c x) - χ (c.value/2) h • R c x =
      χ (c.value/2) h • boundary (c.value/2) x h :=
    burnolDirectRightResolvent_sourceBoundary _ (right_quarter c) _ _
  have atZero : boundary (c.value/2) x 0 = 0 := by
    simp [burnolDirectRightResolventSignedBoundary]
  rw [boundaryPreimage, RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul, map_sub, map_smul,
    commute, written, slope_def_module, sub_zero, atZero, sub_zero]
  rw [← RCLike.real_smul_eq_coe_smul (K := ℂ), smul_comm]

private theorem boundary_range_limit (c : BurnolCompletedMellinCoordinate) (x : BurnolL2) :
    Tendsto (fun h => R c (boundaryPreimage c h x)) (𝓝[≠] (0 : ℝ)) (𝓝 x) := by
  have deriv := (burnolDirectRightResolventSignedBoundary_hasDerivAt (c.value/2) x).tendsto_slope
  have character : Tendsto (χ (c.value/2)) (𝓝[≠] (0 : ℝ)) (𝓝 (χ (c.value/2) 0)) :=
    (positiveMellinQuarterRightResolventCharacter_hasDerivAt (c.value/2)).continuousAt.continuousWithinAt
  have origin : χ (c.value/2) 0 = 1 := by
    simp [positiveMellinQuarterRightResolventCharacter_exp]
  simpa only [← boundary_range_slope, origin, one_smul] using character.smul deriv

/-- The signed source boundary approximates both ends of each actual even conductor graph through R. -/
theorem even_conductor_symmetry (c : BurnolCompletedMellinCoordinate)
    (x gx y gy : BurnolL2) (xe : reflectL2 x = x) (ye : reflectL2 y = y)
    (xp : GammaPair x gx) (yp : GammaPair y gy) :
    inner ℂ gx y = inner ℂ x gy := by
  have read (v g : BurnolL2) (even : reflectL2 v = v) (paid : GammaPair v g) (h : ℝ) :
      G c (boundaryPreimage c h v) = R c (boundaryPreimage c h g) :=
    conductor_unique _ _ _ (actual_gamma_R c _ (boundary_preimage_even c h v even))
      (actual_Gamma_R c _ _ (boundary_preimage_graph c h v g paid))
  have symmetry (h : ℝ) :
      inner ℂ (R c (boundaryPreimage c h gx)) (R c (boundaryPreimage c h y)) =
        inner ℂ (R c (boundaryPreimage c h x)) (R c (boundaryPreimage c h gy)) := by
    rw [← read x gx xe xp h, ← read y gy ye yp h]
    exact gammaR_range_symmetry c _ _ (boundary_preimage_even c h x xe)
      (boundary_preimage_even c h y ye)
  exact tendsto_nhds_unique_of_eventuallyEq
    ((boundary_range_limit c gx).inner (boundary_range_limit c y))
    ((boundary_range_limit c x).inner (boundary_range_limit c gy))
    (Eventually.of_forall symmetry)

theorem even_conductor_value (x g : BurnolL2) (even : reflectL2 x = x)
    (paid : GammaPair x g) : reflectL2 g = g := by
  have twice := gamma_pair_fourier _ _ (gamma_pair_fourier _ _ paid)
  rw [fourierL2_fourierL2, fourierL2_fourierL2, even] at twice
  exact conductor_unique _ _ _ twice paid

end OriginalKFiniteOrderRelease.PositionGapCayley.ConductorJet
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
