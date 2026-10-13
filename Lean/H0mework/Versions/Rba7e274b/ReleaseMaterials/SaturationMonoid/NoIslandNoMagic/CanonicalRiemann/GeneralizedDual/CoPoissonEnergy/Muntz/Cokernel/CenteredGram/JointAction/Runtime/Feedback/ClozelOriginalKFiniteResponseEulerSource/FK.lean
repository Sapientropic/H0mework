import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteResponseEulerSource.Read
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFiniteResponseEulerSource
open Complex MeasureTheory Set Filter SourceGeneratedHilbertCokernel
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
namespace Paid
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.FiniteMobiusResolventFlux (actualMean Rplus RplusIntegrand Rplus_integrable)
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalJointFluxSource (actual_mean_source_integral actual_mean_dilation_source source_weight_mean_phase)
end Paid
local notation "q" => (1/4:ℝ)

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

def actualFiniteEulerFKPrice (n : Nat) (h shift : ℝ) : ℂ:=
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let dual:=OriginalKQuarterTailPhysicalSource.actualStarSource coordinate
 let material:=OriginalKGapMeanRSourceAction.Full.meanDebt coordinate h
 let rate:=star (dual.value-1/2)
 (star (OriginalRieszSource.Kernel.A coordinate)/2)*
  (actualFiniteEulerVPrice dual n material/rate)-
 (star (OriginalRieszSource.Kernel.beta coordinate)/2)*
  (actualFiniteEulerUPrice dual n material/rate)+
 OriginalKResponseCofinalSourceAction.actualRetainedFKStock observation nontrivial half h shift

/-- Actual finite source action generates its FK price; no independent finite Jordan price is supplied. -/
theorem actual_finite_Euler_FK_price (n : Nat) (h shift : ℝ) (nonnegative : 0≤shift) :
 OriginalKResponseCofinalSourceAction.actualFiniteFKPrice observation nontrivial half n h shift=
 actualFiniteEulerFKPrice observation nontrivial half n h shift :=by
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let dual:=OriginalKQuarterTailPhysicalSource.actualStarSource coordinate
 let material:=OriginalKGapMeanRSourceAction.Full.meanDebt coordinate h
 have rate:star (dual.value-1/2)≠0:=by
  intro zero
  apply actual_source_rate_nonzero dual
  have reflected:=congrArg (starRingEnd ℂ) zero
  simpa only [starRingEnd_apply,star_star,star_zero] using reflected
 have u:=actual_U_Jordan_Euler_price dual n material
 have v:=actual_V_Jordan_Euler_price dual n material
 have uprice:actualFiniteEulerJordanPrice dual (actualWholeU n) material=
  actualFiniteEulerUPrice dual n material/star (dual.value-1/2):=
  (eq_div_iff rate).mpr (by simpa only [mul_comm] using u)
 have vprice:actualFiniteEulerJordanPrice dual (actualWholeV n) material=
  actualFiniteEulerVPrice dual n material/star (dual.value-1/2):=
  (eq_div_iff rate).mpr (by simpa only [mul_comm] using v)
 unfold OriginalKResponseCofinalSourceAction.actualFiniteFKPrice actualFiniteEulerFKPrice
 dsimp only
 rw [actual_finite_U_Jordan_read observation nontrivial half n h shift nonnegative,
  actual_finite_V_Jordan_read observation nontrivial half n h shift nonnegative]
 change _=(star (OriginalRieszSource.Kernel.A coordinate)/2)*(actualFiniteEulerVPrice dual n material/star (dual.value-1/2))-
  (star (OriginalRieszSource.Kernel.beta coordinate)/2)*(actualFiniteEulerUPrice dual n material/star (dual.value-1/2))+
  OriginalKResponseCofinalSourceAction.actualRetainedFKStock observation nontrivial half h shift
 rw [uprice,vprice]

/-- The original source retains the exact controlled residual after consuming the stronger finite action. -/
theorem actual_original_FK_Euler_source_price (n : Nat) (h shift : ℝ) (nonnegative : 0≤shift) :
 OriginalKCompactJordanRankSource.actualCompactJordanFKMeanPrice observation nontrivial half h shift=
 actualFiniteEulerFKPrice observation nontrivial half n h shift+
 OriginalKResponseCofinalSourceAction.actualFKResidual observation nontrivial half n h shift :=by
 rw [←actual_finite_Euler_FK_price observation nontrivial half n h shift nonnegative]
 exact OriginalKResponseCofinalSourceAction.actual_original_FK_finite_price observation nontrivial half n h shift

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFiniteResponseEulerSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
