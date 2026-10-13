import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPositionQuarterFTCAction.FTC
import H0mework.Versions.V2.Arithmetic.RiemannNativeCurrent.UnitResponseRadius
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPositionQuarterFTCAction
open Complex MeasureTheory Set Filter SourceGeneratedHilbertCokernel
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
namespace Paid
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.FiniteMobiusResolventFlux (actualMean)
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalJointFluxSource (actual_mean_source_integral actual_mean_dilation_source)
end Paid
local notation "q" => (1/4:ℝ)

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

private theorem actual_compact_mean_integral (material : BurnolL2)
 (supported : originalPhysicalCutoff q material=material) :
 Paid.actualMean material=(2:ℂ)*(∫ x : ℝ,material x) := by
 have source:=originalPhysicalCutoff_coeFn q material
 rw [supported] at source
 rw [Paid.actual_mean_source_integral]
 have integralSource : (∫ x : ℝ,material x)=(∫ x : ℝ in symmetricInterval q,material x) := by
  rw [←integral_indicator (measurableSet_symmetricInterval q)]
  exact integral_congr_ae source
 rw [integralSource]

/-- Actual inside and exterior restrictions of the same zero-mass columns produce the original seed mean. -/
theorem actual_position_source_seed_mean (h : ℝ) (nonnegative : 0≤h) :
 Paid.actualMean (OriginalKInsideDebtRSource.actualInsidePosition observation nontrivial half h)=
 -(2:ℂ)*(∫ x : ℝ,OriginalRieszFinitePairing.CoPoisson.positionSeed
   (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h x) := by
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let inside:=OriginalKInsideDebtRSource.actualInsidePosition observation nontrivial half h
 let seed:=OriginalRieszFinitePairing.CoPoisson.positionSeed coordinate h
 have supported:= (OriginalKInsideDebtRSource.actual_inside_columns_quarter observation nontrivial half h nonnegative).1
 rw [actual_compact_mean_integral inside supported]
 have insideIntegrable : Integrable (inside : ℝ→ℂ) := by
  exact ((OriginalRieszFiniteColumns.positionColumn_integrable coordinate h).add
   (originalPhysicalCutoff_integrable q (OriginalRieszFiniteColumns.positionColumn coordinate (-h)))).congr
   (Lp.coeFn_add (OriginalRieszFiniteColumns.positionColumn coordinate h)
     (originalPhysicalCutoff q (OriginalRieszFiniteColumns.positionColumn coordinate (-h)))).symm
 have seedIntegrable : Integrable (seed : ℝ→ℂ) := by
  have regular:=((OriginalRieszFiniteColumns.positionColumn_integrable coordinate (-h)).sub
    (originalPhysicalCutoff_integrable q (OriginalRieszFiniteColumns.positionColumn coordinate (-h)))).congr
    (Lp.coeFn_sub (OriginalRieszFiniteColumns.positionColumn coordinate (-h))
      (originalPhysicalCutoff q (OriginalRieszFiniteColumns.positionColumn coordinate (-h)))).symm
  rw [←OriginalRieszFinitePairing.CoPoisson.positionSeed_eq_exterior coordinate h nonnegative] at regular
  exact regular
 have inventory : inside+seed=OriginalRieszFiniteColumns.positionColumn coordinate h+
   OriginalRieszFiniteColumns.positionColumn coordinate (-h) := by
  unfold inside seed OriginalKInsideDebtRSource.actualInsidePosition
  rw [OriginalRieszFinitePairing.CoPoisson.positionSeed_eq_exterior coordinate h nonnegative]
  module
 have source:=congrArg (fun material : BurnolL2=>∫ x : ℝ,material x) inventory
 rw [integral_congr_ae (Lp.coeFn_add inside seed)] at source
 simp only [Pi.add_apply] at source
 rw [integral_add insideIntegrable seedIntegrable,
   integral_congr_ae (Lp.coeFn_add (OriginalRieszFiniteColumns.positionColumn coordinate h)
     (OriginalRieszFiniteColumns.positionColumn coordinate (-h))),
   ] at source
 simp only [Pi.add_apply] at source
 rw [integral_add (OriginalRieszFiniteColumns.positionColumn_integrable coordinate h)
     (OriginalRieszFiniteColumns.positionColumn_integrable coordinate (-h)),
   OriginalRieszFinitePairing.positionColumn_integral_zero,
   OriginalRieszFinitePairing.positionColumn_integral_zero,zero_add] at source
 linear_combination (2:ℂ)*source

/-- This denominator qualification is generated by the original admitted coordinate bound. -/
theorem original_quarter_rate_ne_zero (coordinate : BurnolCompletedMellinCoordinate) :
 coordinate.value/2-1/2≠0 := by
 intro zero
 have real:=congrArg Complex.re zero
 simp only [Complex.sub_re,Complex.div_re] at real
 norm_num at real
 linarith [coordinate.belowOne]

def actualPositionQuarterMean (h : ℝ) : ℂ :=
 (OriginalKInsideDebtRSource.actualPositionTailCoefficient observation nontrivial half h*
   (((2*q:ℝ):ℂ)*(q:ℂ)^(-(OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).value))+
 (2:ℂ)*(∫ x : ℝ,OriginalRieszFinitePairing.CoPoisson.positionSeed
   (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h x))/
 ((OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).value/2-1/2)

/-- Original admitted source bounds and the actual quarter FTC/seed action generate the entire position mean price. -/
theorem actual_position_R_quarter_mean (h : ℝ) (nonnegative : 0≤h) :
 Paid.actualMean (OriginalKFullSourceRResponse.Op.R observation nontrivial half
   (OriginalKInsideDebtRSource.actualInsidePosition observation nontrivial half h))=
 actualPositionQuarterMean observation nontrivial half h := by
 have source:=actual_position_quarter_mean_action observation nontrivial half h nonnegative
 rw [actual_position_source_seed_mean observation nontrivial half h nonnegative] at source
 unfold actualPositionQuarterMean
 apply (eq_div_iff (original_quarter_rate_ne_zero
   (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half))).mpr
 linear_combination source



end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPositionQuarterFTCAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
