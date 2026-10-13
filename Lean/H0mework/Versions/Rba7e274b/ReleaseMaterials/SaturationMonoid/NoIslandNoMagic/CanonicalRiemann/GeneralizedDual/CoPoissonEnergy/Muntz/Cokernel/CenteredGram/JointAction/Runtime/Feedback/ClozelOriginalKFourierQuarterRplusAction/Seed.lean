import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFourierQuarterRplusAction.Action
import H0mework.Versions.V2.Arithmetic.RiemannNativeCurrent.UnitResponseRadius
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFourierQuarterRplusAction
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

/-- Actual inside and exterior restrictions of the same zero-mass Fourier columns produce the original seed mean. -/
theorem actual_fourier_source_seed_mean (h : ℝ) (nonnegative : 0≤h) :
 Paid.actualMean (OriginalKInsideDebtRSource.actualInsideFourier observation nontrivial half h)=
 -(2:ℂ)*(∫ x : ℝ,OriginalRieszFinitePairing.CoPoisson.fourierSeed
   (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h x) := by
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let inside:=OriginalKInsideDebtRSource.actualInsideFourier observation nontrivial half h
 let seed:=OriginalRieszFinitePairing.CoPoisson.fourierSeed coordinate h
 have supported:= (OriginalKInsideDebtRSource.actual_inside_columns_quarter observation nontrivial half h nonnegative).2
 rw [actual_compact_mean_integral inside supported]
 have insideIntegrable : Integrable (inside : ℝ→ℂ) := by
  exact ((OriginalRieszFiniteColumns.fourierColumn_integrable coordinate (-h)).add
   (originalPhysicalCutoff_integrable q (OriginalRieszFiniteColumns.fourierColumn coordinate h))).congr
   (Lp.coeFn_add (OriginalRieszFiniteColumns.fourierColumn coordinate (-h))
     (originalPhysicalCutoff q (OriginalRieszFiniteColumns.fourierColumn coordinate h))).symm
 have seedIntegrable : Integrable (seed : ℝ→ℂ) := by
  have regular:=((OriginalRieszFiniteColumns.fourierColumn_integrable coordinate h).sub
    (originalPhysicalCutoff_integrable q (OriginalRieszFiniteColumns.fourierColumn coordinate h))).congr
    (Lp.coeFn_sub (OriginalRieszFiniteColumns.fourierColumn coordinate h)
      (originalPhysicalCutoff q (OriginalRieszFiniteColumns.fourierColumn coordinate h))).symm
  rw [←OriginalRieszFinitePairing.CoPoisson.fourierSeed_eq_exterior coordinate h nonnegative] at regular
  exact regular
 have inventory : inside+seed=OriginalRieszFiniteColumns.fourierColumn coordinate (-h)+
   OriginalRieszFiniteColumns.fourierColumn coordinate h := by
  unfold inside seed OriginalKInsideDebtRSource.actualInsideFourier
  rw [OriginalRieszFinitePairing.CoPoisson.fourierSeed_eq_exterior coordinate h nonnegative]
  module
 have source:=congrArg (fun material : BurnolL2=>∫ x : ℝ,material x) inventory
 rw [integral_congr_ae (Lp.coeFn_add inside seed)] at source
 simp only [Pi.add_apply] at source
 rw [integral_add insideIntegrable seedIntegrable,
   integral_congr_ae (Lp.coeFn_add (OriginalRieszFiniteColumns.fourierColumn coordinate (-h))
     (OriginalRieszFiniteColumns.fourierColumn coordinate h)),
   ] at source
 simp only [Pi.add_apply] at source
 rw [integral_add (OriginalRieszFiniteColumns.fourierColumn_integrable coordinate (-h))
     (OriginalRieszFiniteColumns.fourierColumn_integrable coordinate h),
   OriginalRieszFinitePairing.fourierColumn_integral_zero,
   OriginalRieszFinitePairing.fourierColumn_integral_zero,zero_add] at source
 linear_combination (2:ℂ)*source

def actualFourierQuarterMean (h : ℝ) : ℂ :=
 (2:ℂ)*(∫ x : ℝ,OriginalRieszFinitePairing.CoPoisson.fourierSeed
   (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h x)/
 ((OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).value/2)

/-- The literal Fourier compact source and its complete seed mass generate its positive Rplus mean. -/
theorem actual_fourier_Rplus_source_mean (h : ℝ) (nonnegative : 0≤h) :
 Paid.actualMean (Paid.Rplus
   ((OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).value/2)
   (OriginalKInsideDebtRSource.actualInsideFourier observation nontrivial half h))=
 actualFourierQuarterMean observation nontrivial half h := by
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 have right : 1/4<(coordinate.value/2).re := by
  rw [Complex.div_re];norm_num;linarith [coordinate.rightHalf]
 have source:=actual_compact_Rplus_mean_action (coordinate.value/2) right
   (OriginalKInsideDebtRSource.actualInsideFourier observation nontrivial half h)
   (OriginalKInsideDebtRSource.actual_inside_columns_quarter observation nontrivial half h nonnegative).2
 rw [actual_fourier_source_seed_mean observation nontrivial half h nonnegative] at source
 unfold actualFourierQuarterMean
 linear_combination source



end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFourierQuarterRplusAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
