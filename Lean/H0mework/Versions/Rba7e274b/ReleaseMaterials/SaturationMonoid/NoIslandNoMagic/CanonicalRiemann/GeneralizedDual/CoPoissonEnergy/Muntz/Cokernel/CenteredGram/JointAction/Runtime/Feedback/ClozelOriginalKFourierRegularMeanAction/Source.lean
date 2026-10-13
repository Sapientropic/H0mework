import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKLiteralEdgeMeanSourcePrice.Consumer
import H0mework.Versions.V2.Arithmetic.RiemannNativeCurrent.UnitResponseRadius
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFourierRegularMeanAction
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

/-- The actual corrected source Fourier anti-action and original R source share one isometric orbit. -/
theorem actual_Fourier_regular_R_source (material : BurnolL2) :
 inner ℂ (fourierL2 (OriginalKSourceBalance.regularSource
   (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)))
   (OriginalKFullSourceRResponse.Op.R observation nontrivial half material)=
 -(2:ℂ)*inner ℂ (fourierL2 (OriginalKSourceBalance.correctedField
   (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half))) material := by
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let corrected:=OriginalKSourceBalance.correctedField coordinate
 let velocity:=OriginalKSourceBalance.correctedVelocity coordinate
 let acted:=OriginalKFullSourceRResponse.Op.R observation nontrivial half material
 have native:=OriginalKSourceBalance.corrected_source_strong coordinate
 have source : HasDerivAt (fun shift : ℝ=>burnolMultiplicativeDilation shift corrected) velocity
   ((fun time : ℝ=>-time/2) 0) := by simpa only [neg_zero,zero_div] using native
 have scalar : HasDerivAt (fun time : ℝ=>-time/2) (-1/2:ℝ) 0 := by
  simpa only [Pi.neg_apply,neg_div,id_eq] using ((hasDerivAt_id (0:ℝ)).neg.div_const 2)
 have rescaled:=source.scomp (0:ℝ) scalar
 have rotated:=burnolFourierOrbit_hasDerivAt corrected ((-1/2:ℝ) • velocity) rescaled
 have right : 1/4<(coordinate.value/2).re := by
  rw [Complex.div_re];norm_num;linarith [coordinate.rightHalf]
 have responding:=burnolDirectRightResolventOrbit_hasDerivAt (coordinate.value/2) right material
 have generated:=rotated.inner ℂ responding
 have same : (fun time : ℝ=>inner ℂ
   (burnolMultiplicativeDilation (-time/2) (fourierL2 corrected))
   (burnolMultiplicativeDilation (-time/2) acted))=fun _=>inner ℂ (fourierL2 corrected) acted :=
  funext fun time=>(burnolMultiplicativeDilation (-time/2)).inner_map_map _ _
 change HasDerivAt (fun time : ℝ=>inner ℂ
   (burnolMultiplicativeDilation (-time/2) (fourierL2 corrected))
   (burnolMultiplicativeDilation (-time/2) acted)) _ 0 at generated
 rw [same] at generated
 have zero:=generated.unique (hasDerivAt_const (0:ℝ) (inner ℂ (fourierL2 corrected) acted))
 simp only [neg_zero,zero_div,burnolMultiplicativeDilation_zero] at zero
 change inner ℂ (fourierL2 corrected) ((coordinate.value/2-1/4) • acted+material)+
   inner ℂ (-fourierL2 ((-1/2:ℝ) • velocity)) acted=0 at zero
 rw [←algebraMap_smul ℂ (-1/2:ℝ)] at zero
 push_cast at zero
 unfold velocity OriginalKSourceBalance.correctedVelocity at zero
 rw [map_smul,map_add,map_smul] at zero
 simp only [inner_add_right,inner_add_left,inner_smul_right,inner_neg_left,inner_smul_left,
   starRingEnd_apply,star_neg,star_sub,star_div₀,star_ofNat,star_one,star_star] at zero
 change inner ℂ (fourierL2 (OriginalKSourceBalance.regularSource coordinate)) acted=
   -(2:ℂ)*inner ℂ (fourierL2 corrected) material
 change (coordinate.value/2-1/4)*inner ℂ (fourierL2 corrected) acted+inner ℂ (fourierL2 corrected) material+
   -(-1/2*((-(coordinate.value-1/2))*inner ℂ (fourierL2 corrected) acted+
   inner ℂ (fourierL2 (OriginalKSourceBalance.regularSource coordinate)) acted))=0 at zero
 linear_combination (2:ℂ)*zero



end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFourierRegularMeanAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
