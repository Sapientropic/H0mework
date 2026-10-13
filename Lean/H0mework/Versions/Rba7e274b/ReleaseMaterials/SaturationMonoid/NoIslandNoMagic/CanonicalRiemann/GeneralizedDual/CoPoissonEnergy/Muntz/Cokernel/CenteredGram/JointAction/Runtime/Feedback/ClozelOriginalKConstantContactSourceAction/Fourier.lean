import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKConstantContactSourceAction.Character
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKConstantContactSourceAction
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


/-- The same generated constant-contact source has its actual Fourier opposite action on original R. -/
theorem actual_Fconstant_contact_R_ward (material : BurnolL2) :
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let acted:=OriginalKFullSourceRResponse.Op.R observation nontrivial half material
 inner ℂ (fourierL2 (ConstantSource.velocity coordinate)) acted-
 inner ℂ (fourierL2 (ConstantSource.value coordinate))
   (-(coordinate.value-1/2) • acted-(2:ℂ) • material)=0 := by
 dsimp only
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let source:=ConstantSource.value coordinate
 let velocity:=ConstantSource.velocity coordinate
 let acted:=OriginalKFullSourceRResponse.Op.R observation nontrivial half material
 have native:=ConstantSource.strong_derivative coordinate
 have rescaledSource : HasDerivAt (fun shift : ℝ=>burnolMultiplicativeDilation shift source) velocity
   ((fun time : ℝ=>-time/2) 0) := by simpa only [neg_zero,zero_div] using native
 have scalar : HasDerivAt (fun time : ℝ=>-time/2) (-1/2:ℝ) 0 := by
  simpa only [Pi.neg_apply,neg_div,id_eq] using ((hasDerivAt_id (0:ℝ)).neg.div_const 2)
 have rescaled:=rescaledSource.scomp (0:ℝ) scalar
 have rotated:=burnolFourierOrbit_hasDerivAt source ((-1/2:ℝ) • velocity) rescaled
 have right : 1/4<(coordinate.value/2).re := by
  rw [Complex.div_re];norm_num;linarith [coordinate.rightHalf]
 have generated:=rotated.inner ℂ
   (burnolDirectRightResolventOrbit_hasDerivAt (coordinate.value/2) right material)
 have same : (fun time : ℝ=>inner ℂ
   (burnolMultiplicativeDilation (-time/2) (fourierL2 source))
   (burnolMultiplicativeDilation (-time/2) acted))=fun _=>inner ℂ (fourierL2 source) acted :=
  funext fun time=>(burnolMultiplicativeDilation (-time/2)).inner_map_map _ _
 change HasDerivAt (fun time : ℝ=>inner ℂ
   (burnolMultiplicativeDilation (-time/2) (fourierL2 source))
   (burnolMultiplicativeDilation (-time/2) acted)) _ 0 at generated
 rw [same] at generated
 have zero:=generated.unique (hasDerivAt_const (0:ℝ) (inner ℂ (fourierL2 source) acted))
 simp only [neg_zero,zero_div,burnolMultiplicativeDilation_zero] at zero
 rw [←algebraMap_smul ℂ (-1/2:ℝ)] at zero
 push_cast at zero
 rw [map_smul] at zero
 simp only [inner_add_right,inner_smul_right,inner_neg_left,inner_smul_left,
   starRingEnd_apply,star_div₀,star_neg,star_one,star_ofNat] at zero
 change inner ℂ (fourierL2 velocity) acted-
   inner ℂ (fourierL2 source) (-(coordinate.value-1/2) • acted-(2:ℂ) • material)=0
 change (coordinate.value/2-1/4)*inner ℂ (fourierL2 source) acted+
   inner ℂ (fourierL2 source) material+ -(-1/2*inner ℂ (fourierL2 velocity) acted)=0 at zero
 simp only [inner_sub_right,inner_smul_right]
 linear_combination (2:ℂ)*zero


/-- Source constants themselves have even parity; this keeps actual Fourier direction and the q unit. -/
theorem actual_constant_seed_even : reflectL2 ConstantSource.seed=ConstantSource.seed := by
 change reflectL2 (burnolRadiusZeroExtension q (intervalConstant q))=_
 rw [burnolRadiusZeroExtension_reflect,reflectRestricted_intervalConstant]
 rfl

/-- Actual Fourier source row retains both constant-source response prices in the resonant branch. -/
theorem actual_Fconstant_contact_mean_row (h : ℝ) :
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let material:=(OriginalKGapMeanRSourceAction.Full.meanDebt coordinate h : BurnolL2)
 let acted:=OriginalKFullSourceRResponse.Op.R observation nontrivial half material
 let A:=star (OriginalRieszSource.Kernel.A coordinate)
 let b:=star (OriginalRieszSource.Kernel.beta coordinate)
 A*inner ℂ (fourierL2 OriginalRieszSource.Response.wholeV) acted-
 b*inner ℂ (fourierL2 OriginalRieszSource.Response.wholeU) acted=
 (1-coordinate.value)*A*inner ℂ (fourierL2 ConstantSource.seed) acted+
 coordinate.value*b*inner ℂ ConstantSource.seed acted+
 (2:ℂ)*inner ℂ (fourierL2 (ConstantSource.value coordinate)) material := by
 dsimp only
 have source:=actual_Fconstant_contact_R_ward observation nontrivial half
   (OriginalKGapMeanRSourceAction.Full.meanDebt (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h : BurnolL2)
 have prices:=OriginalKFourierRegularMeanAction.actual_original_UV_R_prices observation nontrivial half h
 dsimp only at source
 unfold ConstantSource.value ConstantSource.velocity at source
 simp only [map_add,map_sub,map_smul] at source
 rw [fourierL2_fourierL2,fourierL2_fourierL2,fourierL2_fourierL2,
   OriginalRieszSource.Response.wholeU_reflection,OriginalRieszSource.Response.wholeV_reflection,
   actual_constant_seed_even] at source
 simp only [inner_add_left,inner_sub_left,inner_smul_left,starRingEnd_apply,
   inner_sub_right,inner_smul_right,star_neg,star_sub,star_div₀,star_mul,star_ofNat,star_one,star_star] at source
 rw [prices.1,prices.2] at source
 unfold ConstantSource.value
 simp only [map_add,map_sub,map_smul]
 rw [fourierL2_fourierL2,actual_constant_seed_even]
 simp only [inner_add_left,inner_sub_left,inner_smul_left,starRingEnd_apply]
 linear_combination -source

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKConstantContactSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
