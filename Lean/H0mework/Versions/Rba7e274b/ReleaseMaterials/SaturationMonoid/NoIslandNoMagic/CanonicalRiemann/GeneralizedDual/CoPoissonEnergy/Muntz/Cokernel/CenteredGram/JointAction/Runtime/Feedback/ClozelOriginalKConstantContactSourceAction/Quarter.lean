import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKConstantContactSourceAction.Source
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


/-- The same actual two-mean material consumes its existing quarter field and the source U/V qualifications. -/
theorem actual_constant_contact_mean_source (h : ℝ) :
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let material:=(OriginalKGapMeanRSourceAction.Full.meanDebt coordinate h : BurnolL2)
 let acted:=OriginalKFullSourceRResponse.Op.R observation nontrivial half material
 let A:=star (OriginalRieszSource.Kernel.A coordinate)
 let b:=star (OriginalRieszSource.Kernel.beta coordinate)
 (2*coordinate.value-1)*inner ℂ (burnolCompletedMellinRieszVector coordinate : BurnolL2) acted=
 A*inner ℂ (fourierL2 OriginalRieszSource.Response.wholeU) acted-
 b*inner ℂ (fourierL2 OriginalRieszSource.Response.wholeV) acted+
 coordinate.value*A*inner ℂ ConstantSource.seed acted+
 (1-coordinate.value)*b*inner ℂ (fourierL2 ConstantSource.seed) acted-
 (2:ℂ)*inner ℂ (ConstantSource.value coordinate) material := by
 dsimp only
 have source:=actual_constant_contact_K_R_source observation nontrivial half
   (OriginalKGapMeanRSourceAction.Full.meanDebt (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h : BurnolL2)
 have prices:=OriginalKFourierRegularMeanAction.actual_original_UV_R_prices observation nontrivial half h
 dsimp only at source
 rw [inner_sub_left,inner_sub_left,prices.1,prices.2] at source
 linear_combination source

/-- Original quarter constant has its own generated price; source units q and norm-squared one-half are kept. -/
theorem actual_constant_seed_R_price (h : ℝ) :
 inner ℂ ConstantSource.seed
   (OriginalKFullSourceRResponse.Op.R observation nontrivial half
     (OriginalKGapMeanRSourceAction.Full.meanDebt
       (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h : BurnolL2))=
 -(1/2:ℂ)*OriginalKGapMeanRSourceAction.actualMeanGram observation nontrivial half h/
   ((OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).value/2) := by
 have read:=(burnolRadiusRestriction q).adjoint_inner_left
   (OriginalKFullSourceRResponse.Op.R observation nontrivial half
     (OriginalKGapMeanRSourceAction.Full.meanDebt
       (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h : BurnolL2))
   (intervalConstant q)
 change inner ℂ ConstantSource.seed _=inner ℂ (intervalConstant q) (burnolRadiusRestriction q _) at read
 rw [read,OriginalKGapMeanRSourceAction.actual_two_mean_debt_quarter_R_field,inner_smul_right]
 have self : inner ℂ (intervalConstant q) (intervalConstant q)=(1/2:ℂ) := by
  rw [L2.inner_def]
  have actual : (fun x : ℝ=>inner ℂ (intervalConstant q x) (intervalConstant q x))=ᵐ[
    volume.restrict (symmetricInterval q)] fun _=>(1:ℂ) := by
   filter_upwards [intervalConstant_coeFn q] with x read
   rw [read]
   simp
  rw [integral_congr_ae actual,integral_const]
  norm_num [symmetricInterval,real_smul]
 rw [self]
 ring


end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKConstantContactSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
