import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKInsideDebtRAction.Price
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKGapMeanRSourceAction
open Complex MeasureTheory Set Filter SourceGeneratedHilbertCokernel
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalRieszFiniteSynthesis
local instance fieldGapMeanRComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
namespace Paid
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.FiniteMobiusResolventFlux (actualMean source_negative_restriction actual_mean_source_negative actual_mean_physical)
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalJointFluxSource (source_weight_mean_phase source_mean_R_read)
end Paid
local notation "q" => (1/4:ℝ)
local notation "G" => gapMeanVector
local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

/-- The actual negative source restrictions generate the complete quarter R field before its scalar mean is read. -/
theorem original_R_quarter_source_action (z : ℂ) (right : 1/4<z.re) (material : BurnolPaAmbientCarrier) :
 burnolRadiusRestriction q (burnolDirectRightResolvent z (material : BurnolL2))=
 (-Paid.actualMean (material : BurnolL2)/z) • intervalConstant q := by
 let restriction:=burnolRadiusRestriction q
 let unitEmbed : ℂ→L[ℂ]BurnolQuarterIntervalL2:=ContinuousLinearMap.toSpanSingleton ℂ (intervalConstant q)
 have integrable:=burnolDirectRightResolventIntegrand_integrableOn z right (material : BurnolL2)
 have decay : (-z).re<0 := by simp only [Complex.neg_re];linarith
 have acted : restriction (burnolDirectRightResolvent z (material : BurnolL2))=
   -(∫ tau : ℝ in Ioi 0,unitEmbed
     (Complex.exp (-z*(tau:ℂ))*Paid.actualMean (material : BurnolL2))) := by
  unfold burnolDirectRightResolvent
  rw [map_neg,←restriction.integral_comp_comm integrable]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro tau positive
  unfold burnolDirectRightResolventIntegrand
  dsimp only
  rw [map_smul]
  have source:=Paid.source_negative_restriction material (-tau/2)
    (by change 0<tau at positive;linarith)
  dsimp only [restriction]
  rw [source,smul_smul,←mul_assoc]
  change (positiveMellinQuarterRightResolventWeight z tau*(Real.exp ((-tau/2)/2):ℂ)*
    Paid.actualMean (material : BurnolL2)) • intervalConstant q=_
  rw [show (-tau/2)/2=-tau/4 by ring,Paid.source_weight_mean_phase]
  rfl
 have scalarIntegrable : IntegrableOn (fun tau : ℝ=>Complex.exp (-z*(tau:ℂ))*Paid.actualMean (material : BurnolL2)) (Ioi 0) :=
  (integrableOn_exp_mul_complex_Ioi decay 0).mul_const _
 rw [acted,unitEmbed.integral_comp_comm scalarIntegrable,integral_mul_const,
   integral_exp_mul_complex_Ioi decay 0]
 simp only [Complex.ofReal_zero,mul_zero,Complex.exp_zero,neg_div_neg_eq]
 unfold unitEmbed
 rw [ContinuousLinearMap.toSpanSingleton_apply,←neg_smul]
 congr 1
 ring

/-- Both original physical G and actual Fourier G supply their own R response and Gram coefficient. -/
theorem actual_two_mean_quarter_R_action :
 burnolRadiusRestriction q (OriginalKFullSourceRResponse.Op.R observation nontrivial half (G : BurnolL2))=
 (-inner ℂ G G / ((OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).value/2)) • intervalConstant q ∧
 burnolRadiusRestriction q (OriginalKFullSourceRResponse.Op.R observation nontrivial half (Fphysical G : BurnolL2))=
 (-inner ℂ G (Fphysical G) / ((OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).value/2)) • intervalConstant q := by
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 have right : 1/4<(coordinate.value/2).re := by
  rw [Complex.div_re];norm_num;linarith [coordinate.rightHalf]
 have first:=original_R_quarter_source_action (coordinate.value/2) right G
 have second:=original_R_quarter_source_action (coordinate.value/2) right (Fphysical G)
 rw [Paid.actual_mean_physical,←gapMeanVector_readback] at first second
 exact ⟨first,second⟩



end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKGapMeanRSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
