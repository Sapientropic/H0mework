import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCompleteMCofinalSource.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFullKernelCofinalSource
open Complex MeasureTheory Filter FourierTransform
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
local notation "K" => burnolCompletedMellinRieszVector
local instance kernelCofinalSourcePhysicalComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete


local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "S" => burnolMeanZeroTruncatedFourierSquare
local notation "b" => burnolRieszSingleFourierSource

def actualFourierKernelForcing (c:BurnolCompletedMellinCoordinate):M:=
 burnolAmbientMeanZeroFourier (burnolAmbientCompletedMellinKernelFormula c)

def actualFiniteKernelSource (c:BurnolCompletedMellinCoordinate) (n:Nat):M:=
 (∑ k ∈ Finset.range n,S^k) (actualFourierKernelForcing c)

/-- The existing finite geometric source action is driven by the actual original Fourier forcing; the target b is not a constructor input. -/
theorem actual_kernel_source_step (c:BurnolCompletedMellinCoordinate) (n:Nat):
 actualFiniteKernelSource c (n+1)=actualFourierKernelForcing c+S (actualFiniteKernelSource c n) :=by
 unfold actualFiniteKernelSource
 rw [geom_sum_succ]
 change S ((∑ k∈Finset.range n,S^k) (actualFourierKernelForcing c))+actualFourierKernelForcing c=_
 exact add_comm _ _

/-- Same source geometric action generates the exact original b residual from its already-generated inverse equation. -/
theorem actual_kernel_source_residual (c:BurnolCompletedMellinCoordinate) (n:Nat):
 b c-actualFiniteKernelSource c n=(S^n) (b c) :=by
 have equation:=burnolRieszSingleFourierSource_equation c
 have source:=(congrArg (fun operator:M→L[ℂ]M=>operator (b c)) (geom_sum_mul_neg S n))
 change (∑ k∈Finset.range n,S^k) (burnolMeanZeroOneMinusSquare (b c))=b c-(S^n) (b c) at source
 rw [equation] at source
 change actualFiniteKernelSource c n=b c-(S^n) (b c) at source
 linear_combination (norm:=module) -source

/-- The already-paid original source square contraction controls this actual forcing response. -/
theorem actual_kernel_source_square_bound : ‖S‖≤(1/4:ℝ) :=by
 apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
 exact OriginalKResponseCofinalSourceAction.actual_square_source_norm

/-- The original inverse's own norm is paid from its true forcing; no physical Pa margin is transferred. -/
theorem actual_original_kernel_source_bound (c:BurnolCompletedMellinCoordinate):
 ‖b c‖≤(4/3:ℝ)*‖actualFourierKernelForcing c‖ :=by
 have equation:=burnolRieszSingleFourierSource_equation c
 have fixed:b c=actualFourierKernelForcing c+S (b c) :=by
  change b c-S (b c)=actualFourierKernelForcing c at equation
  linear_combination (norm:=module) equation
 have source:‖b c‖≤‖actualFourierKernelForcing c‖+‖S (b c)‖:=by
  conv_lhs=>rw [fixed]
  exact norm_add_le _ _
 have paid:=OriginalKResponseCofinalSourceAction.actual_square_source_norm (b c)
 linarith

/-- This new original forcing source pays its finite residual using the existing contraction and full source norm. -/
theorem actual_kernel_source_error (c:BurnolCompletedMellinCoordinate) (n:Nat):
 ‖b c-actualFiniteKernelSource c n‖≤
 (1/4:ℝ)^n*((4/3:ℝ)*‖actualFourierKernelForcing c‖) :=by
 rw [actual_kernel_source_residual]
 have power:‖(S^n) (b c)‖≤(1/4:ℝ)^n*‖b c‖ :=by
  induction n with
  | zero=>simp
  | succ n previous=>
   rw [pow_succ']
   change ‖S ((S^n) (b c))‖≤_
   exact (OriginalKResponseCofinalSourceAction.actual_square_source_norm _).trans
    ((mul_le_mul_of_nonneg_left previous (by norm_num)).trans_eq (by rw [pow_succ];ring))
 exact power.trans (mul_le_mul_of_nonneg_left (actual_original_kernel_source_bound c) (by positivity))

/-- The complete actual b source is the original same forcing limit; its value is not used to recognize a foreign sequence. -/
theorem actual_kernel_source_tendsto (c:BurnolCompletedMellinCoordinate):
 Tendsto (actualFiniteKernelSource c) atTop (𝓝 (b c)) :=by
 have decay:=tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/4) (by norm_num : (1/4:ℝ)<1)
 have source:=decay.mul_const ((4/3:ℝ)*‖actualFourierKernelForcing c‖)
 simp only [zero_mul] at source
 apply tendsto_iff_norm_sub_tendsto_zero.mpr
 have bounded:=squeeze_zero (fun n=>norm_nonneg _) (actual_kernel_source_error c) source
 simpa only [norm_sub_rev] using bounded

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFullKernelCofinalSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
