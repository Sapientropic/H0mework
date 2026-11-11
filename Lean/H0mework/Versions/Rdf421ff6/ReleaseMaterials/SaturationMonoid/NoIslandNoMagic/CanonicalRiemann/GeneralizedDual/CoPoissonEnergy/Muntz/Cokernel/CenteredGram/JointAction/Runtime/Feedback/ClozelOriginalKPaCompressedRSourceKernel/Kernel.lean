import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaCompressedRSourceKernel.Partition
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaCompressedRSourceKernel
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
local instance kernelPhysicalComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

/-- Source qualification and actual vector energy generate separation of the entire original Pa compression, not a caller kernel certificate. -/
theorem compressed_source_kernel_separated (source : PaSourceCarrier)
 (vanishes : compressedR observation nontrivial half source=0) : source=0 := by
 have pairing := compressed_source_inner_read observation nontrivial half source
 rw [vanishes,inner_zero_left] at pairing
 have energy := source_R_energy observation nontrivial half (sourceInclusion source)
 rw [←pairing] at energy
 simp only [Complex.zero_re] at energy
 have lambda := OriginalKDecodedPaRSourceEnergy.source_lambda_positive observation half
 have squared : ‖sourceR observation nontrivial half (sourceInclusion source)‖^2=0 := by
  have product : (observation.coordinate/2-1/4).re *
   ‖sourceR observation nontrivial half (sourceInclusion source)‖^2=0 := by linarith
  exact (mul_eq_zero.mp product).resolve_left (ne_of_gt lambda)
 have rzero : sourceR observation nontrivial half (sourceInclusion source)=0 :=
  norm_eq_zero.mp (by nlinarith [norm_nonneg (sourceR observation nontrivial half (sourceInclusion source))])
 have action := source_R_vector_action observation nontrivial half (sourceInclusion source)
 rw [rzero] at action
 simp only [map_zero,smul_zero,zero_add] at action
 have rawZero : sourceInclusion source=0 := action.unique (hasDerivAt_const (0:ℝ) (0:BurnolL2))
 apply Subtype.ext
 apply Subtype.ext
 exact rawZero

theorem compressed_source_injective : Function.Injective (compressedR observation nontrivial half) := by
 intro left right same
 have zero : compressedR observation nontrivial half (left-right)=0 := by
  rw [map_sub,same,sub_self]
 exact sub_eq_zero.mp (compressed_source_kernel_separated observation nontrivial half (left-right) zero)

/-- The exact source Gram retains its original unit-rank fee; Cauchy gives a quantitative read without an inverse margin assumption. -/
theorem compressed_source_full_cost_bound (source : PaSourceCarrier) :
 (observation.coordinate/2-1/4).re *
  (‖compressedR observation nontrivial half source‖^2+‖unitRankResponse observation nontrivial half source‖^2) ≤
 ‖compressedR observation nontrivial half source‖*‖(source : BurnolPaAmbientCarrier)‖ := by
 rw [←compressed_full_energy]
 have cauchy := re_inner_le_norm (𝕜:=ℂ) (-(compressedR observation nontrivial half source))
  (source : BurnolPaAmbientCarrier)
 change (inner ℂ (-(compressedR observation nontrivial half source)) (source : BurnolPaAmbientCarrier)).re ≤
  ‖-(compressedR observation nontrivial half source)‖*‖(source : BurnolPaAmbientCarrier)‖ at cauchy
 simpa only [inner_neg_left,Complex.neg_re,norm_neg] using cauchy

theorem compressed_source_strict_energy (source : PaSourceCarrier) (nonzero : source≠0) :
 0< -(inner ℂ (compressedR observation nontrivial half source) (source : BurnolPaAmbientCarrier)).re := by
 have output : compressedR observation nontrivial half source≠0 := by
  intro vanishes
  exact nonzero (compressed_source_kernel_separated observation nontrivial half source vanishes)
 have normPositive : 0<‖compressedR observation nontrivial half source‖ := norm_pos_iff.mpr output
 have rankNonnegative := sq_nonneg ‖unitRankResponse observation nontrivial half source‖
 have lambda := OriginalKDecodedPaRSourceEnergy.source_lambda_positive observation half
 rw [compressed_full_energy]
 exact mul_pos lambda (by nlinarith)

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaCompressedRSourceKernel
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
