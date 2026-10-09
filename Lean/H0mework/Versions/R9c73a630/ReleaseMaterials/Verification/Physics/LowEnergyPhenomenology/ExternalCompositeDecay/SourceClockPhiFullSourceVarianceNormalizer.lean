import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiWholeRSourceReturn
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiWholeForcingVariance
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.OriginalRCommutatorSource
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory SourceClockPhiCombinedScalePressure SourceClockPhiMatchedDiffusionSource
open SourceScalarDoubleCurrent SourceClockPhiHeatNativeClosedGraph ClockPhiMatchedNoiseCore
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev H0:End:=diagonalAction
private abbrev A:End:=combinedConjugate
attribute [local irreducible] sourcePair embed diagonalAction combinedConjugate diffusionDrift diffusionDriftTranspose

private theorem complete_product_source(X Y:End):
    completeCurrent (X*Y)-completeCurrent X*Y-X*completeCurrent Y+X*completeCurrent 1*Y=
      (2:ℂ) • ((X*A-A*X)*(Y*A-A*Y)):=by
  simp only [completeCurrent,diffusionCurrent,Algebra.smul_def,map_ofNat]
  noncomm_ring

/-- The normalizer uses the original complete clock generator, including its non-conservative gain, and the genuine conjugate frequency pole. -/
def fullSourceVarianceNormalizer(z:ℂ):End:=
  let L:=H0-(star z) • (1:End)
  let R:=H0-z • (1:End)
  completeCurrent (L*R)-completeCurrent L*R-L*completeCurrent R+L*completeCurrent 1*R

/-- All original drift/gain normalizers and both frequency poles cancel internally. The remaining source is the square of the complete H0-clock commutator. -/
theorem actual_full_source_variance_normalizer(z:ℂ):
    fullSourceVarianceNormalizer z=(2:ℂ) • (bracket H0 A*bracket H0 A):=by
  unfold fullSourceVarianceNormalizer
  rw [complete_product_source]
  simp only [sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm,one_mul,mul_one]
  unfold bracket
  congr 1
  noncomm_ring

private theorem pair_sub_l(f g h:QuantumTest):sourcePair (f-g) h=sourcePair f h-sourcePair g h:=by
  simp only [sourcePair,map_sub,inner_sub_left]
private theorem pair_sub_r(f g h:QuantumTest):sourcePair f (g-h)=sourcePair f g-sourcePair f h:=by
  simp only [sourcePair,map_sub,inner_sub_right]
private theorem pair_smul_r(c:ℂ)(f g:QuantumTest):sourcePair f (c • g)=c*sourcePair f g:=by
  simp only [sourcePair,map_smul,inner_smul_right]
private theorem A_pair(f g:QuantumTest):sourcePair (A f) g= -sourcePair f (A g):=by
  have h:=noiseGenerator_pair 1 0 f g
  simp only [noiseGenerator,Complex.ofReal_one,one_smul,Complex.ofReal_zero,zero_smul,add_zero] at h
  have hh:=congrArg Neg.neg h
  simpa only [neg_neg] using hh.symm
private theorem commutator_pair(f g:QuantumTest):sourcePair (bracket H0 A f) g=sourcePair f (bracket H0 A g):=by
  change sourcePair (H0 (A f)-A (H0 f)) g=sourcePair f (H0 (A g)-A (H0 g))
  rw [pair_sub_l,pair_sub_r]
  rw [←diagonalAction_pair,A_pair,A_pair,←diagonalAction_pair]
  ring

/-- The actual full-source normalizer is a positive Gram price on the original Hilbert source, before any cofinal or Gaussian limit. This is the exact source consumed by the full commutator variance jet. -/
theorem actual_full_source_variance_pair(z:ℂ)(f g:QuantumTest):
    sourcePair f (fullSourceVarianceNormalizer z g)=(2:ℂ)*sourcePair (bracket H0 A f) (bracket H0 A g):=by
  rw [actual_full_source_variance_normalizer]
  simp only [LinearMap.smul_apply,Module.End.mul_apply,pair_smul_r]
  rw [←commutator_pair]

theorem actual_full_source_variance_nonnegative(z:ℂ)(f:QuantumTest):
    0≤(sourcePair f (fullSourceVarianceNormalizer z f)).re:=by
  rw [actual_full_source_variance_pair]
  have hp:0≤(sourcePair (bracket H0 A f) (bracket H0 A f)).re:=by
    simpa only [sourcePair,RCLike.re_eq_complex_re] using inner_self_nonneg (𝕜:=ℂ) (x:=embed (bracket H0 A f))
  norm_num only [Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,zero_mul,sub_zero]
  exact mul_nonneg (by norm_num) hp
end LowEnergy.OriginalRCommutatorSource
