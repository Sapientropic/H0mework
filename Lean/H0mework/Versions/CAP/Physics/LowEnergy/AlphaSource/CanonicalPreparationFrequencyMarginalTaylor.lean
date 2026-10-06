import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationGlobalIntegratedTaylor
import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationCompositionFourierReadback

set_option autoImplicit false
set_option maxHeartbeats 240000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumFrequencyN2
open PreparationVacuumWeyl PreparationVacuumWeylDecay PreparationVacuumFourierJets
open PreparationVacuumMomentumFirst PreparationVacuumTaylor PreparationVacuumRemainder
open PreparationVacuumJetDecay PreparationVacuumGlobalN2 PreparationVacuumCompositionReadback
open CanonicalPreparationSquareCutoff CanonicalPreparationCutoff MeasureTheory Filter Set
open scoped ContDiff Topology SchwartzMap FourierTransform RealInnerProductSpace BigOperators
attribute [local irreducible] partialFourier symbolSlice

private theorem frequency_product_slice_measurable (t : ℝ) (p k : PhysicalMomentum) :
    StronglyMeasurable (fun q : PhysicalMomentum => frequencyProductIntegrand t p (q,k)) :=
  (frequencyProductIntegrand_measurable t p).comp_measurable
    (continuous_id.prodMk continuous_const).measurable

theorem frequency_product_slice_readback (t : ℝ) (p k q : PhysicalMomentum) :
    frequencyProductIntegrand t p (q,k)=compositionIntegrand t 0 p (q,k-q) := by
  simp only [frequencyProductIntegrand,compositionIntegrand,inner_zero_left,
    Real.fourierChar.map_zero_eq_one,one_smul]

private theorem compositionMajorant_marginal_le (p k q : PhysicalMomentum) :
    compositionMajorant p (q,k-q)  ≤  sourceCompositionBound p*frequencyDecay101 q := by
  rw [compositionMajorant]
  calc
    _ = (sourceCompositionBound p*frequencyDecay101 q)*frequencyDecay101 (k-q) := by rw [mul_assoc]
    _  ≤  (sourceCompositionBound p*frequencyDecay101 q)*1 :=
      mul_le_mul_of_nonneg_left (frequencyDecay101_le_one _) (mul_nonneg
        (sourceCompositionBound_nonnegative _) (frequencyDecay101_nonnegative _))
    _ = _ := mul_one _

theorem frequency_product_slice_integrable (t : ℝ) (p k : PhysicalMomentum) (time : |t| ≤ 1) :
    Integrable (fun q : PhysicalMomentum => frequencyProductIntegrand t p (q,k)) := by
  apply (frequencyDecay101_integrable.const_mul (sourceCompositionBound p)).mono
    (frequency_product_slice_measurable t p k).aestronglyMeasurable
  refine Eventually.of_forall fun q => ?_
  rw [frequency_product_slice_readback]
  exact ((compositionIntegrand_norm_bound t 0 p (q,k-q) time).trans
    (compositionMajorant_marginal_le p k q)).trans (le_abs_self _)

theorem sourceSecondMajorant_marginal_le (k q : PhysicalMomentum) :
    sourceSecondCompositionMajorant (q,k-q)  ≤  sourceSecondCompositionBound*frequencyDecay101 q := by
  rw [sourceSecondCompositionMajorant]
  calc
    _ = (sourceSecondCompositionBound*frequencyDecay101 q)*frequencyDecay101 (k-q) := by rw [mul_assoc]
    _  ≤  (sourceSecondCompositionBound*frequencyDecay101 q)*1 :=
      mul_le_mul_of_nonneg_left (frequencyDecay101_le_one _) (mul_nonneg
        sourceSecondCompositionBound_nonnegative (frequencyDecay101_nonnegative _))
    _ = _ := mul_one _

theorem pointSecondRemainder_marginal_measurable (p k : PhysicalMomentum) :
    StronglyMeasurable (fun q : PhysicalMomentum => pointSecondRemainder 0 p (q,k-q)) :=
  (pointSecondRemainder_measurable 0 p).comp_measurable
    (continuous_id.prodMk (continuous_const.sub continuous_id)).measurable

theorem pointSecondRemainder_marginal_integrable (p k : PhysicalMomentum) :
    Integrable (fun q : PhysicalMomentum => pointSecondRemainder 0 p (q,k-q)) :=
  (frequencyDecay101_integrable.const_mul sourceSecondCompositionBound).mono
    (pointSecondRemainder_marginal_measurable p k).aestronglyMeasurable
    (Eventually.of_forall fun q => ((pointSecondRemainder_norm_bound 0 p (q,k-q)).trans
      (sourceSecondMajorant_marginal_le k q)).trans (le_abs_self _))

theorem firstIntegrand_marginal_zero_integrable (p k : PhysicalMomentum) :
    Integrable (fun q : PhysicalMomentum => compositionFirstIntegrand 0 0 p (q,k-q)) := by
  have identity : (fun q : PhysicalMomentum => compositionFirstIntegrand 0 0 p (q,k-q))=
      (fun q => frequencyProductIntegrand 1 p (q,k)-frequencyProductIntegrand 0 p (q,k)-
        pointSecondRemainder 0 p (q,k-q)) := by
    funext q
    rw [frequency_product_slice_readback,frequency_product_slice_readback]
    linear_combination -(composition_point_Taylor 0 p (q,k-q))
  rw [identity]
  exact ((frequency_product_slice_integrable 1 p k (by norm_num)).sub
    (frequency_product_slice_integrable 0 p k (by norm_num))).sub (pointSecondRemainder_marginal_integrable p k)

theorem firstIntegrand_marginal_integral_zero (p k : PhysicalMomentum) :
    (∫ q : PhysicalMomentum,compositionFirstIntegrand 0 0 p (q,k-q))=0 := by
  have change := integral_sub_left_eq_self
    (fun q : PhysicalMomentum => compositionFirstIntegrand 0 0 p (q,k-q)) volume k
  have anti : (fun q : PhysicalMomentum => compositionFirstIntegrand 0 0 p (k-q,k-(k-q)))=
      (fun q => -compositionFirstIntegrand 0 0 p (q,k-q)) := by
    funext q
    rw [sub_sub_self]
    exact compositionFirstIntegrand_zero_antisymmetric 0 p q (k-q)
  rw [anti,integral_neg] at change
  linear_combination -(1/2 : ℂ)*change

theorem sourceFrequencyDefect_point_N2 (p k : PhysicalMomentum) :
    sourceFrequencyDefect p k=
      ∫ q : PhysicalMomentum,pointSecondRemainder 0 p (q,k-q) := by
  have original1 := frequency_product_slice_integrable 1 p k (by norm_num)
  have original0 := frequency_product_slice_integrable 0 p k (by norm_num)
  have first := firstIntegrand_marginal_zero_integrable p k
  calc
    _ = ∫ q : PhysicalMomentum,frequencyProductIntegrand 1 p (q,k)-frequencyProductIntegrand 0 p (q,k)-
        compositionFirstIntegrand 0 0 p (q,k-q) := by
      have lower := integral_sub original1 original0
      have upper := integral_sub (original1.sub original0) first
      simp only [Pi.sub_apply] at upper
      rw [lower,firstIntegrand_marginal_integral_zero,sub_zero] at upper
      simpa only [sourceFrequencyDefect,compositionFrequency] using upper.symm
    _ = _ := by
      apply integral_congr_ae
      refine Eventually.of_forall fun q => ?_
      dsimp only
      rw [frequency_product_slice_readback,frequency_product_slice_readback]
      exact composition_point_Taylor 0 p (q,k-q)

end LowEnergy.PreparationVacuumFrequencyN2
