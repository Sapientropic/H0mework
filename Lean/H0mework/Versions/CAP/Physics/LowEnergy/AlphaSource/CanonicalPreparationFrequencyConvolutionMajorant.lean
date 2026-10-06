import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationFrequencyMarginalTaylor

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

theorem frequencyDecay101_continuous : Continuous frequencyDecay101 := by
  unfold frequencyDecay101
  exact (continuous_const.add continuous_norm).rpow_const
    (fun k => Or.inl (ne_of_gt (by positivity : (0 : ℝ)<1+‖k‖)))

theorem sourceSecondMajorant_measurable : StronglyMeasurable sourceSecondCompositionMajorant :=
  (continuous_const.mul ((frequencyDecay101_continuous.comp continuous_fst).mul
    (frequencyDecay101_continuous.comp continuous_snd))).stronglyMeasurable

theorem sourceSecondMajorant_marginal_integrable (k : PhysicalMomentum) :
    Integrable (fun q : PhysicalMomentum => sourceSecondCompositionMajorant (q,k-q)) :=
  (frequencyDecay101_integrable.const_mul sourceSecondCompositionBound).mono
    (sourceSecondMajorant_measurable.comp_measurable
      (continuous_id.prodMk (continuous_const.sub continuous_id)).measurable).aestronglyMeasurable
    (Eventually.of_forall fun q => by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (sourceSecondCompositionMajorant_nonnegative (q,k-q))]
        using (sourceSecondMajorant_marginal_le k q).trans (le_abs_self _))

def sourceKernelMajorant (k : PhysicalMomentum) : ℝ :=
  sourceSecondCompositionBound*∫ q : PhysicalMomentum,frequencyDecay101 q*frequencyDecay101 (k-q)

theorem sourceKernelMajorant_readback (k : PhysicalMomentum) :
    sourceKernelMajorant k=∫ q : PhysicalMomentum,sourceSecondCompositionMajorant (q,k-q) := by
  rw [sourceKernelMajorant]
  change _=∫ q : PhysicalMomentum,sourceSecondCompositionBound*(frequencyDecay101 q*frequencyDecay101 (k-q))
  rw [integral_const_mul]

theorem sourceKernelMajorant_nonnegative (k : PhysicalMomentum) : 0 ≤ sourceKernelMajorant k := by
  rw [sourceKernelMajorant_readback]
  exact integral_nonneg fun q => sourceSecondCompositionMajorant_nonnegative (q,k-q)

theorem sourceKernelMajorant_measurable : StronglyMeasurable sourceKernelMajorant := by
  have sheared := sourceSecondMajorant_measurable.comp_measurable
    (continuous_fst.prodMk (continuous_snd.sub continuous_fst)).measurable
  have marginal := sheared.integral_prod_left' (μ := (volume : Measure PhysicalMomentum))
  have same : sourceKernelMajorant=(fun k : PhysicalMomentum =>
      ∫ q : PhysicalMomentum,sourceSecondCompositionMajorant (q,k-q)) := funext sourceKernelMajorant_readback
  rw [same]
  exact marginal

theorem sourceSecondMajorant_shear_integrable :
    Integrable (fun w : PhysicalMomentum × PhysicalMomentum =>
      sourceSecondCompositionMajorant (w.1,w.2-w.1)) (volume.prod volume) :=
  (measurePreserving_prod_sub (volume : Measure PhysicalMomentum) volume).integrable_comp_of_integrable
    sourceSecondCompositionMajorant_integrable

theorem sourceKernelMajorant_integrable : Integrable sourceKernelMajorant := by
  have marginal := sourceSecondMajorant_shear_integrable.integral_prod_right
  exact marginal.congr (Eventually.of_forall fun k => (sourceKernelMajorant_readback k).symm)

def sourceCompositionSchurBound : ℝ :=
  sourceSecondCompositionBound*(∫ k : PhysicalMomentum,frequencyDecay101 k)^2

theorem sourceCompositionSchurBound_nonnegative : 0 ≤ sourceCompositionSchurBound :=
  mul_nonneg sourceSecondCompositionBound_nonnegative (sq_nonneg _)

theorem sourceKernelMajorant_integral : (∫ k : PhysicalMomentum,sourceKernelMajorant k)=sourceCompositionSchurBound := by
  have shear := (measurePreserving_prod_sub (volume : Measure PhysicalMomentum) volume).integral_comp
    (MeasurableEquiv.shearSubRight PhysicalMomentum).measurableEmbedding sourceSecondCompositionMajorant
  calc
    _ = ∫ k : PhysicalMomentum,∫ q : PhysicalMomentum,sourceSecondCompositionMajorant (q,k-q) :=
      integral_congr_ae (Eventually.of_forall sourceKernelMajorant_readback)
    _ = ∫ w : PhysicalMomentum × PhysicalMomentum,sourceSecondCompositionMajorant (w.1,w.2-w.1)
        ∂volume.prod volume := (integral_prod_symm _ sourceSecondMajorant_shear_integrable).symm
    _ = ∫ w : PhysicalMomentum × PhysicalMomentum,sourceSecondCompositionMajorant w ∂volume.prod volume := shear
    _ = _ := by
      change (∫ w : PhysicalMomentum × PhysicalMomentum,
        sourceSecondCompositionBound*(frequencyDecay101 w.1*frequencyDecay101 w.2) ∂volume.prod volume)=_
      rw [integral_const_mul,integral_prod_mul,sourceCompositionSchurBound]
      simp only [pow_two]

theorem sourceFrequencyDefect_norm_bound (p k : PhysicalMomentum) :
    ‖sourceFrequencyDefect p k‖ ≤ sourceKernelMajorant k := by
  rw [sourceFrequencyDefect_point_N2,sourceKernelMajorant_readback]
  apply (norm_integral_le_integral_norm _).trans
  exact integral_mono (pointSecondRemainder_marginal_integrable p k).norm
    (sourceSecondMajorant_marginal_integrable k)
    (fun q => pointSecondRemainder_norm_bound 0 p (q,k-q))

theorem actualFullCompositionKernelDefect_norm_bound (xi eta : PhysicalMomentum) :
    ‖actualFullCompositionKernelDefect xi eta‖ ≤ sourceKernelMajorant (xi-eta) := by
  rw [actualFullCompositionKernelDefect_sourceFrequency]
  exact sourceFrequencyDefect_norm_bound _ _

end LowEnergy.PreparationVacuumFrequencyN2
