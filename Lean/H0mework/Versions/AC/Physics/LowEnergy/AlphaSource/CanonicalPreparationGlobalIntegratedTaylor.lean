import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationJetIntegrability

set_option autoImplicit false
set_option maxHeartbeats 240000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumGlobalN2
open PreparationVacuumWeyl PreparationVacuumWeylDecay PreparationVacuumFourierJets
open PreparationVacuumMomentumFirst PreparationVacuumTaylor PreparationVacuumRemainder
open PreparationVacuumJetDecay CanonicalPreparationSquareCutoff CanonicalPreparationCutoff
open MeasureTheory Filter Set
open scoped ContDiff Topology SchwartzMap FourierTransform RealInnerProductSpace BigOperators
attribute [local irreducible] partialFourier symbolSlice

theorem sourceSecondCompositionMajorant_nonnegative (w : PhysicalMomentum × PhysicalMomentum) :
    0  ≤  sourceSecondCompositionMajorant w :=
  mul_nonneg sourceSecondCompositionBound_nonnegative
    (mul_nonneg (frequencyDecay101_nonnegative _) (frequencyDecay101_nonnegative _))

theorem compositionSecondIntegrand_joint_time_measurable (z p : PhysicalMomentum) :
    StronglyMeasurable (fun tw : ℝ × (PhysicalMomentum × PhysicalMomentum) =>
      compositionSecondIntegrand tw.1 z p tw.2) :=
  stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
    (fun w => compositionSecondIntegrand_continuous z p w)
    (fun t => compositionSecondIntegrand_measurable t z p)

theorem weightedSecondIntegrand_joint_measurable (z p : PhysicalMomentum) :
    StronglyMeasurable (fun tw : ℝ × (PhysicalMomentum × PhysicalMomentum) =>
      (1-tw.1) • compositionSecondIntegrand tw.1 z p tw.2) :=
  (continuous_const.sub continuous_fst).stronglyMeasurable.smul
    (compositionSecondIntegrand_joint_time_measurable z p)

theorem weightedSecondIntegrand_norm_bound (t : ℝ) (z p : PhysicalMomentum)
    (w : PhysicalMomentum × PhysicalMomentum) (time : t∈uIoc (0 : ℝ) 1) :
    ‖(1-t) • compositionSecondIntegrand t z p w‖  ≤  sourceSecondCompositionMajorant w := by
  have interval : 0<t ∧ t ≤ 1 := by simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1),mem_Ioc] using time
  have unit : |t| ≤ 1 := by rw [abs_of_pos interval.1]; exact interval.2
  have factor : |1-t| ≤ 1 := by rw [abs_of_nonneg (by linarith : 0 ≤ 1-t)]; linarith
  rw [norm_smul,Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_right factor (norm_nonneg _)).trans
    (by simpa only [one_mul] using compositionSecondIntegrand_norm_bound t z p w unit)

theorem pointSecondRemainder_measurable (z p : PhysicalMomentum) :
    StronglyMeasurable (pointSecondRemainder z p) := by
  have original := (weightedSecondIntegrand_joint_measurable z p).integral_prod_left'
    (μ := volume.restrict (Ioc (0 : ℝ) 1))
  have same : pointSecondRemainder z p=(fun w : PhysicalMomentum × PhysicalMomentum =>
      ∫ t in Ioc (0 : ℝ) 1,(1-t) • compositionSecondIntegrand t z p w) := by
    funext w
    rw [pointSecondRemainder,intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [same]
  exact original

theorem pointSecondRemainder_norm_bound (z p : PhysicalMomentum)
    (w : PhysicalMomentum × PhysicalMomentum) :
    ‖pointSecondRemainder z p w‖  ≤  sourceSecondCompositionMajorant w := by
  have bound := intervalIntegral.norm_integral_le_of_norm_le_const
    (fun t time => weightedSecondIntegrand_norm_bound t z p w time)
  simpa only [pointSecondRemainder,sub_zero,abs_one,mul_one] using bound

theorem pointSecondRemainder_integrable (z p : PhysicalMomentum) :
    Integrable (pointSecondRemainder z p) (volume.prod volume) :=
  sourceSecondCompositionMajorant_integrable.mono (pointSecondRemainder_measurable z p).aestronglyMeasurable
    (Eventually.of_forall fun w => (pointSecondRemainder_norm_bound z p w).trans (le_abs_self _))

theorem compositionFirstIntegrand_zero_integrable (z p : PhysicalMomentum) :
    Integrable (compositionFirstIntegrand 0 z p) (volume.prod volume) := by
  have identity : compositionFirstIntegrand 0 z p=(fun w =>
      compositionIntegrand 1 z p w-compositionIntegrand 0 z p w-pointSecondRemainder z p w) := by
    funext w
    linear_combination -(composition_point_Taylor z p w)
  rw [identity]
  exact ((compositionIntegrand_integrable 1 z p (by norm_num)).sub
    (compositionIntegrand_integrable 0 z p (by norm_num))).sub (pointSecondRemainder_integrable z p)

theorem compositionFirst_integral_zero (z p : PhysicalMomentum) :
    (∫ w : PhysicalMomentum × PhysicalMomentum,compositionFirstIntegrand 0 z p w ∂volume.prod volume)=0 := by
  have symmetry := integral_prod_swap (μ := (volume : Measure PhysicalMomentum))
    (ν := (volume : Measure PhysicalMomentum)) (compositionFirstIntegrand 0 z p)
  have anti : (fun w : PhysicalMomentum × PhysicalMomentum => compositionFirstIntegrand 0 z p w.swap)=
      (fun w => -compositionFirstIntegrand 0 z p w) := by
    funext w
    exact compositionFirstIntegrand_zero_antisymmetric z p w.1 w.2
  rw [anti,integral_neg] at symmetry
  linear_combination -(1/2 : ℂ)*symmetry

theorem compositionFamily_point_N2 (z p : PhysicalMomentum) :
    compositionFamily 1 z p-compositionFamily 0 z p=
      ∫ w : PhysicalMomentum × PhysicalMomentum,pointSecondRemainder z p w ∂volume.prod volume := by
  have first := compositionFirstIntegrand_zero_integrable z p
  have original0 := compositionIntegrand_integrable 0 z p (by norm_num)
  have original1 := compositionIntegrand_integrable 1 z p (by norm_num)
  calc
    _ = ∫ w : PhysicalMomentum × PhysicalMomentum,
        compositionIntegrand 1 z p w-compositionIntegrand 0 z p w-compositionFirstIntegrand 0 z p w
        ∂volume.prod volume := by
      have lower := integral_sub original1 original0
      have upper := integral_sub (original1.sub original0) first
      simp only [Pi.sub_apply] at upper
      rw [lower,compositionFirst_integral_zero,sub_zero] at upper
      simpa only [compositionFamily,Pi.sub_apply] using upper.symm
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall (composition_point_Taylor z p)

theorem weightedSecondIntegrand_integrable (z p : PhysicalMomentum) :
    Integrable (fun tw : ℝ × (PhysicalMomentum × PhysicalMomentum) =>
      (1-tw.1) • compositionSecondIntegrand tw.1 z p tw.2)
      ((volume.restrict (uIoc (0 : ℝ) 1)).prod (volume.prod volume)) := by
  have timeIntegral : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (uIoc (0 : ℝ) 1)) := by
    exact integrableOn_const (by simp)
  have dominant := timeIntegral.mul_prod sourceSecondCompositionMajorant_integrable
  have inTime : ∀ᵐ tw : ℝ × (PhysicalMomentum × PhysicalMomentum)
      ∂(volume.restrict (uIoc (0 : ℝ) 1)).prod (volume.prod volume), tw.1∈uIoc (0 : ℝ) 1 := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_uIoc.preimage measurable_fst)).mpr
    exact (ae_restrict_mem measurableSet_uIoc).mono fun t ht => Eventually.of_forall fun _ => ht
  apply dominant.mono (weightedSecondIntegrand_joint_measurable z p).aestronglyMeasurable
  filter_upwards [inTime] with tw htime
  simpa only [one_mul,Real.norm_eq_abs] using
    (weightedSecondIntegrand_norm_bound tw.1 z p tw.2 htime).trans (le_abs_self _)

def compositionSecondFamily (t : ℝ) (z p : PhysicalMomentum) : ℂ :=
  ∫ w : PhysicalMomentum × PhysicalMomentum,compositionSecondIntegrand t z p w ∂volume.prod volume

theorem compositionFamily_global_N2 (z p : PhysicalMomentum) :
    compositionFamily 1 z p-compositionFamily 0 z p=
      ∫ t in (0 : ℝ)..1,(1-t) • compositionSecondFamily t z p := by
  rw [compositionFamily_point_N2]
  have swap := intervalIntegral_integral_swap
    (f := fun t w => (1-t) • compositionSecondIntegrand t z p w)
    (a := (0 : ℝ)) (b := 1) (μ := volume.prod volume) (weightedSecondIntegrand_integrable z p)
  have literal : (fun t : ℝ => ∫ w : PhysicalMomentum × PhysicalMomentum,
      (1-t) • compositionSecondIntegrand t z p w ∂volume.prod volume)=
      (fun t => (1-t) • compositionSecondFamily t z p) := by
    funext t
    rw [integral_smul]
    rfl
  rw [literal] at swap
  exact swap.symm

theorem sourceFullCompositionDefect_global_N2 (z : FlatConfiguration) (p : PhysicalMomentum) :
    sourceFullCompositionDefect z p=
      ∫ t in (0 : ℝ)..1,(1-t) • compositionSecondFamily t (flatPosition.symm z) p :=
  compositionFamily_global_N2 _ _

theorem sourceFullCompositionDefect_order_zero (z : FlatConfiguration) (p : PhysicalMomentum) :
    ‖sourceFullCompositionDefect z p‖  ≤
      sourceSecondCompositionBound*(∫ k : PhysicalMomentum,frequencyDecay101 k)^2 := by
  change ‖compositionFamily 1 (flatPosition.symm z) p-compositionFamily 0 (flatPosition.symm z) p‖ ≤ _
  rw [compositionFamily_point_N2]
  apply (norm_integral_le_integral_norm _).trans
  calc
    _  ≤  ∫ w : PhysicalMomentum × PhysicalMomentum,sourceSecondCompositionMajorant w ∂volume.prod volume :=
      integral_mono (pointSecondRemainder_integrable _ _).norm sourceSecondCompositionMajorant_integrable
        (fun w => pointSecondRemainder_norm_bound _ _ w)
    _ = _ := by
      change (∫ w : PhysicalMomentum × PhysicalMomentum,
        sourceSecondCompositionBound*(frequencyDecay101 w.1*frequencyDecay101 w.2) ∂volume.prod volume)=_
      rw [integral_const_mul,integral_prod_mul]
      simp only [pow_two]

end LowEnergy.PreparationVacuumGlobalN2
