import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.InitialLog
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitMellin.ResolventSource

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3200000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Top.FiniteMellin
open Complex Filter MeasureTheory Set
open OriginalRieszFinitePairing.CoPoisson.Ward
open scoped Topology InnerProductSpace
open private mellin_source_ae scaled_mellin scaled_norm_integral power_measurable from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitMellin.ResolventSource

private theorem forward_raw (v : BurnolL2) (a : ℝ) (positive : 0 < a) :
    (ContinuousChannels.channel (-1) a v : ℝ → ℂ) =ᵐ[volume]
      fun x : ℝ => (a : ℂ)⁻¹ * v (a⁻¹ * x) := by
  filter_upwards [Lp.coeFn_smul ((Real.sqrt a : ℂ)⁻¹)
    (burnolMultiplicativeDilation (-Real.log a) v),
    burnolMultiplicativeDilation_coeFn (-Real.log a) v] with x scalar dilation
  simp only [ContinuousChannels.channel, neg_one_mul]
  rw [scalar, Pi.smul_apply, smul_eq_mul, dilation, burnolL2RawNormalizedDilation,
    Real.exp_neg, Real.exp_log positive]
  have half : Real.exp (-Real.log a / 2) = (Real.sqrt a)⁻¹ := by
    rw [neg_div, Real.exp_neg, Real.exp_half, Real.exp_log positive]
  rw [half, ofReal_inv, ← mul_assoc, ← mul_inv]
  have square : (Real.sqrt a : ℂ) * (Real.sqrt a : ℂ) = (a : ℂ) := by
    rw [← ofReal_mul, Real.mul_self_sqrt positive.le]
  rw [square]

private theorem forward_coefficient (a : ℝ) (positive : 0 < a) (z : ℂ) :
    (a : ℂ)⁻¹ * ((a⁻¹ : ℝ) : ℂ) ^ (-z) = (a : ℂ) ^ (z - 1) := by
  rw [ofReal_inv, inv_cpow_ofReal_nonneg positive.le, cpow_neg, inv_inv,
    show z - 1 = z + (-1 : ℂ) by ring, cpow_add _ _ (ofReal_ne_zero.mpr positive.ne'),
    cpow_neg, cpow_one]
  ring

private theorem channel_mellin (v : BurnolL2) (z m : ℂ) (a : ℝ) (positive : 0 < a)
    (source : HasMellin (v : ℝ → ℂ) z m) :
    HasMellin (ContinuousChannels.channel (-1) a v : ℝ → ℂ) z
      ((a : ℂ) ^ (z - 1) * m) := by
  have generated := scaled_mellin (v : ℝ → ℂ) z m (a : ℂ)⁻¹ a⁻¹ (inv_pos.mpr positive) source
  rw [forward_coefficient a positive z] at generated
  exact mellin_source_ae _ _ z _ (ae_restrict_of_ae (forward_raw v a positive)) generated

/-- The complete continuous forcing retains its actual zero-to-N integral. -/
theorem actual_normalization_mellin (v : BurnolL2) (z m : ℂ) (upper : ℝ)
    (positive : 0 < z.re) (upperPositive : 0 < upper)
    (source : HasMellin (v : ℝ → ℂ) z m) :
    HasMellin (ContinuousChannels.normalization upper v : ℝ → ℂ) z
      ((upper : ℂ) ^ z / z * m) := by
  let μa := volume.restrict (Ioc 0 upper)
  let μx := volume.restrict (Ioi (0 : ℝ))
  let family := fun a : ℝ => ContinuousChannels.channel (-1) a v
  let raw := fun p : ℝ × ℝ => (p.1 : ℂ)⁻¹ * v (p.1⁻¹ * p.2)
  have rawMeasured : Measurable raw := by
    exact (Complex.measurable_ofReal.comp measurable_fst).inv.mul
      ((Lp.stronglyMeasurable v).measurable.comp (measurable_fst.inv.mul measurable_snd))
  have actual := OriginalPaPhysicalGreen.source_l2_bochner_coeFn μa family
    (ContinuousChannels.channel_integrable (-1) upper v) raw rawMeasured (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with a inside
      exact forward_raw v a inside.1)
  have weightedMeasured : Measurable (fun p : ℝ × ℝ => (p.2 : ℂ) ^ (z - 1) * raw p) :=
    ((power_measurable (z - 1)).comp measurable_snd).mul rawMeasured
  have powerBudget : IntegrableOn (fun a : ℝ => (a : ℂ) ^ (z - 1)) (Ioc 0 upper) :=
    (intervalIntegral.intervalIntegrable_cpow' (a := 0) (b := upper)
      (by simp only [sub_re, one_re]; linarith)).1
  have joint : Integrable (fun p : ℝ × ℝ => (p.2 : ℂ) ^ (z - 1) * raw p) (μa.prod μx) := by
    apply (integrable_prod_iff weightedMeasured.aestronglyMeasurable).mpr
    refine ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with a inside
      exact (scaled_mellin (v : ℝ → ℂ) z m (a : ℂ)⁻¹ a⁻¹ (inv_pos.mpr inside.1) source).1
    · apply (powerBudget.norm.mul_const (∫ x : ℝ in Ioi 0, ‖(x : ℂ) ^ (z - 1) * v x‖)).congr
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with a inside
      dsimp only [raw]
      rw [scaled_norm_integral _ z (a : ℂ)⁻¹ a⁻¹ (inv_pos.mpr inside.1),
        forward_coefficient a inside.1 z]
  have weighted : (fun x : ℝ => (x : ℂ) ^ (z - 1) *
      (ContinuousChannels.normalization upper v : BurnolL2) x) =ᵐ[μx]
      fun x : ℝ => ∫ a : ℝ, (x : ℂ) ^ (z - 1) * raw (a, x) ∂μa := by
    filter_upwards [ae_restrict_of_ae actual] with x actualX
    change (x : ℂ) ^ (z - 1) * ((∫ a : ℝ, family a ∂μa) : BurnolL2) x = _
    rw [actualX, integral_const_mul]
  refine ⟨joint.integral_prod_right.congr weighted.symm, ?_⟩
  change (∫ x : ℝ, (x : ℂ) ^ (z - 1) *
    (ContinuousChannels.normalization upper v : BurnolL2) x ∂μx) = _
  rw [integral_congr_ae weighted, ← integral_integral_swap joint]
  have rows : (fun a : ℝ => ∫ x : ℝ, (x : ℂ) ^ (z - 1) * raw (a, x) ∂μx) =ᵐ[μa]
      fun a : ℝ => (a : ℂ) ^ (z - 1) * m := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with a inside
    have row := (scaled_mellin (v : ℝ → ℂ) z m (a : ℂ)⁻¹ a⁻¹ (inv_pos.mpr inside.1) source).2
    rw [forward_coefficient a inside.1 z] at row
    exact row
  rw [integral_congr_ae rows, integral_mul_const]
  congr 1
  change (∫ a : ℝ in Ioc 0 upper, (a : ℂ) ^ (z - 1)) = _
  rw [← intervalIntegral.integral_of_le upperPositive.le,
    integral_cpow (Or.inl (by simp only [sub_re, one_re]; linarith))]
  have nonzero : z ≠ 0 := ne_of_apply_ne re (by simpa only [zero_re] using positive.ne')
  simp only [sub_add_cancel, ofReal_zero, zero_cpow nonzero, sub_zero]

private theorem sum_mellin {ι : Type*} (index : Finset ι) (v : ι → BurnolL2) (price : ι → ℂ)
    (z : ℂ) (source : ∀ i ∈ index, HasMellin (v i : ℝ → ℂ) z (price i)) :
    HasMellin ((∑ i ∈ index, v i : BurnolL2) : ℝ → ℂ) z (∑ i ∈ index, price i) := by
  classical
  induction index using Finset.induction_on with
  | empty => simp [HasMellin, MellinConvergent, mellin]
  | @insert i index absent previous =>
    have first := source i (Finset.mem_insert_self i index)
    have rest := previous (fun j member => source j (Finset.mem_insert_of_mem member))
    have sum := hasMellin_add first.1 rest.1
    rw [first.2, rest.2] at sum
    simp only [Finset.sum_insert absent]
    exact mellin_source_ae _ _ z _ (ae_restrict_of_ae (Lp.coeFn_add (v i) (∑ j ∈ index, v j))) sum

/-- The finite original programme generates its Mellin value with every integer and continuous contact. -/
theorem actual_finite_source_mellin (v : BurnolL2) (z m : ℂ) (N : ℕ) (positiveN : 0 < N)
    (positive : 0 < z.re) (source : HasMellin (v : ℝ → ℂ) z m) :
    HasMellin (FiniteForcing.source N v : ℝ → ℂ) z
      (((∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (z - 1)) - (N : ℂ) ^ z / z) * m) := by
  have discrete := sum_mellin (Finset.Ico 1 N) (fun n : ℕ => Channels.sourceChannel n v)
    (fun n : ℕ => (n : ℂ) ^ (z - 1) * m) z (by
      intro n member
      have nPositive : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Ico.mp member).1
      simpa only [Channels.sourceChannel, ContinuousChannels.channel, neg_one_mul, Complex.ofReal_natCast] using
        channel_mellin v z m n nPositive source)
  have continuous := actual_normalization_mellin v z m N positive (by exact_mod_cast positiveN) source
  have difference := hasMellin_sub discrete.1 continuous.1
  rw [discrete.2, continuous.2, ← Finset.sum_mul, ← sub_mul] at difference
  exact mellin_source_ae _ _ z _ (ae_restrict_of_ae (Lp.coeFn_sub _ _)) difference

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Top.FiniteMellin
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
