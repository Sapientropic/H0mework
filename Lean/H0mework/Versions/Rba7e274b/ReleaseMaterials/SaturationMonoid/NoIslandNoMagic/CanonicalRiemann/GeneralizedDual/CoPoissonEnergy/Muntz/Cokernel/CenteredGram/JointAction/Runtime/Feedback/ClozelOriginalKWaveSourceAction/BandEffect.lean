import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKWaveSourceAction.BandRead
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKWaveSourceAction.Primitive
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWaveSourceAction
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalRieszFinitePairing OriginalPaPhysicalGreen
local notation "q" => (1 / 4 : ℝ)

private theorem actual_tail_kernel_represents (coordinate : BurnolCompletedMellinCoordinate) :
    (burnolMellinTailKernelL2 coordinate.value coordinate.rightHalf : ℝ → ℂ) =ᵐ[volume]
      burnolMellinTailKernelRaw coordinate.value :=
  (burnolMellinTailKernelRaw_memLp coordinate.value coordinate.rightHalf).coeFn_toLp

private theorem actual_tate_tail_star_represents (coordinate : BurnolCompletedMellinCoordinate) :
    (fun x : ℝ => star ((burnolTateReciprocalL2
      (burnolMellinTailKernelL2 coordinate.value coordinate.rightHalf) : BurnolL2) x)) =ᵐ[volume]
      (fun x : ℝ => ((|x| : ℝ) : ℂ)⁻¹ *
        (if q < x⁻¹ then ((x⁻¹ : ℝ) : ℂ) ^ (-coordinate.value) else 0)) := by
  have original := actual_tail_kernel_represents coordinate
  have pulled := burnolTateReciprocalRaw_ae_congr
    (Lp.memLp (burnolMellinTailKernelL2 coordinate.value coordinate.rightHalf))
    ((Lp.memLp (burnolMellinTailKernelL2 coordinate.value coordinate.rightHalf)).ae_eq original) original
  filter_upwards [burnolTateReciprocalL2_coeFn
    (burnolMellinTailKernelL2 coordinate.value coordinate.rightHalf), pulled] with x actual raw
  rw [actual, raw]
  unfold burnolTateReciprocalRaw
  rw [star_mul, star_inv₀, show star ((|x| : ℝ) : ℂ) = ((|x| : ℝ) : ℂ) by
      simpa only [Complex.star_def] using Complex.conj_ofReal |x|,
    star_burnolMellinTailKernelRaw]
  change (if q < x⁻¹ then ((x⁻¹ : ℝ) : ℂ) ^ (-coordinate.value) else 0) *
    ((|x| : ℝ) : ℂ)⁻¹ = _
  ring

private theorem actual_tate_tail_on_band (coordinate : BurnolCompletedMellinCoordinate)
    (h x : ℝ) (bounded : h ≤ Real.log 2) (inside : x ∈ Ioc q (q * Real.exp h)) :
    ((|x| : ℝ) : ℂ)⁻¹ *
      (if q < x⁻¹ then ((x⁻¹ : ℝ) : ℂ) ^ (-coordinate.value) else 0) =
      (x : ℂ) ^ (coordinate.value - 1) := by
  have positive : 0 < x := lt_trans (by norm_num : (0 : ℝ) < q) inside.1
  have exponential : Real.exp h ≤ 2 := by
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using Real.exp_le_exp.mpr bounded
  have below : x < 4 := by nlinarith [inside.2]
  have inverse : q < x⁻¹ := by
    have actual := (inv_lt_inv₀ (by norm_num : (0 : ℝ) < 4) positive).mpr below
    norm_num at actual
    exact actual
  rw [if_pos inverse, abs_of_pos positive, Complex.ofReal_inv,
    Complex.inv_cpow_ofReal_nonneg positive.le, ← Complex.cpow_neg, neg_neg]
  rw [show coordinate.value - 1 = -1 + coordinate.value by ring,
    Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr positive.ne'), Complex.cpow_neg_one]

private theorem actual_tail_star_represents (coordinate : BurnolCompletedMellinCoordinate) :
    (fun x : ℝ => star ((burnolMellinTailKernelL2 coordinate.value coordinate.rightHalf : BurnolL2) x)) =ᵐ[volume]
      fun x : ℝ => if q < x then (x : ℂ) ^ (-coordinate.value) else 0 := by
  filter_upwards [actual_tail_kernel_represents coordinate] with x source
  rw [source, star_burnolMellinTailKernelRaw]
  rfl

private theorem original_band_two_input_effect (coordinate : BurnolCompletedMellinCoordinate)
    (h x : ℝ) (bounded : h ≤ Real.log 2) :
    (((|x| : ℝ) : ℂ)⁻¹ *
        (if q < x⁻¹ then ((x⁻¹ : ℝ) : ℂ) ^ (-coordinate.value) else 0)) *
        CoPoisson.bandRaw h (positionSource coordinate) x =
      (Ioc q (q * Real.exp h)).indicator
        (fun t : ℝ => -(Real.exp (-h / 2) : ℂ) * (t : ℂ) ^ (coordinate.value - 1) *
          positionSource coordinate (Real.exp (-h) * t)) x ∧
    (if q < x then (x : ℂ) ^ (-coordinate.value) else 0) *
        CoPoisson.bandRaw h (burnolRieszSingleFourierSourceRaw coordinate) x =
      (Ioc q (q * Real.exp h)).indicator
        (fun t : ℝ => -(Real.exp (-h / 2) : ℂ) * (t : ℂ) ^ (-coordinate.value) *
          burnolRieszSingleFourierSourceRaw coordinate (Real.exp (-h) * t)) x := by
  by_cases inside : x ∈ Ioc q (q * Real.exp h)
  · have positive : 0 < x := lt_trans (by norm_num : (0 : ℝ) < q) inside.1
    have active : q < |x| ∧ |x| ≤ q * Real.exp h := by rwa [abs_of_pos positive]
    rw [actual_tate_tail_on_band coordinate h x bounded inside, if_pos inside.1,
      indicator_of_mem inside, indicator_of_mem inside]
    constructor
    · rw [CoPoisson.bandRaw, if_pos active, abs_of_pos positive]
      ring
    · rw [CoPoisson.bandRaw, if_pos active, abs_of_pos positive]
      ring
  · rw [indicator_of_notMem inside, indicator_of_notMem inside]
    by_cases active : q < |x| ∧ |x| ≤ q * Real.exp h
    · have nonpositive : x ≤ 0 := by
        by_contra contrary
        have positive : 0 < x := lt_of_not_ge contrary
        have member : x ∈ Ioc q (q * Real.exp h) := by
          change q < x ∧ x ≤ q * Real.exp h
          simpa only [abs_of_pos positive] using active
        exact inside member
      have noLeft : ¬q < x⁻¹ := not_lt_of_ge ((inv_nonpos.mpr nonpositive).trans (by norm_num))
      have noRight : ¬q < x := not_lt_of_ge (nonpositive.trans (by norm_num))
      rw [if_neg noLeft, if_neg noRight, mul_zero, zero_mul, zero_mul]
      exact ⟨rfl, rfl⟩
    · simp only [CoPoisson.bandRaw, if_neg active, mul_zero, true_and]

theorem actual_original_coefficient_band_effect (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    burnolPaResolventSourceCoefficient coordinate
      (OriginalCommonInverseForcing.SourceJoint.upperSourceWaveAmbient coordinate h nonnegative bounded) =
      (2 : ℂ) * OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h *
        ((∫ x : ℝ in q..(q * Real.exp h), -(Real.exp (-h / 2) : ℂ) *
          (x : ℂ) ^ (coordinate.value - 1) * positionSource coordinate (Real.exp (-h) * x)) +
        ∫ x : ℝ in q..(q * Real.exp h), -(Real.exp (-h / 2) : ℂ) *
          (x : ℂ) ^ (-coordinate.value) * burnolRieszSingleFourierSourceRaw coordinate (Real.exp (-h) * x)) := by
  rw [actual_original_coefficient_band_source_read]
  have ordered : q ≤ q * Real.exp h := by nlinarith [Real.one_le_exp_iff.mpr nonnegative]
  have positionRead : (∫ x : ℝ, inner ℂ
      ((burnolTateReciprocalL2 (burnolMellinTailKernelL2 coordinate.value coordinate.rightHalf) : BurnolL2) x)
      (CoPoisson.bandRaw h (positionSource coordinate) x)) =
      ∫ x : ℝ in q..(q * Real.exp h), -(Real.exp (-h / 2) : ℂ) *
        (x : ℂ) ^ (coordinate.value - 1) * positionSource coordinate (Real.exp (-h) * x) := by
    rw [intervalIntegral.integral_of_le ordered, ← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    filter_upwards [actual_tate_tail_star_represents coordinate] with x source
    rw [RCLike.inner_apply, starRingEnd_apply, source, mul_comm]
    exact (original_band_two_input_effect coordinate h x bounded).1
  have fourierRead : (∫ x : ℝ, inner ℂ
      ((burnolMellinTailKernelL2 coordinate.value coordinate.rightHalf : BurnolL2) x)
      (CoPoisson.bandRaw h (burnolRieszSingleFourierSourceRaw coordinate) x)) =
      ∫ x : ℝ in q..(q * Real.exp h), -(Real.exp (-h / 2) : ℂ) *
        (x : ℂ) ^ (-coordinate.value) * burnolRieszSingleFourierSourceRaw coordinate (Real.exp (-h) * x) := by
    rw [intervalIntegral.integral_of_le ordered, ← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    filter_upwards [actual_tail_star_represents coordinate] with x source
    rw [RCLike.inner_apply, starRingEnd_apply, source, mul_comm]
    exact (original_band_two_input_effect coordinate h x bounded).2
  rw [positionRead, fourierRead]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWaveSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
