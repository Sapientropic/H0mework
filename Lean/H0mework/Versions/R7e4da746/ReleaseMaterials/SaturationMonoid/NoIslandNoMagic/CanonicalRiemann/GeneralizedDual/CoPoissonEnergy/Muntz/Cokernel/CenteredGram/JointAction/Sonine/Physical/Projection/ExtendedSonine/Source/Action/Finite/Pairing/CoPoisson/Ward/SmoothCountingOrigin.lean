import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.TrapezoidSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.SmoothCountingOrigin

open Complex Filter MeasureTheory Set
open scoped Topology
noncomputable section
attribute [local instance 1100] NormedSpace.complexToReal
local notation "q" => (1 / 4 : ℝ)

def gridEnd (x : ℝ) : ℝ := (⌊q / x⌋₊ : ℝ) * x

theorem gridEnd_bounds (x : ℝ) (positive : 0 < x) : 0 ≤ gridEnd x ∧ gridEnd x ≤ q ∧ q - gridEnd x ≤ x := by
  refine ⟨by unfold gridEnd; positivity, ?_, ?_⟩
  · exact (le_div_iff₀ positive).mp (Nat.floor_le (by positivity))
  · have last := (div_lt_iff₀ positive).mp (Nat.lt_floor_add_one (q / x))
    unfold gridEnd
    nlinarith

theorem gridEnd_fract (x : ℝ) (positive : 0 < x) : q - gridEnd x = x * Int.fract (q / x) := by
  have floor : (⌊q / x⌋₊ : ℝ) = q / x - Int.fract (q / x) := by
    rw [natCast_floor_eq_intCast_floor (by positivity)]
    simp only [Int.fract, sub_sub_cancel]
  rw [gridEnd, floor]
  field_simp
  ring

theorem gridEnd_tendsto : Tendsto gridEnd (𝓝[>] (0 : ℝ)) (𝓝 q) := by
  have identity : Tendsto (fun x : ℝ => x) (𝓝[>] (0 : ℝ)) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have lower : Tendsto (fun x : ℝ => q - x) (𝓝[>] (0 : ℝ)) (𝓝 q) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x := q)).sub identity
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' lower tendsto_const_nhds
  · filter_upwards [self_mem_nhdsWithin] with x positive
    linarith [(gridEnd_bounds x positive).2.2]
  · filter_upwards [self_mem_nhdsWithin] with x positive
    exact (gridEnd_bounds x positive).2.1

theorem grid_tendsto (f f' : ℝ → ℂ) (regular : ContinuousOn f (Icc 0 q))
    (regular' : ContinuousOn f' (Icc 0 q))
    (derivative : ∀ t ∈ Icc 0 q, HasDerivAt f (f' t) t) :
    Tendsto (fun x : ℝ => TrapezoidSource.grid f x ⌊q / x⌋₊) (𝓝[>] 0) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro epsilon positiveE
  obtain ⟨delta, positiveD, control⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous regular') epsilon positiveE
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds positiveD)] with x positive small
  have actual := TrapezoidSource.grid_bound f f' regular derivative x epsilon positive positiveE.le
    ⌊q / x⌋₊ (gridEnd_bounds x positive).2.1 (fun a ha b hb close => by
      have short : dist b a < delta := by rw [dist_eq_norm]; exact close.trans_lt small
      simpa only [dist_eq_norm] using (control b hb a ha short).le)
  rw [dist_zero_right]
  exact actual.trans_lt (by norm_num; linarith)

def tailError (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (x : ℂ)⁻¹ * ∫ t : ℝ in (gridEnd x)..q, f t - f q

theorem tail_bound (f : ℝ → ℂ) (L : ℝ) (nonnegative : 0 ≤ L)
    (lipschitz : ∀ a ∈ Icc 0 q, ∀ b ∈ Icc 0 q, ‖f b - f a‖ ≤ L * ‖b - a‖)
    (x : ℝ) (positive : 0 < x) : ‖tailError f x‖ ≤ L * x := by
  have bounds := gridEnd_bounds x positive
  have actual := intervalIntegral.norm_integral_le_of_norm_le_const (a := gridEnd x) (b := q)
    (C := L * x) (f := fun t => f t - f q) (fun t located => by
      have inside : t ∈ Icc (gridEnd x) q := Ioc_subset_Icc_self
        (by simpa only [uIoc_of_le bounds.2.1] using located)
      have estimate := lipschitz q (by norm_num) t ⟨bounds.1.trans inside.1, inside.2⟩
      rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr inside.2)] at estimate
      exact estimate.trans (mul_le_mul_of_nonneg_left (by linarith [inside.1, bounds.2.2]) nonnegative))
  rw [abs_of_nonneg (sub_nonneg.mpr bounds.2.1)] at actual
  unfold tailError
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos positive]
  calc
    _ ≤ x⁻¹ * (L * x * (q - gridEnd x)) := mul_le_mul_of_nonneg_left actual (inv_nonneg.mpr positive.le)
    _ = L * (q - gridEnd x) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left bounds.2.2 nonnegative

theorem tail_tendsto (f : ℝ → ℂ) (L : ℝ) (nonnegative : 0 ≤ L)
    (lipschitz : ∀ a ∈ Icc 0 q, ∀ b ∈ Icc 0 q, ‖f b - f a‖ ≤ L * ‖b - a‖) :
    Tendsto (tailError f) (𝓝[>] 0) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have identity : Tendsto (fun x : ℝ => x) (𝓝[>] (0 : ℝ)) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have upper : Tendsto (fun x : ℝ => L * x) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero] using identity.const_mul L
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ upper
  filter_upwards [self_mem_nhdsWithin] with x positive
  exact tail_bound f L nonnegative lipschitz x positive

def error (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (∑ n ∈ Finset.Icc 1 ⌊q / x⌋₊, f ((n : ℝ) * x)) -
    (x : ℂ)⁻¹ * (∫ t : ℝ in (0 : ℝ)..q, f t) -
      f q * ((1 / 2 : ℂ) - ((Int.fract (q / x) : ℝ) : ℂ)) + f 0 / 2

theorem error_decomposition (f : ℝ → ℂ) (regular : ContinuousOn f (Icc 0 q))
    (x : ℝ) (positive : 0 < x) : error f x =
    TrapezoidSource.grid f x ⌊q / x⌋₊ + (f (gridEnd x) - f q) / 2 - tailError f x := by
  have bounds := gridEnd_bounds x positive
  have first : IntervalIntegrable f volume 0 (gridEnd x) :=
    (regular.mono (Icc_subset_Icc le_rfl bounds.2.1)).intervalIntegrable_of_Icc bounds.1
  have second : IntervalIntegrable f volume (gridEnd x) q :=
    (regular.mono (Icc_subset_Icc bounds.1 le_rfl)).intervalIntegrable_of_Icc bounds.2.1
  have split := intervalIntegral.integral_add_adjacent_intervals first second
  have last : (∫ t : ℝ in (gridEnd x)..q, f t - f q) =
      (∫ t : ℝ in (gridEnd x)..q, f t) - (q - gridEnd x) • f q := by
    rw [intervalIntegral.integral_sub second intervalIntegrable_const, intervalIntegral.integral_const]
  unfold error TrapezoidSource.grid tailError
  rw [last, ← split, gridEnd_fract x positive]
  simp only [Complex.real_smul, ofReal_mul]
  change _ = (∑ n ∈ Finset.Icc 1 ⌊q / x⌋₊, f ((n : ℝ) * x)) -
    (x : ℂ)⁻¹ * (∫ t : ℝ in (0 : ℝ)..gridEnd x, f t) - (f (gridEnd x) - f 0) / 2 +
    (f (gridEnd x) - f q) / 2 -
    (x : ℂ)⁻¹ * ((∫ t : ℝ in (gridEnd x)..q, f t) - (x : ℂ) * ((Int.fract (q / x) : ℝ) : ℂ) * f q)
  field_simp [Complex.ofReal_ne_zero.mpr positive.ne']
  ring

/-- The closed-floor sum retains its endpoint sawtooth; only its genuine quadrature error tends to zero. -/
theorem error_tendsto (f f' : ℝ → ℂ) (regular : ContinuousOn f (Icc 0 q))
    (regular' : ContinuousOn f' (Icc 0 q))
    (derivative : ∀ t ∈ Icc 0 q, HasDerivAt f (f' t) t)
    (L : ℝ) (nonnegative : 0 ≤ L)
    (lipschitz : ∀ a ∈ Icc 0 q, ∀ b ∈ Icc 0 q, ‖f b - f a‖ ≤ L * ‖b - a‖) :
    Tendsto (error f) (𝓝[>] 0) (𝓝 0) := by
  have endpoint := ((derivative q (by norm_num)).continuousAt.tendsto).comp gridEnd_tendsto
  have boundary := (endpoint.sub_const (f q)).div_const (2 : ℂ)
  simp only [sub_self, zero_div] at boundary
  have actual := ((grid_tendsto f f' regular regular' derivative).add boundary).sub
    (tail_tendsto f L nonnegative lipschitz)
  simp only [add_zero, sub_zero] at actual
  apply actual.congr'
  filter_upwards [self_mem_nhdsWithin] with x positive
  exact (error_decomposition f regular x positive).symm

end
end OriginalRieszFinitePairing.CoPoisson.Ward.SmoothCountingOrigin
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
