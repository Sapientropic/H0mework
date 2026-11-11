import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.HMellinFinite

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.HMellin

open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace
noncomputable section
local notation "q" => (1 / 4 : ℝ)

private def envelope (s : ℂ) (x : ℝ) : ℝ :=
  (Ioc 0 1).indicator (fun x : ℝ => x ^ (-s.re)) x +
    (Ioi 1).indicator (fun x : ℝ => q * x ^ (-s.re - 1)) x

private theorem envelope_integrable (s : ℂ) (positive : 0 < s.re) (below : s.re < 1) :
    IntegrableOn (envelope s) (Ioi 0) := by
  have head := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := (1 : ℝ))
    (by linarith : -1 < -s.re)).def'
  rw [uIoc_of_le zero_le_one] at head
  have tail := (integrableOn_Ioi_rpow_of_lt (by linarith : -s.re - 1 < -1) (by norm_num : (0 : ℝ) < 1)).const_mul q
  have first : Integrable ((Ioc (0 : ℝ) 1).indicator (fun x => x ^ (-s.re))) (volume.restrict (Ioi 0)) := by
    rw [integrable_indicator_iff measurableSet_Ioc, IntegrableOn,
      Measure.restrict_restrict measurableSet_Ioc, inter_eq_left.mpr Ioc_subset_Ioi_self]
    exact head
  have second : Integrable ((Ioi (1 : ℝ)).indicator (fun x => q * x ^ (-s.re - 1))) (volume.restrict (Ioi 0)) := by
    rw [integrable_indicator_iff measurableSet_Ioi, IntegrableOn,
      Measure.restrict_restrict measurableSet_Ioi, inter_eq_left.mpr (Ioi_subset_Ioi zero_le_one)]
    exact tail
  exact first.add second

private theorem weighted_bound (s : ℂ) (x : ℝ) (positive : 0 < x) (value : ℂ)
    (bounded : ‖value‖ ≤ 1 ∧ ‖value‖ ≤ q / |x|) :
    ‖(x : ℂ) ^ (-s) * value‖ ≤ envelope s x := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos positive, neg_re]
  unfold envelope
  by_cases head : x ≤ 1
  · rw [indicator_of_mem (show x ∈ Ioc 0 1 from ⟨positive, head⟩),
      indicator_of_notMem (show x ∉ Ioi 1 from not_lt.mpr head), add_zero]
    exact (mul_le_mul_of_nonneg_left bounded.1 (Real.rpow_nonneg positive.le _)).trans_eq (mul_one _)
  · have large : 1 < x := lt_of_not_ge head
    rw [indicator_of_notMem (show x ∉ Ioc 0 1 from fun h => head h.2),
      indicator_of_mem (show x ∈ Ioi 1 from large), zero_add,
      Real.rpow_sub_one positive.ne']
    rw [abs_of_pos positive] at bounded
    exact (mul_le_mul_of_nonneg_left bounded.2 (Real.rpow_nonneg positive.le _)).trans_eq (by ring)

/-- The complete min(1,q/x) source bound pays Mellin integrability at both ends. -/
theorem integrable (s : ℂ) (positive : 0 < s.re) (below : s.re < 1) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s) * ConstantDual.sawtoothRaw x) (Ioi 0) := by
  apply (envelope_integrable s positive below).mono'
    (((by fun_prop : Measurable (fun x : ℝ => (x : ℂ) ^ (-s))).mul ConstantDual.sawtooth_measurable).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact weighted_bound s x hx _ (ConstantDual.sawtooth_bounds x)

theorem finite_integrable (s : ℂ) (positive : 0 < s.re) (below : s.re < 1) (N : ℕ) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s) * ConstantDual.finiteRaw N x) (Ioi 0) := by
  apply (envelope_integrable s positive below).mono'
    (((by fun_prop : Measurable (fun x : ℝ => (x : ℂ) ^ (-s))).mul (ConstantDual.finite_measurable N)).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact weighted_bound s x hx _ (ConstantDual.finite_bounds N x)

/-- The actual finite source reaches the full Mellin integral by weighted L¹ dominated convergence. -/
theorem integral_tendsto (s : ℂ) (positive : 0 < s.re) (below : s.re < 1) :
    Tendsto (fun N : ℕ => ∫ x : ℝ in Ioi 0, (x : ℂ) ^ (-s) * ConstantDual.finiteRaw N x) atTop
      (𝓝 (∫ x : ℝ in Ioi 0, (x : ℂ) ^ (-s) * ConstantDual.sawtoothRaw x)) := by
  apply tendsto_integral_of_dominated_convergence (envelope s)
    (fun N => (finite_integrable s positive below N).aestronglyMeasurable)
    (envelope_integrable s positive below)
  · intro N
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact weighted_bound s x hx _ (ConstantDual.finite_bounds N x)
  · filter_upwards with x
    apply tendsto_const_nhds.congr'
    filter_upwards [ConstantDual.finite_eventually x] with N same
    rw [same]

/-- The original zero and functional equation pay the H Mellin value, with no vanishing input. -/
theorem original_zero (coordinate : BurnolCompletedMellinCoordinate) (zero : riemannZeta coordinate.value = 0) :
    (∫ x : ℝ in Ioi 0, (x : ℂ) ^ (-star coordinate.value) * ConstantDual.sawtoothRaw x) = 0 := by
  have positive : 0 < (star coordinate.value).re := by
    simp only [star_def, conj_re]
    linarith [coordinate.rightHalf]
  have below : (star coordinate.value).re < 1 := by simpa only [star_def, conj_re] using coordinate.belowOne
  have source := integral_tendsto (star coordinate.value) positive below
  have arithmetic := (DirichletCoefficient.original_coefficient_limits coordinate zero).2.const_mul
    ((q : ℂ) ^ (1 - star coordinate.value) / (1 - star coordinate.value))
  simp only [mul_zero] at arithmetic
  have actual := arithmetic.congr' (Eventually.of_forall (fun N => (finite_integral _ positive below N).symm))
  exact tendsto_nhds_unique source actual

end
end OriginalRieszFinitePairing.CoPoisson.Ward.HMellin
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
