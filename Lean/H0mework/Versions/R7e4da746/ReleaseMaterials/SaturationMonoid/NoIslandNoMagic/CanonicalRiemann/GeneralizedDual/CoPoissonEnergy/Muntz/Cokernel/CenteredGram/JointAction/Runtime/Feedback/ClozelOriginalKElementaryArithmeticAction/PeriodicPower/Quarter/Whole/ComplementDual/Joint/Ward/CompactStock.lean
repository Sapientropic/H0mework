import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.Reverse

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward

open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszFinitePairing.CoPoisson.Ward OriginalPaPhysicalGreen
open scoped Topology
local notation "q" => (1 / 4 : ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "E" => burnolQuarterZeroExtension

def compactRaw (state : Hq) : ℝ → ℂ := (symmetricInterval q).indicator (state : ℝ → ℂ)

theorem compact_normalization_raw (state : Hq) (N : ℕ) :
    ((∫ a : ℝ in Ioc 0 (N : ℝ), ContinuousChannels.channel 1 a (E state) : BurnolL2) : ℝ → ℂ)
      =ᵐ[volume] fun x => ∫ a : ℝ in Ioc 0 (N : ℝ), compactRaw state (a * x) := by
  have measurable : Measurable (compactRaw state) :=
    (Lp.stronglyMeasurable state).measurable.indicator (measurableSet_symmetricInterval q)
  apply source_l2_bochner_coeFn (volume.restrict (Ioc 0 (N : ℝ))) _
    (ContinuousChannels.channel_integrable 1 N (E state))
    (fun point : ℝ × ℝ => compactRaw state (point.1 * point.2))
    (measurable.comp (by fun_prop))
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with a inside
  exact DualSourceRaw.channel_coeFn _ _ (burnolQuarterZeroExtension_coe state) a inside.1

/-- The finite continuous source has fully covered the compact input at every annulus point. -/
theorem compact_normalization_positive (state : Hq) (N : ℕ) (one : 1 ≤ N)
    (x : ℝ) (outside : q < x) :
    (∫ a : ℝ in Ioc 0 (N : ℝ), compactRaw state (a * x)) =
      (x : ℂ)⁻¹ * ∫ u : ℝ in Ioc 0 q, state u := by
  have positive : 0 < x := (by norm_num : (0 : ℝ) < q).trans outside
  have large : (1 : ℝ) ≤ N := by exact_mod_cast one
  have covered : q ≤ (N : ℝ) * x := by nlinarith
  have scaled : (∫ a : ℝ in Ioc 0 (N : ℝ), compactRaw state (a * x)) =
      x⁻¹ • ∫ u : ℝ in Ioc 0 ((N : ℝ) * x), compactRaw state u := by
    rw [← intervalIntegral.integral_of_le (Nat.cast_nonneg N),
      intervalIntegral.integral_comp_mul_right _ positive.ne', zero_mul,
      intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ (N : ℝ) * x)]
  have pointwise : EqOn (compactRaw state) ((Ioc 0 q).indicator (state : ℝ → ℂ))
      (Ioc 0 ((N : ℝ) * x)) := by
    intro u inside
    have lower : -q ≤ u := by linarith [inside.1]
    simp only [compactRaw, symmetricInterval, indicator_apply, mem_Icc, mem_Ioc,
      lower, inside.1, true_and]
  rw [scaled, setIntegral_congr_fun measurableSet_Ioc pointwise,
    integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.mpr (Ioc_subset_Ioc le_rfl covered)]
  simp only [Complex.real_smul, Complex.ofReal_inv]

/-- Integer invisibility pays a genuine ordinary-mass rank in the whole same-N commutator. -/
theorem actual_compact_stock_positive (state : Hq) (N : ℕ) (one : 1 ≤ N) :
    (cutBoundaryStock N (E state) : ℝ → ℂ) =ᵐ[volume.restrict (Ioc q 4)]
      fun x => -(x : ℂ)⁻¹ * ∫ u : ℝ in Ioc 0 q, state u := by
  rw [actual_compact_cut_stock]
  let normalization : BurnolL2 := ∫ a : ℝ in Ioc 0 (N : ℝ), ContinuousChannels.channel 1 a (E state)
  filter_upwards [ae_restrict_of_ae (Lp.coeFn_neg (sourceAnnulusCut normalization)),
    ae_restrict_of_ae (sourceAnnulusCut_coeFn normalization),
    ae_restrict_of_ae (compact_normalization_raw state N), ae_restrict_mem measurableSet_Ioc]
    with x negative cut raw inside
  have positive : 0 < x := (by norm_num : (0 : ℝ) < q).trans inside.1
  have band : q < |x| ∧ |x| ≤ 4 := by simpa only [mem_Ioc, abs_of_pos positive] using inside
  change (-sourceAnnulusCut normalization : BurnolL2) x = _
  rw [negative, Pi.neg_apply, cut, if_pos band, raw,
    compact_normalization_positive state N one x inside.1]
  ring

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
