import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent

open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKCoefficientBFiniteAction OriginalKSourceResolventReconstruction
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source
open scoped SchwartzMap

open private read eulerRead from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.DualEuler
open private reverse_resolvent from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.UnitResolvent
open private seed_continuous seed_endpoint_ne_zero seed_memLp from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar

local notation "q" => (1/4 : ℝ)
local notation "collar" => Ioo (q/2) q
local notation "D" => DualSource.source
local notation "R" => fun c : BurnolCompletedMellinCoordinate =>
  burnolDirectRightResolventCLM (OriginalPrimitiveRankBalance.conjugateCoordinate c)

private def seedPrice (c : BurnolCompletedMellinCoordinate) (test : SchwartzMap ℝ ℂ) : ℂ :=
  ∫ x : ℝ, test x * seedRaw c.value x

private theorem supported_test_exists (c : BurnolCompletedMellinCoordinate) :
    ∃ test : SchwartzMap ℝ ℂ, tsupport (test : ℝ → ℂ) ⊆ collar ∧ seedPrice c test ≠ 0 := by
  by_contra absent
  have integrable : IntegrableOn (seedRaw c.value) (Ioc (q/2) q) :=
    (seed_memLp c).integrable (by norm_num)
  have gone := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (integrable.mono_set Ioo_subset_Ioc_self).locallyIntegrableOn
    (fun test smooth compact supported => by
      let testℂ : ℝ → ℂ := Complex.ofRealCLM ∘ test
      have compactℂ : HasCompactSupport testℂ := compact.comp_left rfl
      let ψ : SchwartzMap ℝ ℂ := compactℂ.toSchwartzMap (Complex.ofRealCLM.contDiff.comp smooth)
      have supportℂ : tsupport (ψ : ℝ → ℂ) ⊆ collar :=
        (tsupport_comp_subset (show Complex.ofRealCLM 0 = 0 from rfl) test).trans supported
      have zero : seedPrice c ψ = 0 := by
        by_contra live
        exact absent ⟨ψ, supportℂ, live⟩
      change (∫ x : ℝ, (test x : ℂ) * seedRaw c.value x) = 0 at zero
      simpa only [Complex.real_smul] using zero)
  have restricted := (ae_restrict_iff' (μ := volume) measurableSet_Ioo).mpr gone
  rw [Measure.restrict_congr_set Ioo_ae_eq_Icc] at restricted
  have point := Measure.eqOn_Icc_of_ae_eq volume (by norm_num : q/2 ≠ q) restricted
    (seed_continuous c) continuousOn_const
  exact seed_endpoint_ne_zero c (point ⟨by norm_num, le_rfl⟩)

private def test (c : BurnolCompletedMellinCoordinate) : SchwartzMap ℝ ℂ :=
  (supported_test_exists c).choose

private theorem test_spec (c : BurnolCompletedMellinCoordinate) :
    tsupport (test c : ℝ → ℂ) ⊆ collar ∧ seedPrice c (test c) ≠ 0 :=
  (supported_test_exists c).choose_spec

private theorem difference_read (c : BurnolCompletedMellinCoordinate) (N : ℕ) (covered : 2 ≤ N)
    (ψ : SchwartzMap ℝ ℂ) (supported : tsupport (ψ : ℝ → ℂ) ⊆ collar) :
    read ψ (difference c N) = -(coefficientStep c N) * seedPrice c ψ := by
  change (difference c N : TemperedDistribution ℝ ℂ) ψ = _
  rw [Lp.toTemperedDistribution_apply, seedPrice, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [(ae_restrict_iff' measurableSet_Ioc).mp (actual_difference_raw c N covered)]
    with x source
  by_cases inside : x ∈ Ioc (q/2) q
  · rw [smul_eq_mul, source inside]
    ring
  · have ψZero : ψ x = 0 := image_eq_zero_of_notMem_tsupport
      (fun mem => inside (Ioo_subset_Ioc_self (supported mem)))
    rw [ψZero, zero_smul, zero_mul, mul_zero]

private def eulerTest (c : BurnolCompletedMellinCoordinate) (ψ : SchwartzMap ℝ ℂ) :
    BurnolL2 →L[ℂ] ℂ :=
  eulerRead ψ + sourceRate c • read ψ

/-- The original Euler action is tested on the entire resolvent output. -/
theorem actual_tested_action (c : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (ψ : SchwartzMap ℝ ℂ) :
    eulerTest c ψ (R c value) = -(2 : ℂ) * read ψ value := by
  have actual := congrArg (fun T : TemperedDistribution ℝ ℂ => T ψ) (sourceResolvent_euler c value)
  simp only [add_apply, smul_apply, smul_eq_mul] at actual
  change eulerRead ψ (R c value) + sourceRate c * read ψ (R c value) =
    -(2 : ℂ) * read ψ value at actual
  simpa only [eulerTest, add_apply, smul_apply, smul_eq_mul] using actual

/-- A continuous read on the original resolvent output recovers the actual collar coefficient. -/
def recover (c : BurnolCompletedMellinCoordinate) : BurnolL2 →L[ℂ] ℂ :=
  (-(2 * seedPrice c (test c))⁻¹) • eulerTest c (test c)

theorem actual_recovered (c : BurnolCompletedMellinCoordinate) (N : ℕ) (covered : 2 ≤ N) :
    recover c (R c (difference c N)) = -coefficientStep c N := by
  rw [recover, smul_apply, smul_eq_mul, actual_tested_action,
    difference_read c N covered _ (test_spec c).1]
  have live : (2 * seedPrice c (test c)) ≠ 0 :=
    mul_ne_zero (by norm_num) (test_spec c).2
  calc
    _ = ((2 * seedPrice c (test c))⁻¹ * (2 * seedPrice c (test c))) *
      (-coefficientStep c N) := by ring
    _ = -coefficientStep c N := by rw [inv_mul_cancel₀ live, one_mul]

theorem actual_resolvent_difference (c : BurnolCompletedMellinCoordinate) (N : ℕ) :
    R c (difference c N) = D (N+1) (R c (input c)) - D N (R c (input c)) +
      coefficientStep c N • R c (elementarySource c) := by
  unfold difference compensated coefficientStep
  simp only [map_sub, map_add, map_smul]
  change sourceResolvent c (D (N+1) (input c)) + _ -
    (sourceResolvent c (D N (input c)) + _) =
      D (N+1) (sourceResolvent c (input c)) - D N (sourceResolvent c (input c)) + _
  rw [reverse_resolvent, reverse_resolvent]
  module

/-- The coefficient read from the acted residual writes the full next original count after the same R action. -/
theorem actual_resolvent_writeback (c : BurnolCompletedMellinCoordinate) (N : ℕ) (covered : 2 ≤ N) :
    D (N+1) (R c (input c)) = D N (R c (input c)) + R c (difference c N) +
      recover c (R c (difference c N)) • R c (elementarySource c) := by
  rw [actual_recovered c N covered, actual_resolvent_difference]
  module

theorem actual_resolvent_ne_zero (c : BurnolCompletedMellinCoordinate) (N : ℕ) (covered : 2 ≤ N) :
    R c (difference c N) ≠ 0 := by
  intro gone
  have actual := actual_recovered c N covered
  rw [gone, map_zero] at actual
  exact (actual_coefficient_step_ne_zero c N (by omega)) (neg_eq_zero.mp actual.symm)

end OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
