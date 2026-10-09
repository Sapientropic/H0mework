import H0mework.Versions.V2.Arithmetic.RieszForcing.ForcingCutoffPairing

/-! The original endpoint distribution has zero mass and a retained nonzero quadratic read. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszSource.Kernel

open Complex Filter MeasureTheory Set
open scoped Topology
open Translator.ForcingMeanZero Translator.ForcingCutoff

noncomputable section
attribute [local instance 1100] NormedSpace.complexToReal

local notation "q" => (1 / 4 : ℝ)

/-- The same original plateau test weighted by the physical position squared. -/
def quadraticTest : SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ) ^ 2) oneTest

private theorem quadraticTest_eq {x : ℝ} (inside : x ∈ Icc (-q) q) :
    quadraticTest x = (x : ℂ) ^ 2 := by
  have growth : (fun x : ℝ => (x : ℂ) ^ 2).HasTemperateGrowth := by fun_prop
  unfold quadraticTest
  rw [SchwartzMap.smulLeftCLM_apply growth]
  change (x : ℂ) ^ 2 * oneTest x = _
  rw [oneTest_eq inside, mul_one]

theorem edge_mass_zero : GapEuler.edge q oneTest = 0 := by
  have integralRead : (∫ x : ℝ in Ioc (-q) q, oneTest x) = (1 / 2 : ℂ) := by
    calc
      _ = ∫ _x : ℝ in Ioc (-q) q, (1 : ℂ) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with x inside
        exact oneTest_eq (Ioc_subset_Icc_self inside)
      _ = _ := by
        rw [← intervalIntegral.integral_of_le (by norm_num : -q ≤ q)]
        norm_num [intervalIntegral.integral_const]
  rw [edge_pairing, oneTest_eq (by norm_num), oneTest_eq (by norm_num), integralRead]
  norm_num

private theorem quadratic_integral :
    (∫ x : ℝ in Ioc (-q) q, (x : ℂ) ^ 2) = (1 / 96 : ℂ) := by
  have derivative (x : ℝ) :
      HasDerivAt (fun y : ℝ => (y : ℂ) ^ 3 / 3) ((x : ℂ) ^ 2) x := by
    have generated := ((Complex.ofRealCLM.hasDerivAt (x := x)).pow 3).div_const (3 : ℂ)
    convert! generated using 1
    norm_num
  have continuous : Continuous (fun x : ℝ => (x : ℂ) ^ 2) := by fun_prop
  have generated := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x (_inside : x ∈ uIcc (-q) q) => derivative x)
    (continuous.intervalIntegrable (-q) q)
  rw [intervalIntegral.integral_of_le (by norm_num : -q ≤ q)] at generated
  exact generated.trans (by norm_num)

theorem edge_quadratic_read : GapEuler.edge q quadraticTest = (1 / 48 : ℂ) := by
  have integralRead : (∫ x : ℝ in Ioc (-q) q, quadraticTest x) = (1 / 96 : ℂ) := by
    calc
      _ = ∫ x : ℝ in Ioc (-q) q, (x : ℂ) ^ 2 := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with x inside
        exact quadraticTest_eq (Ioc_subset_Icc_self inside)
      _ = _ := quadratic_integral
  rw [edge_pairing, quadraticTest_eq (by norm_num), quadraticTest_eq (by norm_num), integralRead]
  norm_num

theorem edge_nonzero : GapEuler.edge q ≠ 0 := by
  intro zero
  have actual := edge_quadratic_read
  rw [zero] at actual
  norm_num at actual

end
end OriginalRieszSource.Kernel
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
