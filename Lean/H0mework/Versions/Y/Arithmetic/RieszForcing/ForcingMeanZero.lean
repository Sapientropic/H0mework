import H0mework.Versions.Y.Arithmetic.RieszForcing.ForcingWhole
import H0mework.Versions.Y.Arithmetic.RieszCanonicalRaw.Forcing

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszSource.Translator.ForcingMeanZero

open Complex Filter MeasureTheory Set
open scoped ENNReal Topology InnerProductSpace ContDiff
noncomputable section

local notation "q" => (1 / 4 : ℝ)
local notation "μq" => (volume.restrict (symmetricInterval q))

def mean (coordinate : BurnolCompletedMellinCoordinate) : ℂ :=
  burnolQuarterMeanCoefficient (burnolQuarterRestriction
    (burnolAmbientEvenPart (fourierL2 (burnolAmbientCompletedMellinKernelFormula coordinate))))

def edgeMean : ℂ :=
  burnolQuarterMeanCoefficient (Constructor.compact (Edge.raw q) (Edge.raw_continuous q))

def eta : BurnolQuarterMeanZeroCarrier :=
  Constructor.endpointColumn q + Constructor.endpointColumn (-q)

theorem forcingRaw_eq (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    burnolRieszFourierForcingRaw coordinate x = ForcingWhole.raw coordinate x - mean coordinate := rfl

theorem mean_integral (coordinate : BurnolCompletedMellinCoordinate) :
    mean coordinate = (2 : ℂ) * ∫ x : ℝ in Ioc (-q) q, ForcingWhole.raw coordinate x := by
  have restriction :
      (burnolQuarterRestriction (ForcingWhole.whole coordinate) : ℝ → ℂ) =ᵐ[μq]
        ForcingWhole.raw coordinate :=
    (LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) (ForcingWhole.whole coordinate)).trans
      (ae_restrict_of_ae (ForcingWhole.whole_read coordinate))
  have sameMean : mean coordinate = burnolQuarterMeanCoefficient
      (burnolQuarterRestriction (ForcingWhole.whole coordinate)) := by
    unfold mean ForcingWhole.whole
    rw [fourierL2_burnolAmbientEvenPart]
  rw [sameMean, Constructor.mean_integral]
  congr 1
  rw [← integral_Icc_eq_integral_Ioc]
  exact integral_congr_ae restriction

theorem edgeMean_integral :
    edgeMean = (2 : ℂ) * ∫ x : ℝ in Ioc (-q) q, Edge.raw q x := by
  rw [edgeMean, Constructor.mean_compact,
    intervalIntegral.integral_of_le (by norm_num : -q ≤ q)]

theorem eta_read : (eta : ℝ → ℂ) =ᵐ[μq] fun x : ℝ => Edge.raw q x - edgeMean := by
  have source := burnolMeanZeroProjection_ae_raw
    (Constructor.compact (Edge.raw q) (Edge.raw_continuous q))
    (Edge.raw q) Edge.quarter_restriction_read
  change ((Constructor.zeroMean (Constructor.compact (Edge.raw q) (Edge.raw_continuous q)) :
    BurnolQuarterIntervalL2) : ℝ → ℂ) =ᵐ[μq] _ at source
  rw [Edge.zeroMean_raw_eq_endpointColumns] at source
  exact source

private def onePulse : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩

def oneTest : SchwartzMap ℝ ℂ :=
  (onePulse.hasCompactSupport.comp_left (g := Complex.ofReal) Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp onePulse.contDiff)

theorem oneTest_compact : HasCompactSupport (oneTest : ℝ → ℂ) :=
  onePulse.hasCompactSupport.comp_left (g := Complex.ofReal) Complex.ofReal_zero

theorem oneTest_eq {x : ℝ} (inside : x ∈ Icc (-q) q) : oneTest x = 1 := by
  change (onePulse x : ℂ) = 1
  rw [onePulse.one_of_mem_closedBall]
  · rfl
  · change dist x 0 ≤ 1
    rw [Real.dist_eq, sub_zero, abs_le]
    constructor <;> linarith [inside.1, inside.2]

theorem oneTest_deriv {x : ℝ} (inside : x ∈ Icc (-q) q) : deriv oneTest x = 0 := by
  have member : x ∈ Metric.ball (0 : ℝ) onePulse.rIn := by
    change dist x 0 < 1
    rw [Real.dist_eq, sub_zero, abs_lt]
    constructor <;> linarith [inside.1, inside.2]
  have equal : (oneTest : ℝ → ℂ) =ᶠ[𝓝 x] fun _ => (1 : ℂ) := by
    filter_upwards [onePulse.eventuallyEq_one_of_mem_ball member] with y read
    change (onePulse y : ℂ) = 1
    rw [read]
    rfl
  exact ((hasDerivAt_const x (1 : ℂ)).congr_of_eventuallyEq equal).deriv

theorem raw_mean_boundary (coordinate : BurnolCompletedMellinCoordinate) :
    ForcingWhole.raw coordinate q = star coordinate.value * mean coordinate +
      ForcingWhole.coefficient coordinate * edgeMean := by
  have source := ForcingWhole.raw_interval_ibp coordinate oneTest
  have read : (∫ x : ℝ in Ioc (-q) q,
      ((x : ℂ) * ForcingWhole.raw coordinate x) * deriv oneTest x +
        (star coordinate.value * ForcingWhole.raw coordinate x +
          ForcingWhole.coefficient coordinate * Edge.raw q x) * oneTest x) =
      star coordinate.value * (∫ x : ℝ in Ioc (-q) q, ForcingWhole.raw coordinate x) +
        ForcingWhole.coefficient coordinate * (∫ x : ℝ in Ioc (-q) q, Edge.raw q x) := by
    have original := ((ForcingWhole.raw_local coordinate).integrableOn_isCompact
      (isCompact_Icc (a := -q) (b := q))).mono_set Ioc_subset_Icc_self
    have edge := ((Edge.raw_continuous q).integrableOn_Icc :
      IntegrableOn (Edge.raw q) (Icc (-q) q)).mono_set Ioc_subset_Icc_self
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (original.const_mul _) (edge.const_mul _)]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [oneTest_eq (Ioc_subset_Icc_self hx), oneTest_deriv (Ioc_subset_Icc_self hx)]
    ring
  rw [read, oneTest_eq (by norm_num), oneTest_eq (by norm_num)] at source
  rw [mean_integral, edgeMean_integral]
  push_cast at source
  linear_combination -2 * source

theorem forcing_mean_boundary (coordinate : BurnolCompletedMellinCoordinate) :
    burnolRieszFourierForcingRaw coordinate q =
      (star coordinate.value - 1) * mean coordinate + ForcingWhole.coefficient coordinate * edgeMean := by
  rw [forcingRaw_eq, raw_mean_boundary]
  ring

end
end OriginalRieszSource.Translator.ForcingMeanZero
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
