import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Top.FiniteMellin
import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.LogMellin
import H0mework.Versions.R7e4da746.Arithmetic.RiemannDivision.AnalyticComplementAmbientMellinEvaluator

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2800000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Top.MellinRead
open Complex Filter MeasureTheory Set
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalRieszSource
open CenteredGram.IntegralGraphJointAction.OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.LogMellin
open scoped Topology InnerProductSpace
open private divisionJet_value_ae_eq_gapCoefficient_on_Ioc from
  H0mework.Versions.R7e4da746.Arithmetic.RiemannDivision.AnalyticComplementAmbientMellinEvaluator
open private mellin_source_ae from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitMellin.ResolventSource
local notation "q" => (1 / 4 : ℝ)
local notation "E" => burnolQuarterZeroExtension
local notation "Rq" => burnolQuarterRestriction
local notation "M" => BurnolQuarterMeanZeroCarrier

/-- The original ambient CLM reads the honest Mellin integral on every actual position-gap field. -/
theorem actual_position_gap_mellin (c : BurnolCompletedMellinCoordinate) (v : BurnolL2)
    (gap : v ∈ locallyConstantFace burnolUnscaledCommonGapRadius) :
    HasMellin (v : ℝ → ℂ) (1 - c.value) (burnolAmbientCompletedMellinEvaluator c v) := by
  obtain ⟨coefficient, quarter⟩ := mem_locallyConstantFace_iff_exists.mp gap
  have exponent : -1 < (-c.value).re := by simp only [neg_re]; linarith [c.belowOne]
  have power : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-c.value)) (Ioc 0 q) :=
    (intervalIntegral.intervalIntegrable_cpow' (a := 0) (b := q) exponent).1
  have near : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-c.value) * v x) (Ioc 0 q) := by
    apply (power.mul_const coefficient).congr
    filter_upwards [divisionJet_value_ae_eq_gapCoefficient_on_Ioc q (by norm_num) v coefficient quarter]
      with x read
    rw [read]
  have tail := burnolRadiusMellinWeight_integrableOn_tail q (by norm_num) c.value c.rightHalf v
  constructor
  · change IntegrableOn (fun x : ℝ => (x : ℂ) ^ ((1 - c.value) - 1) • v x) (Ioi 0)
    rw [show (1 - c.value) - 1 = -c.value by ring]
    change IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-c.value) * v x) (Ioi 0)
    rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ q)]
    exact near.union tail
  · have honest := burnolAmbientCompletedMellinEvaluator_eq_positive_integral_of_positionGap c v gap
    simpa only [mellin, show (1 - c.value) - 1 = -c.value by ring, smul_eq_mul] using honest.symm

private theorem gap_zero (value : M) : burnolAmbientGapCoefficient q (E (value : BurnolQuarterIntervalL2)) = 0 := by
  simp only [burnolAmbientGapCoefficient, smul_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, smul_eq_mul]
  change (‖intervalConstant q‖ ^ 2 : ℂ)⁻¹ * inner ℂ (intervalConstant q) (Rq (E (value : BurnolQuarterIntervalL2))) = 0
  rw [burnolQuarterRestriction_zeroExtension]
  have zero : inner ℂ (intervalConstant q) (value : BurnolQuarterIntervalL2) = 0 :=
    (Submodule.mem_orthogonal _ _).mp value.property _ (Submodule.mem_span_singleton_self _)
  rw [zero, mul_zero]

/-- A genuine centered compact column has zero ambient read; its honest Mellin contribution is retained separately. -/
theorem actual_centered_extension_read (c : BurnolCompletedMellinCoordinate) (value : M) :
    burnolAmbientCompletedMellinEvaluator c (E (value : BurnolQuarterIntervalL2)) = 0 := by
  have tail : burnolRadiusMellinTailEvaluator q (by norm_num) c.value c.rightHalf
      (E (value : BurnolQuarterIntervalL2)) = 0 := by
    rw [burnolRadiusMellinTailEvaluator_eq_integral]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_of_ae (burnolQuarterZeroExtension_coe (value : BurnolQuarterIntervalL2)),
      ae_restrict_mem measurableSet_Ioi] with x read outside
    rw [read]
    have absent : x ∉ symmetricInterval q := by
      intro inside
      exact not_le_of_gt outside inside.2
    rw [indicator_of_notMem absent, mul_zero]
    rfl
  change burnolRadiusMellinGapMoment q c.value *
    burnolAmbientGapCoefficient q (E (value : BurnolQuarterIntervalL2)) +
      burnolRadiusMellinTailEvaluator q (by norm_num) c.value c.rightHalf
        (E (value : BurnolQuarterIntervalL2)) = 0
  rw [gap_zero, tail, mul_zero, zero_add]

/-- Removing the actually generated centered quarter yields one position-gap field with the same full ambient read. -/
theorem actual_centered_quarter_split (v : BurnolL2) :
    v - E (Constructor.zeroMean (Rq v) : BurnolQuarterIntervalL2) ∈
      locallyConstantFace burnolUnscaledCommonGapRadius := by
  apply mem_locallyConstantFace_iff_exists.mpr
  refine ⟨burnolQuarterMeanCoefficient (Rq v), ?_⟩
  change burnolQuarterMeanCoefficient (Rq v) • intervalConstant q =
    Rq (v - E (Constructor.zeroMean (Rq v) : BurnolQuarterIntervalL2))
  rw [map_sub, burnolQuarterRestriction_zeroExtension, Constructor.zeroMean_read]
  module

/-- The actual logarithmic quarter supplies the entire correction to the bounded ambient reader. -/
theorem actual_log_quarter_mellin (c : BurnolCompletedMellinCoordinate) (v : BurnolL2) (coefficient : ℂ)
    (quarter : Constructor.zeroMean (Rq v) = coefficient • CenteredCountingDual.logarithm) :
    HasMellin (v : ℝ → ℂ) (1 - c.value)
      (burnolAmbientCompletedMellinEvaluator c v -
        coefficient * (c.value * (q : ℂ) ^ (1 - c.value) / (1 - c.value)^2)) := by
  let compact : BurnolL2 := E (CenteredCountingDual.logarithm : BurnolQuarterIntervalL2)
  let rest : BurnolL2 := v - coefficient • compact
  have restGap : rest ∈ locallyConstantFace burnolUnscaledCommonGapRadius := by
    have generated := actual_centered_quarter_split v
    rw [quarter] at generated
    simpa only [Submodule.coe_smul, map_smul] using generated
  have restSource := actual_position_gap_mellin c rest restGap
  have logSource := actual_plain_log_reflected_moment c
  have scaled := hasMellin_const_smul logSource.1 coefficient
  rw [logSource.2] at scaled
  have scaledSource : HasMellin (coefficient • compact : BurnolL2) (1 - c.value)
      (coefficient * -(c.value * (q : ℂ) ^ (1 - c.value) / (1 - c.value)^2)) :=
    mellin_source_ae _ _ _ _ (ae_restrict_of_ae (Lp.coeFn_smul coefficient compact)) scaled
  have combined := hasMellin_add restSource.1 scaledSource.1
  rw [restSource.2, scaledSource.2] at combined
  have field : rest + coefficient • compact = v := by dsimp only [rest]; module
  have actual := mellin_source_ae _ _ _ _
    (ae_restrict_of_ae (Lp.coeFn_add rest (coefficient • compact))) combined
  rw [field] at actual
  have restRead : burnolAmbientCompletedMellinEvaluator c rest = burnolAmbientCompletedMellinEvaluator c v := by
    change burnolAmbientCompletedMellinEvaluator c (v - coefficient • compact) = _
    rw [map_sub, map_smul]
    change burnolAmbientCompletedMellinEvaluator c v - coefficient *
      burnolAmbientCompletedMellinEvaluator c (E (CenteredCountingDual.logarithm : BurnolQuarterIntervalL2)) = _
    rw [actual_centered_extension_read, mul_zero, sub_zero]
  rw [restRead] at actual
  convert actual using 1
  ring

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Top.MellinRead
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
