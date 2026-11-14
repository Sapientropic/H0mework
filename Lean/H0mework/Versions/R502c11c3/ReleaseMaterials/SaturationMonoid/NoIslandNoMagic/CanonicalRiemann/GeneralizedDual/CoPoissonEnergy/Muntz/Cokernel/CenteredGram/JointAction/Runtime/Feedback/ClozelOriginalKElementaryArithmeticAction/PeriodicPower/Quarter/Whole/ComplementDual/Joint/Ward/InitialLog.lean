import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.ActedSchur
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CenteredCountingDualSupport

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2800000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Prices
open scoped Topology InnerProductSpace
open private forward_reflect from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountingJointEnergy
local notation "q" => (1 / 4 : ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "E" => burnolQuarterZeroExtension
local notation "Rq" => burnolQuarterRestriction
local notation "P0" => Constructor.zeroMean
local notation "AN" => FiniteForcing.source
local notation "DN" => DualSource.source
local notation "Cq" => intervalConstant q

def nativeCotestGap (c : BurnolCompletedMellinCoordinate) : ℂ :=
  burnolConstantGapCoefficient burnolUnscaledCommonGapRadius (physicalCotest c)

private theorem physical_quarter (c : BurnolCompletedMellinCoordinate) :
    Rq (physicalCotest c : BurnolL2) = nativeCotestGap c • Cq := by
  apply Lp.ext
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) (physicalCotest c : BurnolL2),
    burnolAmbientGap_ae (physicalCotest c), Lp.coeFn_smul (nativeCotestGap c) Cq,
    intervalConstant_coeFn q] with x restricted gap scaled constant
  change Rq (physicalCotest c : BurnolL2) x = (physicalCotest c : BurnolL2) x at restricted
  rw [restricted, gap, scaled, Pi.smul_apply, smul_eq_mul, constant, mul_one]
  rfl

private theorem seed_even : reflectL2 ConstantDual.seed = ConstantDual.seed := by
  change reflectL2 (burnolRadiusZeroExtension q Cq) = _
  rw [burnolRadiusZeroExtension_reflect, reflectRestricted_intervalConstant]
  rfl

private theorem centered_outside_zero (value : BurnolL2) (even : reflectL2 value = value)
    (outside : Rq value = 0) (N : ℕ) (positive : 0 < N) :
    P0 (Rq (AN N value)) = 0 := by
  let z : M := P0 (Rq (AN N value))
  have zEven : reflectRestricted q (z : Hq) = (z : Hq) := by
    change reflectRestricted q (burnolQuarterMeanZeroProjection (restrictToInterval q (AN N value))) = _
    rw [← burnolQuarterMeanZeroProjection_reflect, ← restrictToInterval_reflectL2, forward_reflect, even]
    rfl
  have supported := CenteredCountingDualSupport.source_support z zEven N positive
  have dualZero : inner ℂ (DN N (E (z : Hq))) value = 0 := by
    rw [supported]
    change inner ℂ (burnolQuarterRestriction.adjoint (Rq (DN N (E (z : Hq))))) value = 0
    rw [ContinuousLinearMap.adjoint_inner_left, outside, inner_zero_right]
  have adjointPair : inner ℂ (DN N (E (z : Hq))) value = inner ℂ (E (z : Hq)) (AN N value) := by
    rw [CountingDual.dual_eq_adjoint]
    exact ContinuousLinearMap.adjoint_inner_left (CountingDual.sourceCLM N) value (E (z : Hq))
  have zeroPair : inner ℂ (z : Hq) (Rq (AN N value)) = 0 := by
    rw [adjointPair] at dualZero
    exact (ContinuousLinearMap.adjoint_inner_left Rq (AN N value) (z : Hq)).symm.trans dualZero
  have projected : inner ℂ (z : Hq) (z : Hq) = inner ℂ (z : Hq) (Rq (AN N value)) :=
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left z (Rq (AN N value))
  have zero : (z : Hq) = 0 := inner_self_eq_zero.mp (projected.trans zeroPair)
  exact Subtype.ext zero

/-- The fixed physical cotest generates its plain-log centered quarter at the same finite N. -/
theorem actual_native_initial_log_finite (c : BurnolCompletedMellinCoordinate) (N : ℕ) (positive : 0 < N) :
    P0 (Rq (AN N (physicalCotest c : BurnolL2))) =
      nativeCotestGap c • P0 SmallScaleLog.logL2 := by
  let outside : BurnolL2 := (physicalCotest c : BurnolL2) - nativeCotestGap c • ConstantDual.seed
  have restricted : Rq outside = 0 := by
    change Rq ((physicalCotest c : BurnolL2) - nativeCotestGap c • E Cq) = 0
    rw [map_sub, map_smul, burnolQuarterRestriction_zeroExtension, physical_quarter, sub_self]
  have even : reflectL2 outside = outside := by
    change reflectL2 ((physicalCotest c : BurnolL2) - nativeCotestGap c • ConstantDual.seed) = _
    rw [map_sub, map_smul, seed_even,
      mem_evenL2ClosedFace_iff.mp (physicalCotest c).property.2]
  have discarded := centered_outside_zero outside even restricted N positive
  have constant := congrArg P0 (WindowCounting.constant_source N positive)
  rw [map_add, map_smul, Constructor.zeroMean_constant, smul_zero, zero_add] at constant
  change P0 (Rq (AN N ConstantDual.seed)) = P0 SmallScaleLog.logL2 at constant
  have split : (physicalCotest c : BurnolL2) = nativeCotestGap c • ConstantDual.seed + outside := by
    dsimp only [outside]
    module
  change P0 (Rq (CountingDual.sourceCLM N (physicalCotest c : BurnolL2))) = _
  rw [split]
  simp only [map_add, map_smul, CountingDual.sourceCLM_apply]
  rw [discarded, constant, add_zero]

/-- The sharp whole value consumes that finite source identity without dropping its separate complete mean. -/
theorem actual_native_initial_log (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) :
    nativeActedSchur c 0 = nativeCotestGap c • P0 SmallScaleLog.logL2 := by
  have original := actual_paired_cotest_forward c zero
  change Tendsto (fun N : ℕ => AN N (physicalCotest c : BurnolL2)) atTop (𝓝 (pairedCotestForward c)) at original
  have centered := (Constructor.zeroMean.continuous.comp burnolQuarterRestriction.continuous).tendsto _ |>.comp original
  have finite := centered.congr' (show (fun N : ℕ => P0 (Rq (AN N (physicalCotest c : BurnolL2)))) =ᶠ[atTop]
      (fun _ : ℕ => nativeCotestGap c • P0 SmallScaleLog.logL2) from by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N after
    exact actual_native_initial_log_finite c N (by omega))
  have actual := tendsto_nhds_unique finite tendsto_const_nhds
  simpa only [nativeActedSchur, nativeActedQuarter, nativeOutgoingCotest, pow_zero, one_apply_eq_self, Function.comp_apply] using actual

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
