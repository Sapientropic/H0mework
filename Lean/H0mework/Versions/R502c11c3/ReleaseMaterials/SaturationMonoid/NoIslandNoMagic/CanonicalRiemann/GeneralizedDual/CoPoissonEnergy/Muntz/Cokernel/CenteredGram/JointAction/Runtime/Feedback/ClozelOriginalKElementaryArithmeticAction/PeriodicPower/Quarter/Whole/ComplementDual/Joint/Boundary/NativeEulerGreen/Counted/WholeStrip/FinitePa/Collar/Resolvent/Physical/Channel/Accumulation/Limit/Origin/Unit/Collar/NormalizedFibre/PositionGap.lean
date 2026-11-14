import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.HomogeneousFibre
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKForcingGapAction.Source

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent

open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalRieszSource OriginalPaPhysicalGreen
open OriginalKSourceResolventReconstruction
open scoped ENNReal

open private cutoff_split_read from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.HomogeneousFibre

local notation "L¹" => Lp ℂ 1 (volume : Measure ℝ)
local notation "S'" => TemperedDistribution ℝ ℂ
local notation "q" => (1/4 : ℝ)
local notation "r₀" => (q/2)
local notation "box" => symmetricInterval r₀
local notation "unit" => FiniteMobiusResolventFlux.box r₀
local notation "unit₁" => Prod.fst (splitAtPhysicalCutoff r₀ unit)
local notation "R" => burnolDirectRightResolventCLM

/-- The actual mass of the half-gap centre, expressed as a constant density. -/
def positionGapCentreDensity : L¹ →L[ℂ] ℂ := (4 : ℂ) • L1.integralCLM' ℂ

/-- The same exterior and the original compact unit recover a flat mixed centre in L². -/
def recoverPositionGapSplit : (L¹ × BurnolL2) →L[ℂ] BurnolL2 :=
  (positionGapCentreDensity.comp (ContinuousLinearMap.fst ℂ L¹ BurnolL2)).smulRight unit +
    ContinuousLinearMap.snd ℂ L¹ BurnolL2

private theorem centre_unit_read :
    ((unit₁ : L¹) : ℝ → ℂ) =ᵐ[volume] Set.indicator box (fun _ => (1 : ℂ)) := by
  filter_upwards [cutoff_split_read r₀ unit, FiniteMobiusResolventFlux.box_read r₀] with x split original
  rw [split.1]
  by_cases inside : x ∈ box
  · rw [indicator_of_mem inside, original, indicator_of_mem inside]
  · rw [indicator_of_notMem inside, indicator_of_notMem inside]

private theorem density_unit : positionGapCentreDensity unit₁ = 1 := by
  change (4 : ℂ) * L1.integralCLM' ℂ unit₁ = _
  rw [← L1.integral_eq' ℂ, L1.integral_eq_integral, integral_congr_ae centre_unit_read,
    integral_indicator (measurableSet_symmetricInterval r₀), integral_const, measureReal_def, Measure.restrict_apply_univ]
  norm_num [symmetricInterval, Real.volume_Icc]

private theorem actual_gap_cutoff (value : BurnolL2) (a : ℂ)
    (constant : burnolQuarterRestriction value = a • intervalConstant q) :
    originalPhysicalCutoff r₀ value = a • unit := by
  have localRead : (value : ℝ → ℂ) =ᵐ[volume.restrict (symmetricInterval q)] fun _ => a := by
    filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) value,
      intervalConstant_coeFn q, Lp.coeFn_smul a (intervalConstant q)] with x read one scalar
    change burnolQuarterRestriction value x = value x at read
    rw [constant, scalar, Pi.smul_apply, smul_eq_mul, one, mul_one] at read
    exact read.symm
  have full := (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp localRead
  apply Lp.ext
  filter_upwards [full, originalPhysicalCutoff_coeFn r₀ value,
    FiniteMobiusResolventFlux.box_read r₀, Lp.coeFn_smul a unit] with x atx cut one scalar
  rw [cut, scalar, Pi.smul_apply, smul_eq_mul, one]
  by_cases inside : x ∈ box
  · rw [indicator_of_mem inside, indicator_of_mem inside, mul_one]
    exact atx (abs_le.mp ((abs_le.mpr inside).trans (by norm_num)))
  · rw [indicator_of_notMem inside, indicator_of_notMem inside, mul_zero]

private theorem actual_gap_centre (value : BurnolL2) (a : ℂ)
    (constant : burnolQuarterRestriction value = a • intervalConstant q) :
    (splitAtPhysicalCutoff r₀ value).1 = a • unit₁ := by
  have cut := actual_gap_cutoff value a constant
  apply Lp.ext
  filter_upwards [(originalPhysicalCutoff_integrable r₀ value).coeFn_toL1, centre_unit_read,
    Lp.coeFn_smul a unit, Lp.coeFn_smul a unit₁, FiniteMobiusResolventFlux.box_read r₀]
    with x inside unitRead scalar centreScalar unitRaw
  change (splitAtPhysicalCutoff r₀ value).1 x = originalPhysicalCutoff r₀ value x at inside
  rw [inside, cut, scalar, centreScalar, Pi.smul_apply, Pi.smul_apply, unitRead, unitRaw]

private theorem density_actual (value : BurnolL2) (a : ℂ)
    (constant : burnolQuarterRestriction value = a • intervalConstant q) :
    positionGapCentreDensity (splitAtPhysicalCutoff r₀ value).1 = a := by
  rw [actual_gap_centre value a constant, map_smul, density_unit, smul_eq_mul, mul_one]

theorem recover_actual_position_gap_split (value : BurnolL2)
    (gap : value ∈ locallyConstantFace q) :
    recoverPositionGapSplit (splitAtPhysicalCutoff r₀ value) = value := by
  obtain ⟨a, constant⟩ := mem_locallyConstantFace_iff_exists.mp gap
  have source : burnolQuarterRestriction value = a • intervalConstant q := constant.symm
  change positionGapCentreDensity (splitAtPhysicalCutoff r₀ value).1 • unit+
    (value-originalPhysicalCutoff r₀ value) = value
  rw [density_actual value a source, actual_gap_cutoff value a source]
  abel

private theorem recover_flat_split_roundtrip (z : L¹ × BurnolL2)
    (exterior : ∀ᵐ x : ℝ ∂volume, x ∈ box → z.2 x = 0)
    (flat : ∃ a : ℂ, z.1 = a • unit₁) :
    splitAtPhysicalCutoff r₀ (recoverPositionGapSplit z) = z := by
  obtain ⟨a, flat⟩ := flat
  have density : positionGapCentreDensity z.1 = a := by
    rw [flat, map_smul, density_unit, smul_eq_mul, mul_one]
  have recovered : recoverPositionGapSplit z = a • unit+z.2 := by
    change positionGapCentreDensity z.1 • unit+z.2 = _
    rw [density]
  rw [recovered]
  let value := a • unit+z.2
  have actual : ∀ᵐ x : ℝ ∂volume, value x = a*(Set.indicator box (fun _ => (1 : ℂ)) x)+z.2 x := by
    filter_upwards [Lp.coeFn_add (a • unit) z.2, Lp.coeFn_smul a unit,
      FiniteMobiusResolventFlux.box_read r₀] with x add scalar read
    change value x = _ at add
    rw [add, Pi.add_apply, scalar, Pi.smul_apply, smul_eq_mul, read]
  apply Prod.ext <;> apply Lp.ext
  · filter_upwards [cutoff_split_read r₀ value, actual, exterior, centre_unit_read,
      Lp.coeFn_smul a unit₁] with x split read zero one scalar
    change (splitAtPhysicalCutoff r₀ value).1 x = z.1 x
    rw [split.1, flat, scalar, Pi.smul_apply, smul_eq_mul, one]
    by_cases inside : x ∈ box
    · rw [indicator_of_mem inside, read, zero inside, add_zero]
    · rw [indicator_of_notMem inside, indicator_of_notMem inside, mul_zero]
  · filter_upwards [cutoff_split_read r₀ value, actual, exterior] with x split read zero
    change (splitAtPhysicalCutoff r₀ value).2 x = z.2 x
    rw [split.2]
    by_cases inside : x ∈ box
    · rw [indicator_of_mem inside, sub_self, zero inside]
    · rw [indicator_of_notMem inside, read, indicator_of_notMem inside, mul_zero, zero_add, sub_zero]

/-- The position gap supplies the compact coordinate, so the weak Euler
observation determines both components without a physical projection input. -/
theorem position_gap_euler_injective (c : BurnolCompletedMellinCoordinate)
    {left right : L¹ × BurnolL2} (leftSplit : IsEvenPhysicalSplit left) (rightSplit : IsEvenPhysicalSplit right)
    (leftFlat : ∃ a : ℂ, left.1 = a • unit₁) (rightFlat : ∃ a : ℂ, right.1 = a • unit₁)
    (same : eulerOfPhysicalSplit c left = eulerOfPhysicalSplit c right) : left = right := by
  let read : BurnolL2 →L[ℂ] S' :=
    (GapEuler.euler + (star c.value-1/2) • ContinuousLinearMap.id ℂ S').comp
      (Lp.toTemperedDistributionCLM ℂ volume 2)
  have leftRound := recover_flat_split_roundtrip left leftSplit.exterior leftFlat
  have rightRound := recover_flat_split_roundtrip right rightSplit.exterior rightFlat
  have literal (z : L¹ × BurnolL2) (round : splitAtPhysicalCutoff r₀ (recoverPositionGapSplit z) = z) :
      eulerOfPhysicalSplit c z = read (recoverPositionGapSplit z) := by
    calc
      _ = eulerOfPhysicalSplit c (splitAtPhysicalCutoff r₀ (recoverPositionGapSplit z)) :=
        congrArg (eulerOfPhysicalSplit c) round.symm
      _ = _ := by
        change GapEuler.euler (distributionOfSplit (splitAtPhysicalCutoff r₀ (recoverPositionGapSplit z))) +
          (star c.value-1/2) • distributionOfSplit (splitAtPhysicalCutoff r₀ (recoverPositionGapSplit z)) = _
        rw [distributionOfSplit_from_cutoff]
        rfl
  have equation := (literal left leftRound).symm.trans (same.trans (literal right rightRound))
  have zero : read (recoverPositionGapSplit left-recoverPositionGapSplit right) = 0 := by
    rw [map_sub, equation, sub_self]
  have positive : 0 < (star c.value-(1/2 : ℂ)).re := by
    simp only [Complex.sub_re, Complex.star_def, Complex.conj_re]
    norm_num
    linarith [c.rightHalf]
  have equal := sub_eq_zero.mp (homogeneous_L2_unique (star c.value-1/2) positive _ zero)
  exact leftRound.symm.trans ((congrArg (splitAtPhysicalCutoff r₀) equal).trans rightRound)

/-- The actual source density pays the compact update. The remainder uses the
same original R action on the whole recovered source and the same unit. -/
def positionGapMixedAction (c : BurnolCompletedMellinCoordinate) : (L¹ × BurnolL2) →L[ℂ] (L¹ × BurnolL2) :=
  let nextDensity := (-(1 : ℂ)/(c.value/2)) •
    (positionGapCentreDensity.comp (ContinuousLinearMap.fst ℂ L¹ BurnolL2))
  (nextDensity.smulRight unit₁).prod ((R c).comp recoverPositionGapSplit - nextDensity.smulRight unit)

theorem actual_position_gap_mixed_action (c : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (gap : value ∈ locallyConstantFace q) :
    positionGapMixedAction c (splitAtPhysicalCutoff r₀ value) = splitAtPhysicalCutoff r₀ (R c value) := by
  obtain ⟨a, constant⟩ := mem_locallyConstantFace_iff_exists.mp gap
  have source : burnolQuarterRestriction value = a • intervalConstant q := constant.symm
  have right : 1/4 < (c.value/2).re := by
    rw [Complex.div_re]
    norm_num
    linarith [c.rightHalf]
  have target : burnolQuarterRestriction (R c value) = (-a/(c.value/2)) • intervalConstant q :=
    OriginalKForcingGapAction.right_resolvent_quarter_constant _ right value a source
  have scalar : (-(1 : ℂ)/(c.value/2))*a = -a/(c.value/2) := by ring
  apply Prod.ext
  · change ((-(1 : ℂ)/(c.value/2))*positionGapCentreDensity (splitAtPhysicalCutoff r₀ value).1) • unit₁ = _
    rw [density_actual value a source, scalar, actual_gap_centre _ _ target]
  · change R c (recoverPositionGapSplit (splitAtPhysicalCutoff r₀ value)) -
      ((-(1 : ℂ)/(c.value/2))*positionGapCentreDensity (splitAtPhysicalCutoff r₀ value).1) • unit =
        R c value-originalPhysicalCutoff r₀ (R c value)
    rw [recover_actual_position_gap_split value gap, density_actual value a source,
      scalar, actual_gap_cutoff _ _ target]

theorem actual_position_gap_mixed_centre (value : BurnolL2) (gap : value ∈ locallyConstantFace q) :
    ∃ a : ℂ, (splitAtPhysicalCutoff r₀ value).1 = a • unit₁ := by
  obtain ⟨a, constant⟩ := mem_locallyConstantFace_iff_exists.mp gap
  exact ⟨a, actual_gap_centre value a constant.symm⟩

end OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
