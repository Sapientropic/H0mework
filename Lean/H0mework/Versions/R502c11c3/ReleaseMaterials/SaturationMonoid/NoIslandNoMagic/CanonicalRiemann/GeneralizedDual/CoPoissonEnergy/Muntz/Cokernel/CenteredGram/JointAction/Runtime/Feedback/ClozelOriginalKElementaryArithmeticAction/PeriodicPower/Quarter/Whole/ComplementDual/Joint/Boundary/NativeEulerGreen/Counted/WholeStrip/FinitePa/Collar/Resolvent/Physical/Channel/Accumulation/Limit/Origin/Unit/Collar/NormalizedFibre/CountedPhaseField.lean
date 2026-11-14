import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.CountedPhaseInput

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent

open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeSmooth
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source
open scoped Topology

open private phase_rescale phase_source_even from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.CountedPhaseInput
open private counted_actual_origin_trace from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.CountedStrongOriginTrace
open private phase_scaled_error_zero phase_ne from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.PhysicalJetRate
open private moment from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel

local notation "L¹" => Lp ℂ 1 (volume : Measure ℝ)
local notation "q" => (1/4 : ℝ)
local notation "r₀" => (q/2)
local notation "s₀" => fun c => star (BurnolCompletedMellinCoordinate.value c)
local notation "phase" => fun c (n : Nat) => ((n+2 : Nat) : ℂ)^(-s₀ c)
local notation "clock" => fun n : Nat => Real.log ((n+2 : Nat) : ℝ)
local notation "A" => fun c (n : Nat) => Prod.fst (clockCoefficients c (actualClockPair c n))
local notation "B" => fun c (n : Nat) => Prod.snd (clockCoefficients c (actualClockPair c n))
local notation "bφ" => fun c n => (phase c n)⁻¹*B c n
local notation "m" => fun c => moment c
  (burnolQuarterZeroExtension (burnolMeanZeroTruncatedFourier (nativeSmooth c) : BurnolQuarterIntervalL2))
local notation "Γ" => fun c => 2*(∫ t : ℝ in r₀..q, (t : ℂ)^(s₀ c-1)*seedRaw (BurnolCompletedMellinCoordinate.value c) t)
local notation "R" => fun c => burnolDirectRightResolventCLM (OriginalPrimitiveRankBalance.conjugateCoordinate c)
local notation "H" => countedHomogeneousSplit
local notation "K" => burnolCompletedMellinRieszVector

private theorem phase_trace_literal (c : BurnolCompletedMellinCoordinate) (n : Nat) :
    originalCentreTrace c (countedPhaseSource c n) = (phase c n)⁻¹*A c n - bφ c n*Γ c := by
  have live : (clock n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (Real.log_pos (by exact_mod_cast (by omega : 1 < n+2))).ne'
  rw [phase_rescale, map_smul, counted_actual_origin_trace]
  change (clock n : ℂ)*((((clock n : ℂ)*phase c n)⁻¹)*A c n-
    ((((clock n : ℂ)*phase c n)⁻¹)*B c n)*Γ c) = _
  rw [mul_inv_rev]
  field_simp [live, phase_ne c (n+1)]

private theorem actual_phase_outer_constant (c : BurnolCompletedMellinCoordinate) :
    Tendsto (fun n : Nat => 2*((phase c n)⁻¹*A c n)+(clock n : ℂ)) atTop (𝓝 (m c)) := by
  let error := fun n : Nat => A c n-(1/2 : ℂ)*(m c-(clock n : ℂ))*phase c n
  let bound := ‖m c‖*cutoffJetBudget c 0+cutoffJetBudget c 1
  have rate (n : Nat) : ‖error n‖ ≤ bound*((n+2 : Nat) : ℝ)^(-(s₀ c).re-3/4) :=
    actual_clock_outer_price_error c n
  have small := ((phase_scaled_error_zero c error bound rate).const_mul (2 : ℂ)).add_const (m c)
  simp only [mul_zero, zero_add] at small
  apply small.congr'
  filter_upwards with n
  change 2*((A c n-(1/2 : ℂ)*(m c-(clock n : ℂ))*phase c n)/phase c n)+m c = _
  have live : phase c n ≠ 0 := phase_ne c (n+1)
  field_simp [live]
  ring

theorem actual_counted_phase_trace_constant (c : BurnolCompletedMellinCoordinate) :
    Tendsto (fun n : Nat => 2*originalCentreTrace c (countedPhaseSource c n)+(clock n : ℂ))
      atTop (𝓝 (m c+Γ c)) := by
  have bLimit : Tendsto (bφ c) atTop (𝓝 (-(1/2 : ℂ))) := actual_phase_count_limit c
  have shift := (bLimit.mul_const (Γ c)).const_mul (2 : ℂ)
  have limit := (actual_phase_outer_constant c).sub shift
  have coefficient : (m c)-2*((-(1/2 : ℂ))*Γ c) = m c+Γ c := by ring
  rw [coefficient] at limit
  apply limit.congr'
  filter_upwards with n
  rw [phase_trace_literal]
  ring

private theorem origin_action_add_trace (c : BurnolCompletedMellinCoordinate) (z : L¹ × BurnolL2) (a : ℂ) :
    originAwareMixedAction c (z,0) = originAwareMixedAction c (z,a)+(2*a) • H c := by
  change (outgoingCentre c z.1, R c z.2)-((2 : ℂ)*0) • H c =
    (outgoingCentre c z.1, R c z.2)-(2*a) • H c+(2*a) • H c
  rw [mul_zero, zero_smul, sub_zero, sub_add_cancel]

/-- The actual weighted trace has been consumed, leaving the regular output
at the original phase and the same full mixed source. -/
def countedPhaseRegularField (c : BurnolCompletedMellinCoordinate) (n : Nat) : L¹ × BurnolL2 :=
  originAwareMixedAction c (splitAtPhysicalCutoff r₀ (countedPhaseSource c n), 0)

theorem counted_phase_regular_split (c : BurnolCompletedMellinCoordinate) (n : Nat) :
    countedPhaseRegularField c n = splitAtPhysicalCutoff r₀ (R c (countedPhaseSource c n))+
      (2*originalCentreTrace c (countedPhaseSource c n)) • H c := by
  unfold countedPhaseRegularField
  rw [origin_action_add_trace c _ (originalCentreTrace c (countedPhaseSource c n)),
    actual_origin_aware_mixed_action c (countedPhaseSource c n) (phase_source_even c n)]

theorem actual_counted_phase_regular_limit (c : BurnolCompletedMellinCoordinate) :
    Tendsto (countedPhaseRegularField c) atTop
      (𝓝 ((-(1/2 : ℂ)) • originAwareMixedAction c (countedSeedSplit c,0))) := by
  have source := (actual_counted_phase_source_limit c).prodMk_nhds (tendsto_const_nhds (x := (0 : ℂ)))
  have result := ((originAwareMixedAction c).continuous.tendsto _).comp source
  have target : ((-(1/2 : ℂ)) • countedSeedSplit c,(0 : ℂ)) =
      (-(1/2 : ℂ)) • (countedSeedSplit c,(0 : ℂ)) := by
    apply Prod.ext
    · rfl
    · exact (smul_zero (-(1/2 : ℂ))).symm
  rw [target, map_smul] at result
  exact result

/-- The next mixed field after the original leading logarithm is removed. -/
def countedPhaseSubleadingLimit (c : BurnolCompletedMellinCoordinate) : L¹ × BurnolL2 :=
  (-(1/2 : ℂ)) • originAwareMixedAction c (countedSeedSplit c,0)-(m c+Γ c) • H c

/-- Subtract the fixed leading log times the same original homogeneous field.
The next entire mixed field uses both original coefficients. -/
theorem actual_counted_phase_subleading_field (c : BurnolCompletedMellinCoordinate) :
    Tendsto (fun n : Nat => splitAtPhysicalCutoff r₀ (R c (countedPhaseSource c n))-(clock n : ℂ) • H c) atTop
      (𝓝 (countedPhaseSubleadingLimit c)) := by
  have result := (actual_counted_phase_regular_limit c).sub ((actual_counted_phase_trace_constant c).smul_const (H c))
  apply result.congr'
  filter_upwards with n
  rw [counted_phase_regular_split, add_smul]
  abel

theorem actual_phase_regular_physical_projection (c : BurnolCompletedMellinCoordinate) (n : Nat) :
    physicalProjectionFromCentre (countedPhaseRegularField c n) = -(2*(bφ c n*Γ c)) • K c := by
  rw [counted_phase_regular_split, map_add, map_smul, actual_homogeneous_physical_projection,
    original_physical_projection_from_split r₀ (by norm_num), phase_trace_literal]
  unfold countedPhaseSource
  simp only [map_smul, actual_clock_physical, smul_smul]
  module


/-- The subleading field is generated by the original Euler action of the
actual phase source. Its physical observation is the original Riesz vector
with the original finite-part coefficient. -/
theorem actual_counted_phase_subleading_observations (c : BurnolCompletedMellinCoordinate) :
    eulerOfPhysicalSplit c (countedPhaseSubleadingLimit c) = distributionOfSplit (countedSeedSplit c) ∧
    physicalProjectionFromCentre (countedPhaseSubleadingLimit c) = -(m c) • K c := by
  let field := fun n : Nat => splitAtPhysicalCutoff r₀ (R c (countedPhaseSource c n))-(clock n : ℂ) • H c
  have tends : Tendsto field atTop (𝓝 (countedPhaseSubleadingLimit c)) := actual_counted_phase_subleading_field c
  constructor
  · have Hlaw : eulerOfPhysicalSplit c (H c) = 0 := counted_homogeneous_euler c
    have generated (n : Nat) : eulerOfPhysicalSplit c (field n) =
        -(2 : ℂ) • distributionOfSplit (splitAtPhysicalCutoff r₀ (countedPhaseSource c n)) := by
      dsimp only [field]
      have erase : (clock n : ℂ) • (0 : TemperedDistribution ℝ ℂ) = 0 := by
        ext test
        simp [smul_apply]
      rw [map_sub, map_smul, Hlaw, erase, sub_zero, distributionOfSplit_from_cutoff]
      exact actual_split_R_equation c (countedPhaseSource c n)
    have left := ((eulerOfPhysicalSplit c).continuous.tendsto (countedPhaseSubleadingLimit c)).comp tends
    have right := (((distributionOfSplit.continuous.tendsto ((-(1/2 : ℂ)) • countedSeedSplit c)).comp
      (actual_counted_phase_source_limit c)).const_smul (-(2 : ℂ)))
    rw [map_smul, smul_smul, show (-(2 : ℂ))*(-(1/2 : ℂ)) = 1 by norm_num, one_smul] at right
    exact tendsto_nhds_unique left (right.congr' (Eventually.of_forall fun n => (generated n).symm))
  · have left := (physicalProjectionFromCentre.continuous.tendsto (countedPhaseSubleadingLimit c)).comp tends
    have right := (actual_phase_outer_constant c).neg.smul_const (K c)
    apply tendsto_nhds_unique left
    apply right.congr'
    filter_upwards with n
    change -(2*((phase c n)⁻¹*A c n)+(clock n : ℂ)) • K c = physicalProjectionFromCentre (field n)
    dsimp only [field]
    rw [map_sub, map_smul, actual_homogeneous_physical_projection,
      original_physical_projection_from_split r₀ (by norm_num)]
    unfold countedPhaseSource
    simp only [map_smul, actual_clock_physical, smul_smul]
    module

end OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
