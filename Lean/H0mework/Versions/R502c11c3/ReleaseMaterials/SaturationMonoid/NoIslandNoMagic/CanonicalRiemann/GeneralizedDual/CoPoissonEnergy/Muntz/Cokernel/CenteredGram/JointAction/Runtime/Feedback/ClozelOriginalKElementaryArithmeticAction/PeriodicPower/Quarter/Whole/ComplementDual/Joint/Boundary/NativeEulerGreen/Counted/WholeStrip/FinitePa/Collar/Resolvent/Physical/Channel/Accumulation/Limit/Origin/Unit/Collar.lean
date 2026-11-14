import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit
import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Endpoint

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent

open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen OriginalRieszSource
open OriginalRieszFinitePairing.CoPoisson.Ward OriginalRieszFinitePairing.CoPoisson.Ward.CountedSchur
open OriginalKCoefficientBFiniteAction
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeSmooth
open scoped Topology InnerProductSpace

open private collarPower seed_memLp from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar
open private compensated_even from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical
open private moment from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel
open private quarterExterior quarterTail from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation
open private coefficient_limit whole_limit from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit
open private actual_compact_R_exterior from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin
open private finite_R_exterior from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit
open private mean_power from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.SeedFourier
open private quarter_tail_ne_zero from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.ReverseSourceRTail

local notation "q" => (1/4 : ℝ)
local notation "band" => Ioc (q/2) q
local notation "CollarRead" => LpToLpRestrictCLM ℝ ℂ ℂ volume 2 band
local notation "Hq" => BurnolQuarterIntervalL2
local notation "E" => burnolQuarterZeroExtension
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "R₀" => fun c => burnolDirectRightResolventCLM (barC c)
local notation "Z" => fun c => FiniteForcing.coefficient (star (BurnolCompletedMellinCoordinate.value c))
local notation "ζ" => fun c => riemannZeta (star (BurnolCompletedMellinCoordinate.value c))
local notation "counted" => fun c => floorFromResponses c + ζ c • elementarySource c
local notation "countedPrice" => fun c =>
  moment c (E (S (nativeSmooth c) : Hq)) * ζ c +
    CoefficientJet.zetaJet 1 (star (BurnolCompletedMellinCoordinate.value c))

private theorem collar_difference (c : BurnolCompletedMellinCoordinate) (n : Nat) (covered : 2 ≤ n) :
    CollarRead (difference c n) = (-coefficientStep c n) • collarPower c := by
  apply Lp.ext
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ band (difference c n), actual_difference_raw c n covered,
    Lp.coeFn_smul (-coefficientStep c n) (collarPower c), (seed_memLp c).coeFn_toLp] with
    x localRead raw scale seed
  change collarPower c x = _ at seed
  rw [localRead, raw, scale, Pi.smul_apply, smul_eq_mul, seed]

private theorem finite_collar (c : BurnolCompletedMellinCoordinate) (n : Nat) :
    CollarRead (compensated c (n+2)) =
      CollarRead (compensated c 2) + (Z c 2-Z c (n+2)) • collarPower c := by
  induction n with
  | zero => simp only [Nat.zero_add, sub_self, zero_smul, add_zero]
  | succ n earlier =>
    have actual := collar_difference c (n+2) (by omega)
    change CollarRead (compensated c (n+2+1)-compensated c (n+2)) = _ at actual
    rw [map_sub, coefficientStep] at actual
    change CollarRead (compensated c (n+2+1)) =
      CollarRead (compensated c 2) + (Z c 2-Z c (n+2+1)) • collarPower c
    linear_combination (norm := module) actual + earlier

private theorem complete_collar (c : BurnolCompletedMellinCoordinate) :
    CollarRead (counted c) = CollarRead (compensated c 2) + (Z c 2-ζ c) • collarPower c := by
  have whole : Tendsto (fun n : Nat => compensated c (n+2)) atTop (𝓝 (counted c)) :=
    (whole_limit c).comp (tendsto_add_atTop_nat 1)
  have coefficient : Tendsto (fun n : Nat => Z c (n+2)) atTop (𝓝 (ζ c)) :=
    (coefficient_limit c).comp (tendsto_add_atTop_nat 1)
  have other := (tendsto_const_nhds (x := CollarRead (compensated c 2))).add
    (((tendsto_const_nhds (x := Z c 2)).sub coefficient).smul_const (collarPower c))
  apply tendsto_nhds_unique (((CollarRead).continuous.tendsto _).comp whole)
  exact other.congr' (Eventually.of_forall fun n => (finite_collar c n).symm)

/-- An actual complete count keeps the exact first collar already paid by its finite cutoff. -/
theorem actual_counted_collar_source (c : BurnolCompletedMellinCoordinate) (n : Nat) :
    CollarRead (counted c-compensated c (n+2)) = (Z c (n+2)-ζ c) • collarPower c := by
  rw [map_sub, complete_collar c, finite_collar c n]
  module

private theorem complete_even (c : BurnolCompletedMellinCoordinate) : reflectL2 (counted c) = counted c := by
  apply tendsto_nhds_unique ((reflectL2.continuous.tendsto _).comp (whole_limit c))
  exact (whole_limit c).congr' (Eventually.of_forall fun n => (compensated_even c (n+1)).symm)

private theorem complete_compact (c : BurnolCompletedMellinCoordinate) :
    originalPhysicalCutoff q (counted c) = counted c := by
  let cut := (E).comp burnolQuarterRestriction
  change cut (counted c) = counted c
  apply tendsto_nhds_unique ((cut.continuous.tendsto _).comp (whole_limit c))
  exact (whole_limit c).congr' (Eventually.of_forall fun n => (actual_compact c (n+1) (Nat.succ_pos n)).symm)

/-- The two actual terms in the collar primitive are the log of the remaining interval and the quarter mean. -/
def collarPrimitive (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  (Real.log (q/x) : ℂ) - 2 * GapEuler.gapMean q c *
    (((q : ℂ)^(star c.value) - (x : ℂ)^(star c.value))/star c.value)

private theorem collar_primitive_source (c : BurnolCompletedMellinCoordinate)
    (x : ℝ) (positive : 0 < x) (bounded : x ≤ q) :
    2*(∫ y : ℝ in x..q, (y : ℂ)^(star c.value-1)*seedRaw c.value y) = collarPrimitive c x := by
  let s := star c.value
  let m := GapEuler.gapMean q c
  have exponent : -1 < (s-1).re := by
    simp only [s, sub_re, one_re, star_def, conj_re]
    linarith [c.rightHalf]
  have readIntegrand (y : ℝ) (inside : y ∈ Ioo x q) :
      (y : ℂ)^(s-1)*seedRaw c.value y = (1/2 : ℂ)*(y : ℂ)⁻¹-m*(y : ℂ)^(s-1) := by
    have live := positive.trans inside.1
    have power : (y : ℂ)^(s-1)*(y : ℂ)^(-s) = (y : ℂ)⁻¹ := by
      rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr live.ne'),
        show s-1+-s=(-1 : ℂ) by ring, Complex.cpow_neg, Complex.cpow_one]
    unfold seedRaw powerRaw
    rw [abs_of_pos live]
    change (y : ℂ)^(s-1)*((1/2 : ℂ)*((y : ℂ)^(-s)-rawMean (powerRaw c.value))) = _
    linear_combination (1/2 : ℂ)*power - (y : ℂ)^(s-1)*mean_power c
  have transformed := intervalIntegral.integral_congr_Ioo_of_le (μ := volume) bounded readIntegrand
  have inverseCont : ContinuousOn (fun y : ℝ => (y : ℂ)⁻¹) (Icc x q) :=
    Complex.continuous_ofReal.continuousOn.inv₀ (fun y member =>
      Complex.ofReal_ne_zero.mpr (positive.trans_le member.1).ne')
  have inverseDomain : IntervalIntegrable (fun y : ℝ => (y : ℂ)⁻¹) volume x q :=
    inverseCont.intervalIntegrable_of_Icc bounded
  have powerDomain : IntervalIntegrable (fun y : ℝ => (y : ℂ)^(s-1)) volume x q :=
    intervalIntegral.intervalIntegrable_cpow' exponent
  change 2*(∫ y : ℝ in x..q, (y : ℂ)^(s-1)*seedRaw c.value y) = _
  rw [transformed, intervalIntegral.integral_sub (inverseDomain.const_mul _) (powerDomain.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_cpow (Or.inl exponent),
    sub_add_cancel]
  simp_rw [← Complex.ofReal_inv, intervalIntegral.integral_ofReal, integral_inv_of_pos positive
    (positive.trans_le bounded)]
  unfold collarPrimitive
  change 2*((1/2 : ℂ)*(Real.log (q/x) : ℂ)-m*(((q : ℂ)^s-(x : ℂ)^s)/s)) = _
  ring

private theorem actual_collar_action (c : BurnolCompletedMellinCoordinate) (v : BurnolL2)
    (even : reflectL2 v = v) (a : ℂ) (source : CollarRead v = a • collarPower c) :
    (R₀ c v : ℝ → ℂ) =ᵐ[volume.restrict band] fun x =>
      (x : ℂ)^(-star c.value)*(-moment c v+a*collarPrimitive c x) := by
  have raw : (v : ℝ → ℂ) =ᵐ[volume.restrict band] fun x => a * seedRaw c.value x := by
    have readLocal := LpToLpRestrictCLM_coeFn ℂ band v
    change (CollarRead v : ℝ → ℂ) =ᵐ[volume.restrict band] (v : ℝ → ℂ) at readLocal
    rw [source] at readLocal
    filter_upwards [readLocal, Lp.coeFn_smul a (collarPower c), (seed_memLp c).coeFn_toLp] with
      x actual scale seed
    change collarPower c x = _ at seed
    rw [← actual, scale, Pi.smul_apply, smul_eq_mul, seed]
  filter_upwards [ae_restrict_of_ae (actual_quarter_endpoint_action c v even),
    ae_restrict_mem measurableSet_Ioc] with x action inside
  have positive : 0 < x := (by norm_num : 0 < q/2).trans inside.1
  have interval : (∫ y : ℝ in x..q, (y : ℂ)^(star c.value-1)*v y) =
      a*(∫ y : ℝ in x..q, (y : ℂ)^(star c.value-1)*seedRaw c.value y) := by
    rw [intervalIntegral.integral_of_le inside.2, intervalIntegral.integral_of_le inside.2,
      ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc_left inside.1.le) raw] with y value
    rw [value]
    ring
  rw [action positive inside.2, interval, ← collar_primitive_source c x positive inside.2]
  ring

/-- The actual accumulated R difference on the first collar uses the same two source coefficients as its exterior and next count. -/
theorem actual_counted_R_collar (c : BurnolCompletedMellinCoordinate) (n : Nat) :
    (R₀ c (counted c-compensated c (n+2)) : ℝ → ℂ) =ᵐ[volume.restrict band] fun x =>
      (x : ℂ)^(-star c.value) * (-(countedPrice c-countedJetPrice c (n+1)) +
        (Z c (n+2)-ζ c)*collarPrimitive c x) := by
  let v := counted c-compensated c (n+2)
  have compact : originalPhysicalCutoff q v = v := by
    let cut := (E).comp burnolQuarterRestriction
    change cut (counted c-compensated c (n+2)) = v
    rw [map_sub]
    exact congrArg₂ (· - ·) (complete_compact c) (actual_compact c (n+2) (by omega))
  have even : reflectL2 v = v := by
    dsimp only [v]
    rw [map_sub, complete_even, compensated_even]
  have whole := (actual_counted_R_fields c).1
  change quarterExterior (R₀ c (counted c)) = countedPrice c • quarterTail c at whole
  have initial := finite_R_exterior c (n+1)
  have exterior : quarterExterior (R₀ c v) =
      (countedPrice c-countedJetPrice c (n+1)) • quarterTail c := by
    dsimp only [v]
    rw [map_sub, map_sub, whole, initial, sub_smul]
  have momentRead := actual_compact_R_exterior c v compact even
  rw [exterior] at momentRead
  have same : moment c v = countedPrice c-countedJetPrice c (n+1) := by
    apply sub_eq_zero.mp
    apply (smul_eq_zero.mp (show (moment c v-(countedPrice c-countedJetPrice c (n+1))) • quarterTail c = 0 by
      rw [sub_smul, momentRead, sub_self])).resolve_right (quarter_tail_ne_zero (barC c))
  have source := actual_collar_action c v even _ (actual_counted_collar_source c n)
  rw [same] at source
  exact source

end OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
