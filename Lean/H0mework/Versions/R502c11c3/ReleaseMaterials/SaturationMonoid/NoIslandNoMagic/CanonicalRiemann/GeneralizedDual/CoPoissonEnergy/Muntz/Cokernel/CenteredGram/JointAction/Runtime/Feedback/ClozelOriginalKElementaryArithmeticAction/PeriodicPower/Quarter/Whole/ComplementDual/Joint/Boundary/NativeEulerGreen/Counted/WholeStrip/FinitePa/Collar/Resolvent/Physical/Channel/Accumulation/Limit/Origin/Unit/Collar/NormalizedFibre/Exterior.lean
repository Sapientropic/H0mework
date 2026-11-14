import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent

open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszFinitePairing.CoPoisson.Ward OriginalKCoefficientBFiniteAction
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source
open scoped Topology

open private complete_even from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar
open private compensated_even from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical
open private quarterTail from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation
open private even_eq_of_positive from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.PaUpdate
open private cut_reflection from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.CorePosition
open private inward_even from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.QuarterSourceCommutator
open private radiusTail_positiveRead from
  H0mework.Versions.R7e4da746.Arithmetic.RiemannFirstSource.FirstCurrent
open private count_below_log_scale from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre

local notation "q" => (1/4 : ℝ)
local notation "r" => (q/2)
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "s₀" => fun c => star (BurnolCompletedMellinCoordinate.value c)
local notation "whole" => fun c => floorFromResponses c+riemannZeta (s₀ c) • elementarySource c
local notation "delta" => fun c (n : Nat) => whole c-compensated c (n+2)
local notation "acted" => fun c (n : Nat) => burnolDirectRightResolventCLM (barC c) (delta c n)
local notation "A" => fun c (n : Nat) => Prod.fst (clockCoefficients c (actualClockPair c n))
local notation "B" => fun c (n : Nat) => Prod.snd (clockCoefficients c (actualClockPair c n))
local notation "scale" => fun c (n : Nat) =>
  (Real.log ((n+2 : Nat) : ℝ) : ℂ)*((n+2 : Nat) : ℂ)^(-s₀ c)
local notation "O" => fun radius : ℝ => ContinuousLinearMap.id ℂ BurnolL2 -
  ContinuousLinearMap.comp (burnolRadiusZeroExtension radius) (burnolRadiusRestriction radius)
local notation "tail" => fun c => burnolRadiusNormalizedUnitTail (barC c) r (by norm_num)

private theorem outside_read (radius : ℝ) (value : BurnolL2) :
    ∀ᵐ x : ℝ ∂volume, O radius value x = if radius < |x| then value x else 0 := by
  filter_upwards [Lp.coeFn_sub value (originalPhysicalCutoff radius value),
    originalPhysicalCutoff_coeFn radius value] with x subtracted cut
  change (value-originalPhysicalCutoff radius value : BurnolL2) x = _
  rw [subtracted, Pi.sub_apply, cut]
  by_cases inside : |x| ≤ radius
  · have mem : x ∈ symmetricInterval radius := abs_le.mp inside
    rw [if_neg (not_lt_of_ge inside), indicator_of_mem mem, sub_self]
  · have missing : x ∉ symmetricInterval radius := fun hx => inside (abs_le.mpr hx)
    rw [if_pos (lt_of_not_ge inside), indicator_of_notMem missing, sub_zero]

private theorem outside_even (radius : ℝ) (value : BurnolL2)
    (even : reflectL2 value = value) : reflectL2 (O radius value) = O radius value := by
  have cut : reflectL2 (originalPhysicalCutoff radius value) =
      originalPhysicalCutoff radius (reflectL2 value) := cut_reflection radius value
  change reflectL2 (value-originalPhysicalCutoff radius value) =
    value-originalPhysicalCutoff radius value
  rw [map_sub, cut, even]

private theorem acted_even (c : BurnolCompletedMellinCoordinate) (n : Nat) :
    reflectL2 (acted c n) = acted c n := by
  apply inward_even
  change reflectL2 (whole c-compensated c (n+2)) = _
  rw [map_sub, complete_even, compensated_even]

private theorem half_tail_even (c : BurnolCompletedMellinCoordinate) :
    reflectL2 (tail c) = tail c := by
  unfold burnolRadiusNormalizedUnitTail
  rw [map_neg, map_add, reflectL2_reflectL2, add_comm]

private theorem actual_quarter_exterior (c : BurnolCompletedMellinCoordinate) (n : Nat) :
    O q (acted c n) = A c n • quarterTail c := by
  have full := (actual_counted_R_fields c).1
  have finite := (actual_compensated_R_fields c (n+1)).1
  change O q (burnolDirectRightResolventCLM (barC c) (whole c)) = _ at full
  change O q (burnolDirectRightResolventCLM (barC c) (compensated c (n+2))) = _ at finite
  change O q (burnolDirectRightResolventCLM (barC c) (whole c-compensated c (n+2))) = _
  rw [map_sub, map_sub, full, finite]
  dsimp only
  rw [actual_clock_coefficients]
  module

private def bandRead (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  if x ∈ Ioc r q then (x : ℂ)^(-s₀ c)*collarPrimitive c x else 0

private theorem actual_half_exterior_positive (c : BurnolCompletedMellinCoordinate) (n : Nat) :
    ∀ᵐ x : ℝ ∂volume, 0 < x →
      O r (acted c n) x = A c n*tail c x+B c n*bandRead c x := by
  have outer := outside_read q (acted c n)
  rw [actual_quarter_exterior c n] at outer
  filter_upwards [outside_read r (acted c n), outer,
    Lp.coeFn_smul (A c n) (quarterTail c), actual_settled_R_profile c n,
    radiusTail_positiveRead (barC c) q (by norm_num),
    radiusTail_positiveRead (barC c) r (by norm_num)] with x cutoff exterior scaled inside tailQ tailR pos
  rw [cutoff, abs_of_pos pos, tailR pos]
  change (if r<x then acted c n x else 0) =
    A c n*(if r<x then -(x : ℂ)^(-s₀ c) else 0)+B c n*bandRead c x
  unfold bandRead
  by_cases after : r < x
  · rw [if_pos after, if_pos after]
    by_cases beyond : q < x
    · rw [abs_of_pos pos, if_pos beyond, scaled, Pi.smul_apply, smul_eq_mul] at exterior
      change A c n*quarterTail c x = acted c n x at exterior
      have tailValue : quarterTail c x = -(x : ℂ)^(-s₀ c) := by
        simpa only [quarterTail, if_pos beyond, show (barC c).value = star c.value from rfl] using tailQ pos
      rw [← exterior, tailValue, if_neg (show x ∉ Ioc r q from fun mem => (not_le_of_gt beyond) mem.2), mul_zero, add_zero]
    · have bounded := le_of_not_gt beyond
      have covered : q/x < ((n+2 : Nat) : ℝ) :=
        ((div_lt_iff₀ pos).mpr (by linarith : q < 2*x)).trans_le (by exact_mod_cast Nat.le_add_left 2 n)
      rw [inside pos bounded covered, if_pos (show x ∈ Ioc r q from ⟨after,bounded⟩)]
      ring
  · rw [if_neg after, if_neg after, if_neg (show x ∉ Ioc r q from fun mem => after mem.1), mul_zero, mul_zero, add_zero]

/-- The literal half-quarter exterior is generated by the original two endpoint
coefficients, with the collar column realized by an actual counted action. -/
theorem actual_counted_half_exterior (c : BurnolCompletedMellinCoordinate) :
    ∃ column : BurnolL2, ∀ n : Nat,
      acted c n-originalPhysicalCutoff r (acted c n) = A c n • tail c+B c n • column := by
  have live : ∀ᶠ n : Nat in atTop, B c n ≠ 0 := by
    filter_upwards [(actual_phase_count_limit c).eventually
      (compl_singleton_mem_nhds_iff.mpr (by norm_num : -(1/2 : ℂ) ≠ 0))]
      with n near gone
    exact near (by simp only [gone, mul_zero, mem_singleton_iff])
  obtain ⟨j, nonzero⟩ := live.exists
  let column := (B c j)⁻¹ • (O r (acted c j)-A c j • tail c)
  have colEven : reflectL2 column = column := by
    dsimp only [column]
    rw [map_smul, map_sub, map_smul, outside_even r _ (acted_even c j), half_tail_even]
  have colRead : ∀ᵐ x : ℝ ∂volume, 0 < x → column x = bandRead c x := by
    filter_upwards [Lp.coeFn_smul (B c j)⁻¹ (O r (acted c j)-A c j • tail c),
      Lp.coeFn_sub (O r (acted c j)) (A c j • tail c), Lp.coeFn_smul (A c j) (tail c),
      actual_half_exterior_positive c j] with x scaled diff tailScale raw positive
    change ((B c j)⁻¹ • (O r (acted c j)-A c j • tail c) : BurnolL2) x = _
    rw [scaled, Pi.smul_apply, smul_eq_mul, diff, Pi.sub_apply, tailScale, Pi.smul_apply,
      smul_eq_mul, raw positive, add_sub_cancel_left, ← mul_assoc, inv_mul_cancel₀ nonzero, one_mul]
  refine ⟨column, fun n => ?_⟩
  change O r (acted c n) = _
  apply even_eq_of_positive _ _ (outside_even r _ (acted_even c n))
  · rw [map_add, map_smul, map_smul, half_tail_even, colEven]
  · filter_upwards [actual_half_exterior_positive c n, colRead,
      Lp.coeFn_add (A c n • tail c) (B c n • column), Lp.coeFn_smul (A c n) (tail c),
      Lp.coeFn_smul (B c n) column] with x raw col sum t b positive
    rw [raw positive, sum, Pi.add_apply, t, b, Pi.smul_apply, Pi.smul_apply,
      smul_eq_mul, smul_eq_mul, col positive]

/-- The normalized exterior has a strong limit on the same acted field, including
the first counted collar before it reaches the fixed two-clock consumer. -/
theorem actual_normalized_counted_half_exterior (c : BurnolCompletedMellinCoordinate) :
    Tendsto (fun n => countedNormalizedField c n-originalPhysicalCutoff r (countedNormalizedField c n))
      atTop (𝓝 ((-(1/2 : ℂ)) • tail c)) := by
  obtain ⟨column, exactField⟩ := actual_counted_half_exterior c
  have outer := (actual_scaled_outer_limit c).const_mul (-(1/2 : ℂ))
  simp only [mul_one] at outer
  have coefficient : Tendsto (fun n : Nat => (scale c n)⁻¹*A c n) atTop (𝓝 (-(1/2 : ℂ))) := by
    apply outer.congr'
    filter_upwards with n
    change -(1/2 : ℂ)*((scale c n)⁻¹*(-(2*A c n))) = _
    ring
  have limit := (coefficient.smul_const (tail c)).add ((count_below_log_scale c).smul_const column)
  simp only [zero_smul, add_zero] at limit
  apply limit.congr'
  filter_upwards with n
  change _ = O r ((scale c n)⁻¹ • acted c n)
  have exactExterior : O r (acted c n) = _ := exactField n
  rw [map_smul, exactExterior, smul_add, smul_smul, smul_smul]

end OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
