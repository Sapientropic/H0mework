import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar
import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.Fixed

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent

open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszSource OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKSourceResolventReconstruction OriginalKFiniteOrderRelease.UnitPowerJordanSource
open OriginalKElementaryArithmeticAction.FreeParameter.Riesz
open OriginalKElementaryArithmeticAction.FreeParameter.UnitConsumer
open OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.Consumer
open OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.Cotest
open OriginalKElementaryArithmeticAction.FreeParameter.SourceWindow
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeSmooth
open scoped InnerProductSpace Topology

open private collarPower seed_endpoint_ne_zero from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar
open private compensated_even from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical
open private quarter_even_integral from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Endpoint
open private conjugate_zero_count from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit
open private collar_primitive_source complete_even complete_compact from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar

local notation "q" => (1/4 : ℝ)
local notation "band" => Ioc (q/2) q
local notation "closedBand" => Icc (q/2) q
local notation "box" => symmetricInterval q
local notation "CollarRead" => LpToLpRestrictCLM ℝ ℂ ℂ volume 2 band
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "R₀" => fun c => burnolDirectRightResolventCLM (barC c)
local notation "Z" => fun c => FiniteForcing.coefficient (star (BurnolCompletedMellinCoordinate.value c))
local notation "h₀" => Real.log stageZeroSonineQ

private theorem collar_primitive_derivative (c : BurnolCompletedMellinCoordinate) (x : ℝ)
    (member : x ∈ closedBand) :
    HasDerivWithinAt (collarPrimitive c)
      (2*(-((x : ℂ)^(star c.value-1)*seedRaw c.value x))) closedBand x := by
  let w := fun y : ℝ => (y : ℂ)^(star c.value-1)*seedRaw c.value y
  have regular (y : ℝ) (live : y ≠ 0) : ContinuousAt w y := by
    have power := (Complex.continuousAt_ofReal_cpow_const |y| (-star c.value)
      (Or.inr (abs_ne_zero.mpr live))).comp continuous_abs.continuousAt
    have seed : ContinuousAt (seedRaw c.value) y := by
      unfold seedRaw powerRaw
      exact continuousAt_const.mul (power.sub continuousAt_const)
    exact (Complex.continuousAt_ofReal_cpow_const y (star c.value-1) (Or.inr live)).mul seed
  have measurable : Measurable w := by
    apply measurable_of_continuousOn_compl_singleton 0
    intro y outside
    exact (regular y (by simpa only [mem_compl_iff, mem_singleton_iff] using outside)).continuousWithinAt
  have positive : 0 < x := (by norm_num : 0 < q/2).trans_le member.1
  have cont : ContinuousOn w (Icc x q) :=
    fun y hy => (regular y (positive.trans_le hy.1).ne').continuousWithinAt
  have domain : IntervalIntegrable w volume x q := cont.intervalIntegrable_of_Icc member.2
  have derivative := (intervalIntegral.integral_hasDerivAt_left domain
    measurable.stronglyMeasurable.stronglyMeasurableAtFilter (regular x positive.ne')).const_mul (2 : ℂ)
  exact derivative.hasDerivWithinAt.congr_of_mem
    (fun y hy => (collar_primitive_source c y ((by norm_num : 0 < q/2).trans_le hy.1) hy.2).symm) member

private theorem collar_primitive_ne_zero (c : BurnolCompletedMellinCoordinate) :
    ∃ x ∈ closedBand, collarPrimitive c x ≠ 0 := by
  by_contra! silent
  have member : q ∈ closedBand := ⟨by norm_num, le_rfl⟩
  have zero := (hasDerivWithinAt_const q closedBand (0 : ℂ)).congr_of_mem silent member
  have different := uniqueDiffOn_Icc (by norm_num : q/2 < q) q member
  have same := different.eq_deriv closedBand (collar_primitive_derivative c q member) zero
  exact mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0)
    (neg_ne_zero.mpr (mul_ne_zero
      (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num : (q : ℂ) ≠ 0)))
      (seed_endpoint_ne_zero c))) same

/-- The actual collar action retains both coordinates. The endpoint fixes the exterior price and the primitive fixes the counted cell. -/
theorem collar_action_injective (c : BurnolCompletedMellinCoordinate) (a b a' b' : ℂ)
    (same : (fun x : ℝ => (x : ℂ)^(-star c.value)*(-a+b*collarPrimitive c x)) =ᵐ[volume.restrict band]
      fun x => (x : ℂ)^(-star c.value)*(-a'+b'*collarPrimitive c x)) :
    a = a' ∧ b = b' := by
  have affine : (fun x => -a+b*collarPrimitive c x) =ᵐ[volume.restrict band]
      fun x => -a'+b'*collarPrimitive c x := by
    filter_upwards [same, ae_restrict_mem measurableSet_Ioc] with x point member
    have positive : 0 < x := (by norm_num : 0 < q/2).trans member.1
    exact mul_left_cancel₀
      (Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr positive.ne'))) point
  rw [Measure.restrict_congr_set Ioc_ae_eq_Icc] at affine
  have regular : ContinuousOn (collarPrimitive c) closedBand :=
    fun x member => (collar_primitive_derivative c x member).continuousWithinAt
  have equal := Measure.eqOn_Icc_of_ae_eq volume (by norm_num : q/2 ≠ q) affine
    (continuousOn_const.add (continuousOn_const.mul regular))
    (continuousOn_const.add (continuousOn_const.mul regular))
  have atEdge : collarPrimitive c q = 0 := by
    rw [← collar_primitive_source c q (by norm_num) le_rfl, intervalIntegral.integral_same, mul_zero]
  have first := equal (show q ∈ closedBand from ⟨by norm_num, le_rfl⟩)
  dsimp only at first
  rw [atEdge, mul_zero, mul_zero, add_zero, add_zero] at first
  have firstPrice := neg_injective first
  refine ⟨firstPrice, ?_⟩
  obtain ⟨x, member, live⟩ := collar_primitive_ne_zero c
  have inside := equal member
  dsimp only at inside
  rw [firstPrice] at inside
  exact mul_right_cancel₀ live (add_left_cancel inside)

private theorem fixed_clock_bounds : 0 ≤ h₀ ∧ h₀ ≤ Real.log 2 := by
  constructor
  · apply Real.log_nonneg
    change 1 ≤ Real.sqrt 3
    exact Real.one_le_sqrt.mpr (by norm_num)
  · apply Real.log_le_log stageZeroSonineQ_pos
    change Real.sqrt 3 ≤ 2
    exact Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩

private theorem original_moved_collar_price (c : BurnolCompletedMellinCoordinate) (v : BurnolL2)
    (compact : originalPhysicalCutoff q v = v) (even : reflectL2 v = v) :
    inner ℂ (movedTest c h₀) v = 2*inner ℂ (CollarRead (movedTest c h₀)) (CollarRead v) := by
  let test := movedTest c h₀
  let f := fun x : ℝ => inner ℂ (test x) (v x)
  have domain : Integrable f volume := L2.integrable_inner (𝕜 := ℂ) test v
  have testEven : reflectL2 test = test := by
    have kernelEven := mem_evenL2ClosedFace_iff.mp (burnolCompletedMellinRieszVector c).property.2
    unfold test movedTest
    rw [map_sub, map_smul, reflectL2_burnolMultiplicativeDilation, kernelEven]
  have left := Lp.coeFn_compMeasurePreserving test negMeasurePreserving
  have right := Lp.coeFn_compMeasurePreserving v negMeasurePreserving
  change (reflectL2 test : ℝ → ℂ) =ᵐ[volume] fun x => test (-x) at left
  change (reflectL2 v : ℝ → ℂ) =ᵐ[volume] fun x => v (-x) at right
  rw [testEven] at left
  rw [even] at right
  have parity : ∀ᵐ x ∂volume, f (-x) = f x := by
    filter_upwards [left, right] with x l r
    change inner ℂ (test (-x)) (v (-x)) = inner ℂ (test x) (v x)
    rw [← l, ← r]
  have support := originalPhysicalCutoff_coeFn q v
  rw [compact] at support
  have carrier : f =ᵐ[volume] (box).indicator f := by
    filter_upwards [support] with x source
    by_cases inside : x ∈ box
    · rw [indicator_of_mem inside]
    · have zero : v x = 0 := source.trans (indicator_of_notMem inside _)
      rw [indicator_of_notMem inside]
      change inner ℂ (test x) (v x) = 0
      rw [zero, inner_zero_right]
  obtain ⟨nn, small⟩ := fixed_clock_bounds
  have reach : q/2 ≤ q*Real.exp (-h₀) := by
    have half : (1/2 : ℝ) = Real.exp (-Real.log 2) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]
      norm_num
    have bound := Real.exp_le_exp.mpr (neg_le_neg small)
    rw [← half] at bound
    linarith
  have gap := actual_moved_gap c h₀ nn
  have vanished : (∫ x in (0 : ℝ)..(q/2), f x) = 0 := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ q/2)]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_of_ae gap, ae_restrict_mem measurableSet_Ioc] with x atx inside
    have zero : test x = 0 := atx (by rw [abs_of_pos inside.1]; exact inside.2.trans reach)
    change inner ℂ (test x) (v x) = 0
    rw [zero, inner_zero_left]
  have split := intervalIntegral.integral_add_adjacent_intervals
    (domain.intervalIntegrable (a := 0) (b := q/2))
    (domain.intervalIntegrable (a := q/2) (b := q))
  rw [vanished, zero_add, intervalIntegral.integral_of_le (by norm_num : q/2 ≤ q)] at split
  have localRead : (∫ x in band, f x) = inner ℂ (CollarRead test) (CollarRead v) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [LpToLpRestrictCLM_coeFn ℂ band test, LpToLpRestrictCLM_coeFn ℂ band v]
      with x testRead valueRead
    change inner ℂ (test x) (v x) = inner ℂ (CollarRead test x) (CollarRead v x)
    rw [testRead, valueRead]
  change inner ℂ test v = _
  rw [L2.inner_def, integral_congr_ae carrier, integral_indicator (measurableSet_symmetricInterval q),
    quarter_even_integral f domain.integrableOn parity, ← split, localRead]

/-- The original fixed consumer reads its entire counted contribution from the actual R collar. -/
theorem actual_fixed_counted_collar_price (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) (n : Nat) (a b : ℂ)
    (profile : (R₀ c (floorFromResponses c-compensated c (n+2)) : ℝ → ℂ) =ᵐ[volume.restrict band]
      fun x => (x : ℂ)^(-star c.value)*(-a+b*collarPrimitive c x)) :
    inner ℂ (movedTest c h₀) (floorFromResponses c) =
      inner ℂ (movedTest c h₀) (compensated c (n+2)) +
        (2*b)*inner ℂ (CollarRead (movedTest c h₀)) (collarPower c) := by
  have conjugate := conjugate_zero_count c zero
  have actual := actual_counted_R_collar c n
  simp only [conjugate, zero_smul, add_zero, mul_zero, zero_add, sub_zero] at actual
  have price := (collar_action_injective c a b _ _ (profile.symm.trans actual)).2
  have supported : originalPhysicalCutoff q (floorFromResponses c) = floorFromResponses c := by
    simpa only [conjugate, zero_smul, add_zero] using complete_compact c
  have parity : reflectL2 (floorFromResponses c) = floorFromResponses c := by
    simpa only [conjugate, zero_smul, add_zero] using complete_even c
  let v := floorFromResponses c-compensated c (n+2)
  have support : originalPhysicalCutoff q v = v := by
    let cut := (burnolQuarterZeroExtension).comp burnolQuarterRestriction
    change cut (floorFromResponses c-compensated c (n+2)) = v
    rw [map_sub]
    exact congrArg₂ (· - ·) supported (actual_compact c (n+2) (by omega))
  have even : reflectL2 v = v := by
    dsimp only [v]
    rw [map_sub, parity, compensated_even]
  have localRead := actual_counted_collar_source c n
  simp only [conjugate, zero_smul, add_zero, sub_zero] at localRead
  have native := original_moved_collar_price c v support even
  change inner ℂ (movedTest c h₀) (floorFromResponses c-compensated c (n+2)) =
    2*inner ℂ (CollarRead (movedTest c h₀)) (CollarRead (floorFromResponses c-compensated c (n+2))) at native
  rw [inner_sub_right, localRead, ← price,
    inner_smul_right (CollarRead (movedTest c h₀)) (collarPower c) b] at native
  linear_combination native

private theorem actual_fixed_receipt_net (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) :
    -(installedOriginalKReceiptAt (burnolPaZeroObservation c zero)
      (burnolPaZeroObservation_nontrivial c zero) c.rightHalf).fixedResidual = Fixed.nativeFixedNet c := by
  obtain ⟨nonnegative, bounded⟩ := fixed_clock_bounds
  rw [installedOriginalK_fixedResidual_eq_original,
    OriginalKPairedBEulerJunctionSource.ResponseForcing.Consumer.actual_original_fixed_residual c zero]
  unfold OriginalKPairedBEulerJunctionSource.ResponseForcing.Consumer.completeResponseNet
  rw [OriginalKElementaryArithmeticAction.FreeParameter.FixedConsumer.actual_complete_price c zero _ nonnegative bounded,
    star_star, OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.CrossContact.actual_native_joint_read c _ bounded,
    actual_complete_native_price c _ nonnegative bounded]
  unfold Fixed.nativeFixedNet
  ring

/-- The installed fixed receipt consumes the recovered counted price and retains the original clocks and seeds. -/
theorem actual_fixed_net_from_R_collar (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) (n : Nat) (a b : ℂ)
    (profile : (R₀ c (floorFromResponses c-compensated c (n+2)) : ℝ → ℂ) =ᵐ[volume.restrict band]
      fun x => (x : ℂ)^(-star c.value)*(-a+b*collarPrimitive c x)) :
    let test := fourierTest c h₀
    let acted := sourceResolvent (barC c) test;
    -(installedOriginalKReceiptAt (burnolPaZeroObservation c zero)
      (burnolPaZeroObservation_nontrivial c zero) c.rightHalf).fixedResidual =
      (pairedMellinTranslationCharacter c.value h₀ -
        pairedMellinTranslationCharacter (star c.value) h₀)*kernelSelfSource c +
      (1/2 : ℂ)*(inner ℂ (movedTest c h₀) (compensated c (n+2)) +
        (2*b)*inner ℂ (CollarRead (movedTest c h₀)) (collarPower c) +
        ForcingPrimitive.leadingCoefficient c*inner ℂ (twoClockCorrection c h₀) (centeredLogColumn c 0) -
        (1/2 : ℂ)*((nativeGamma c-originCoefficient c)*inner ℂ acted Response.wholeU -
          nativeBeta c*inner ℂ acted Response.wholeV +
          2*nativeBeta c*inner ℂ test ConstantDual.seed +
          star c.value*nativeBeta c*inner ℂ acted ConstantDual.seed)) := by
  rw [actual_fixed_receipt_net c zero, FixedPrice.actual_fixed_counted_net c zero,
    actual_fixed_counted_collar_price c zero n a b profile]

end OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
