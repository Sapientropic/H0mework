import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.OriginTrace
import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.PositionGapEuler

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKDirectRCofinalDivision

open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent

open private actual_gap_cutoff density_actual from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.PositionGap
open private actual_raw_even from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalOutsideVolterraSource.Source

local notation "q" => (1/4 : ℝ)
local notation "r₀" => (q/2)
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate

/-- The actual flat position gap computes the same weighted source trace from
its centre density and the original compact unit. -/
theorem original_centre_trace_from_gap (c : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (even : reflectL2 value = value) (gap : value ∈ locallyConstantFace q) :
    originalCentreTrace c value =
      2*positionGapCentreDensity (splitAtPhysicalCutoff r₀ value).1*((r₀ : ℂ)^(star c.value)/(star c.value)) := by
  obtain ⟨a, constant⟩ := mem_locallyConstantFace_iff_exists.mp gap
  have source : burnolQuarterRestriction value = a • intervalConstant q := constant.symm
  let u := FiniteMobiusResolventFlux.box r₀
  have cutoff : FiniteMobiusResolventFlux.cutoff r₀ value = a • u := actual_gap_cutoff value a source
  have inner : ∀ᵐ t : ℝ ∂volume.restrict (Ioc 0 r₀), (a • u : BurnolL2) t = a := by
    filter_upwards [ae_restrict_of_ae (Lp.coeFn_smul a u),
      ae_restrict_of_ae (FiniteMobiusResolventFlux.box_read r₀), ae_restrict_mem measurableSet_Ioc]
      with t scalar read member
    have inside : t ∈ symmetricInterval r₀ := ⟨(by norm_num : (-r₀ : ℝ) ≤ 0).trans member.1.le, member.2⟩
    rw [scalar, Pi.smul_apply, smul_eq_mul, read, indicator_of_mem inside, mul_one]
  let s := star c.value
  have right : 0 < s.re := by
    have half : 1/2 < s.re := by simpa only [s, Complex.star_def, Complex.conj_re] using c.rightHalf
    linarith
  have nonzero : s ≠ 0 := by
    intro zero
    rw [zero, Complex.zero_re] at right
    exact (lt_irrefl _ right)
  have power : (∫ t : ℝ in 0..r₀, (t : ℂ)^(s-1)) = (r₀ : ℂ)^s/s := by
    rw [integral_cpow (Or.inl (by simp only [Complex.sub_re, Complex.one_re]; linarith)),
      sub_add_cancel, Complex.ofReal_zero, Complex.zero_cpow nonzero, sub_zero]
    norm_num [Complex.ofReal_div]
  rw [original_centre_trace_integral c value even, density_actual value a source, cutoff]
  have read : (∫ t : ℝ in 0..r₀, (t : ℂ)^(s-1)*(a • u : BurnolL2) t) =
      a*(∫ t : ℝ in 0..r₀, (t : ℂ)^(s-1)) := by
    rw [← intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ r₀),
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ r₀)]
    apply integral_congr_ae
    filter_upwards [inner] with t unit
    rw [unit, mul_comm]
  change 2*(∫ t : ℝ in 0..r₀, (t : ℂ)^(s-1)*(a • u : BurnolL2) t) = 2*a*((r₀ : ℂ)^s/s)
  rw [read, power, mul_assoc]

/-- On the literal cofinal source, the weighted trace is already determined
by positionGap. The continuous mixed action still reads the whole original born. -/
theorem actual_division_origin_trace_action
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
    (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat) :
    let c := burnolDivisionZeroCompletedMellinCoordinate observation half.down
    let x := D.raw observation nontrivial half depth ordinal
    let current := splitAtPhysicalCutoff r₀ x
    let weighted := 2*positionGapCentreDensity current.1*((r₀ : ℂ)^c.value/c.value)
    let mixed := originAwareMixedAction (barC c) (current, weighted)
    let born := DirectRDivisionControls.bornRead observation nontrivial half depth ordinal
    originalCentreTrace (barC c) x = weighted ∧
      mixed = positionGapMixedAction c current ∧ recoverPositionGapSplit mixed = born ∧
      ((physicalProjectionFromCentre mixed : BurnolL2), born-(physicalProjectionFromCentre mixed : BurnolL2)) =
        OriginalKCombFirstFullSourceDynamics.input observation nontrivial half depth (ordinal+1) := by
  dsimp only
  let c := burnolDivisionZeroCompletedMellinCoordinate observation half.down
  let x := D.raw observation nontrivial half depth ordinal
  let current := splitAtPhysicalCutoff r₀ x
  let weighted := 2*positionGapCentreDensity current.1*((r₀ : ℂ)^c.value/c.value)
  let born := DirectRDivisionControls.bornRead observation nontrivial half depth ordinal
  let mixed := originAwareMixedAction (barC c) (current, weighted)
  have gap := OriginalKCombCofinalRAction.actual_source_gap observation nontrivial half depth ordinal
  have even := actual_raw_even observation nontrivial half depth ordinal
  have trace : originalCentreTrace (barC c) x = weighted := by
    have computed := original_centre_trace_from_gap (barC c) x even gap
    change originalCentreTrace (barC c) x =
      2*positionGapCentreDensity current.1*((r₀ : ℂ)^(star (star c.value))/(star (star c.value))) at computed
    rwa [star_star] at computed
  have originalR : burnolDirectRightResolventCLM (barC (barC c)) x = burnolDirectRightResolventCLM c x := by
    change burnolDirectRightResolvent (star (star c.value)/2) x = burnolDirectRightResolvent (c.value/2) x
    rw [star_star]
  have actual : mixed = positionGapMixedAction c current := by
    change originAwareMixedAction (barC c) (current, weighted) = _
    rw [← trace, actual_origin_aware_mixed_action (barC c) x even, originalR]
    exact (actual_position_gap_mixed_action c x gap).symm
  have bornNext := actual_division_position_gap_mixed_next observation nontrivial half depth ordinal
  refine ⟨trace, actual, ?_, ?_⟩
  · exact (congrArg recoverPositionGapSplit actual).trans bornNext.2.1
  · exact (congrArg (fun z => ((physicalProjectionFromCentre z : BurnolL2),
      born-(physicalProjectionFromCentre z : BurnolL2))) actual).trans bornNext.2.2.2.2.1

end OriginalKDirectRCofinalDivision
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
