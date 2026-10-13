import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.TwoWindow.Action
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalTwoWindowInverseForcing
open Complex MeasureTheory Set Filter OriginalRieszSource
open scoped Topology InnerProductSpace
local notation "q" => (1/4:ℝ)

theorem two_window_positive (h x : ℝ) (inside : x∈uIcc (lowerRadius h) (upperRadius h)) : 0<x := by
  have lower : 0<lowerRadius h := mul_pos (by norm_num) (Real.exp_pos _)
  have upper : 0<upperRadius h := mul_pos (by norm_num) (Real.exp_pos _)
  exact (lt_min lower upper).trans_le inside.1
theorem jointProduct_intervalIntegrable (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) :
    IntervalIntegrable (jointProduct coordinate h) volume (lowerRadius h) (upperRadius h) := by
  apply ContinuousOn.intervalIntegrable
  intro x inside
  exact (jointProduct_continuousAt coordinate h x (two_window_positive h x inside)).continuousWithinAt
theorem forcingCross_intervalIntegrable (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) :
    IntervalIntegrable (forcingCross coordinate h) volume (lowerRadius h) (upperRadius h) := by
  apply ContinuousOn.intervalIntegrable
  intro x inside
  exact (forcingCross_continuousAt coordinate h x (two_window_positive h x inside)).continuousWithinAt

theorem original_two_window_integrated_action (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) :
    coupling coordinate*(∫ x:ℝ in (lowerRadius h)..(upperRadius h),jointProduct coordinate h x)=
      sourceAction coordinate h (upperRadius h)-sourceAction coordinate h (lowerRadius h)-
        (∫ x:ℝ in (lowerRadius h)..(upperRadius h),forcingCross coordinate h x) := by
  have product:=jointProduct_intervalIntegrable coordinate h
  have forcing:=forcingCross_intervalIntegrable coordinate h
  have generated:=intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x inside=>original_two_leg_source_action coordinate h x (two_window_positive h x inside))
    ((product.const_mul (coupling coordinate)).add forcing)
  rw [intervalIntegral.integral_add (product.const_mul (coupling coordinate)) forcing,
    intervalIntegral.integral_const_mul] at generated
  exact eq_sub_of_add_eq generated

theorem original_source_pair_two_window (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) :
    OriginalRieszFinitePairing.sourcePairRead coordinate h=
      (2:ℂ)*(∫ x:ℝ in (lowerRadius h)..(upperRadius h),jointProduct coordinate h x) := by
  have cancel : lowerScale h*upperScale h=1 := by
    unfold lowerScale upperScale
    rw [← Real.exp_add,show -h/2+h/2=0 by ring,Real.exp_zero]
  have doubled : upperScale h*upperScale h=Real.exp h := by
    unfold upperScale
    rw [← Real.exp_add]
    congr 1
    ring
  have lowerEndpoint : upperScale h*(q*Real.exp (-h))=lowerRadius h := by
    unfold upperScale lowerRadius FixedWindowFourierReaction.actualRadius
    rw [mul_left_comm,← Real.exp_add]
    congr 1
    ring
  have upperEndpoint : upperScale h*q=upperRadius h := by
    unfold upperScale upperRadius FixedWindowFourierReaction.actualRadius
    ring
  have raw : OriginalRieszFinitePairing.sourceProduct coordinate h=
      fun x:ℝ=>jointProduct coordinate h (upperScale h*x) := by
    funext x
    unfold OriginalRieszFinitePairing.sourceProduct jointProduct b p
    rw [← mul_assoc,cancel,one_mul,← mul_assoc,doubled]
    ring
  unfold OriginalRieszFinitePairing.sourcePairRead
  rw [raw]
  change (2:ℂ)*(upperScale h:ℂ)*(∫ x:ℝ in (q*Real.exp (-h))..q,
    jointProduct coordinate h (upperScale h*x))=_
  rw [intervalIntegral.integral_comp_mul_left (c:=upperScale h) (jointProduct coordinate h)
    (Real.exp_ne_zero (h/2)),lowerEndpoint,upperEndpoint]
  change (2:ℂ)*(upperScale h:ℂ)*((upperScale h)⁻¹•
    (∫ x:ℝ in (lowerRadius h)..(upperRadius h),jointProduct coordinate h x))=_
  simp only [Complex.real_smul,Complex.ofReal_inv]
  have scaleNe : (upperScale h:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  rw [mul_assoc,mul_inv_cancel_left₀ scaleNe]

def forcingPrice (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
  (2:ℂ)*(sourceAction coordinate h (upperRadius h)-sourceAction coordinate h (lowerRadius h)-
    (∫ x:ℝ in (lowerRadius h)..(upperRadius h),forcingCross coordinate h x))/coupling coordinate

theorem original_source_pair_forcing_price (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) :
    OriginalRieszFinitePairing.sourcePairRead coordinate h=forcingPrice coordinate h := by
  have nonzero : coupling coordinate≠0 := OriginalRieszSourceGreen.source_cross_parameter_ne_zero coordinate coordinate
  have action:=original_two_window_integrated_action coordinate h
  rw [original_source_pair_two_window]
  unfold forcingPrice
  apply (eq_div_iff nonzero).mpr
  linear_combination 2*action

end OriginalTwoWindowInverseForcing
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
