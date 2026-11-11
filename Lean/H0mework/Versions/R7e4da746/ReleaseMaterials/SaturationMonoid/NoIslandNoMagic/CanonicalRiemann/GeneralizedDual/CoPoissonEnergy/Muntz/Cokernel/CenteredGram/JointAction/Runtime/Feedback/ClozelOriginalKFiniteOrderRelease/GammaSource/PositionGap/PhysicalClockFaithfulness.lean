import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.OutsideHistory.ClockReconstruction
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.OutsideHistory.ExpandedGap
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.CompactFourierUniqueness
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.FourierInventoryAction

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.PhysicalClock

open BurnolPhysicalState Complex Filter MeasureTheory Set
open OriginalKFiniteOrderRelease.OutsideQuarterAction
open scoped Topology InnerProductSpace

open private exponentialIntegral exponentialIntegral_differentiable frequencyPoint real_slice
  centered_fourier_zero_head from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.CompactFourierUniqueness
open private interval_read from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.OutsideHistory.ExpandedGap

open private gap_restrict from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.OutsideHistory.ClockReconstruction

local notation "q" => (1/4 : ℝ)
local notation "F" => fourierL2
local notation "E" => burnolQuarterZeroExtension
local notation "P" => OriginalKCombPhysicalAction.physicalProjection
local notation "O" => OriginalKCombPhysicalAction.physicalRemainder
local notation "D" => burnolMultiplicativeDilation

private theorem frequency_point_injective : Function.Injective frequencyPoint := by
  intro x y same
  apply Complex.ofReal_injective
  apply mul_left_cancel₀ _ same
  exact mul_ne_zero
    (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero

private theorem constant_centered_fourier_on_interval
    (z : BurnolQuarterMeanZeroCarrier) {left right : ℝ} (width : left < right) (mean : ℂ)
    (localRead : EqOn (burnolTruncatedFourierRaw (z : BurnolQuarterIntervalL2))
      (fun _ => mean) (Icc left right)) : z = 0 := by
  let state := (z : BurnolQuarterIntervalL2)
  have analytic : AnalyticOnNhd ℂ (exponentialIntegral state) univ :=
    (exponentialIntegral_differentiable state).differentiableOn.analyticOnNhd isOpen_univ
  have accumulates : frequencyPoint left ∈ closure (frequencyPoint '' Ioo left right) := by
    apply image_closure_subset_closure_image (continuous_const.mul Complex.continuous_ofReal)
    refine ⟨left, ?_, rfl⟩
    rw [closure_Ioo width.ne]
    exact ⟨le_rfl, width.le⟩
  have isolatedRemoved : frequencyPoint left ∈
      closure ({w | exponentialIntegral state w = mean} \ {frequencyPoint left}) := by
    apply closure_mono _ accumulates
    rintro _ ⟨x, inside, rfl⟩
    exact ⟨(real_slice state x).trans (localRead ⟨inside.1.le, inside.2.le⟩),
      fun same => inside.1.ne' (frequency_point_injective same)⟩
  have all (x : ℝ) : burnolTruncatedFourierRaw state x = mean := by
    rw [← real_slice]
    exact analytic.eqOn_of_preconnected_of_mem_closure analyticOnNhd_const isPreconnected_univ
      (mem_univ _) isolatedRemoved (mem_univ _)
  have zero : mean = 0 := (all 0).symm.trans (centered_fourier_zero_head z)
  have erased : F (E state) = 0 := by
    apply Lp.ext
    filter_upwards [burnolFourierL2_zeroExtension_ae_eq_raw state, Lp.coeFn_zero ℂ 2 volume]
      with x read gone
    exact read.trans ((all x).trans (zero.trans gone.symm))
  have stored := congrArg burnolQuarterRestriction
    ((F).injective (erased.trans (map_zero (F)).symm))
  rw [burnolQuarterRestriction_zeroExtension, map_zero] at stored
  exact Subtype.ext stored

/-- A strictly wider actual position gap separates the two legs of the original outside column. -/
theorem physical_read_faithful_on_wider_gap (v : BurnolL2) {radius : ℝ} (wider : q < radius)
    (gap : v ∈ locallyConstantFace radius) (even : reflectL2 v = v) (erased : P v = 0) : v = 0 := by
  obtain ⟨mean, read⟩ := interval_read gap
  have quarter : v ∈ locallyConstantFace q := gap_restrict wider.le gap
  let z := burnolAmbientMeanZeroSecondCorrection v
  have balance := (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.starProjection_add_starProjection_orthogonal v
  change P v + O v = v at balance
  rw [erased, zero_add, outside_of_gap v even quarter, outsideEmbedding_read] at balance
  let left := (q+radius)/2
  have outsideLeft : q < left := by dsimp [left]; linarith
  have width : left < radius := by dsimp [left]; linarith
  have localAE : burnolTruncatedFourierRaw (z : BurnolQuarterIntervalL2) =ᵐ[
      volume.restrict (Icc left radius)] fun _ => mean := by
    apply (ae_restrict_iff' measurableSet_Icc).mpr
    filter_upwards [read, burnolQuarterZeroExtension_coe
      (burnolMeanZeroTruncatedFourier z : BurnolQuarterIntervalL2),
      burnolFourierL2_zeroExtension_ae_eq_raw (z : BurnolQuarterIntervalL2),
      Lp.coeFn_sub (F (E (z : BurnolQuarterIntervalL2)))
        (E (burnolMeanZeroTruncatedFourier z : BurnolQuarterIntervalL2))] with x readAt cut wave sub inside
    have beyond : x ∉ symmetricInterval q := fun inQ => (outsideLeft.trans_le inside.1).not_ge inQ.2
    have near : x ∈ symmetricInterval radius := by
      refine ⟨?_, inside.2⟩
      linarith [outsideLeft.trans_le inside.1, wider]
    have value := readAt near
    rw [← balance, sub] at value
    change F (E (z : BurnolQuarterIntervalL2)) x -
      E (burnolMeanZeroTruncatedFourier z : BurnolQuarterIntervalL2) x = mean at value
    rw [cut, indicator_of_notMem beyond, sub_zero, wave] at value
    exact value
  have localRead := Measure.eqOn_Icc_of_ae_eq (volume : Measure ℝ) width.ne localAE
    (burnolRadiusTruncatedFourierRaw_continuous _).continuousOn continuous_const.continuousOn
  have gone := constant_centered_fourier_on_interval z width mean localRead
  change F (E (z : BurnolQuarterIntervalL2)) -
    E (burnolMeanZeroTruncatedFourier z : BurnolQuarterIntervalL2) = v at balance
  rw [gone] at balance
  simpa only [Submodule.coe_zero, map_zero, sub_zero, eq_comm] using balance

/-- Every strictly inward clock makes the original physical projection faithful on the position-gap field. -/
theorem physical_inward_read_injective {v w : BurnolL2} (t : ℝ) (positive : 0 < t)
    (vgap : v ∈ locallyConstantFace q) (wgap : w ∈ locallyConstantFace q)
    (veven : reflectL2 v = v) (weven : reflectL2 w = w)
    (same : P (D (-t) v) = P (D (-t) w)) : v = w := by
  have wider : q < q * Real.exp (-(-t)) := by
    rw [neg_neg]
    exact lt_mul_of_one_lt_right (by norm_num) (Real.one_lt_exp_iff.mpr positive)
  have gap := burnolMultiplicativeDilation_mem_locallyConstantFace_scaled (-t)
    ((locallyConstantFace q).sub_mem vgap wgap)
  have even : reflectL2 (D (-t) (v-w)) = D (-t) (v-w) := by
    rw [reflectL2_burnolMultiplicativeDilation, map_sub, veven, weven]
  have erased : P (D (-t) (v-w)) = 0 := by rw [map_sub, map_sub, same, sub_self]
  have zero := physical_read_faithful_on_wider_gap _ wider gap even erased
  exact sub_eq_zero.mp ((D (-t)).injective (zero.trans (map_zero (D (-t))).symm))

end OriginalKFiniteOrderRelease.PositionGapCayley.PhysicalClock
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
