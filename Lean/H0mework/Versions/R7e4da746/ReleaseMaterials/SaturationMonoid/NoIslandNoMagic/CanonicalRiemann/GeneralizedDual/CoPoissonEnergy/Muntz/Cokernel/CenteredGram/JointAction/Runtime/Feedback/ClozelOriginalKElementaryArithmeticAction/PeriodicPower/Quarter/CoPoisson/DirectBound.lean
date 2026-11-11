import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Poisson.Constant

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.DirectBound
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Resolved OriginalKElementaryArithmeticAction.PeriodicPower.Alias.Continuous
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Consumer
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Compact OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Poisson.Mass OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Poisson.Constant
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Source
open scoped Topology ENNReal InnerProductSpace FourierTransform
open private character_read from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Source
local notation "q" => (1/4:ℝ)

/-- The original zero observation pays the actual continuous head of the same H_h. -/
theorem actual_positive_origin (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nonnegative:0≤h) : positiveRaw c h 0=0 := by
  have radius : (0:ℝ) ≤ innerRadius h := by unfold innerRadius;positivity
  have selected : riemannZeta (star c.value)=0 := by
    simpa only [star_def,zero,map_zero] using riemannZeta_conj c.value
  rw [positiveRaw,if_pos radius,innerRaw,actual_compact_fourier_zero c h nonnegative]
  unfold regularClockRaw
  rw [mul_zero,actual_alias_origin_constant,selected,add_zero,character_read]
  ring

/-- A representative with its source-generated continuous zero at the singleton. -/
def directRaw (c:BurnolCompletedMellinCoordinate) (h x:ℝ) : ℂ :=
  if x=0 then 0 else differenceRaw c h x

theorem actual_direct_nonzero (c:BurnolCompletedMellinCoordinate) (h x:ℝ) (nonzero:x≠0) :
    directRaw c h x=differenceRaw c h x := if_neg nonzero

theorem actual_direct_origin (c:BurnolCompletedMellinCoordinate) (h:ℝ) : directRaw c h 0=0 := by
  simp [directRaw]

private theorem difference_even (c:BurnolCompletedMellinCoordinate) (h x:ℝ) :
    differenceRaw c h (-x)=differenceRaw c h x := by
  unfold differenceRaw
  rw [mul_neg,actual_quarter_even,actual_quarter_even]

theorem actual_direct_even (c:BurnolCompletedMellinCoordinate) (h x:ℝ) :
    directRaw c h (-x)=directRaw c h x := by
  simp only [directRaw,neg_eq_zero,difference_even]

theorem actual_direct_measurable (c:BurnolCompletedMellinCoordinate) (h:ℝ) :
    Measurable (directRaw c h) := by
  have source : Measurable (differenceRaw c h) :=
    (measurable_const.mul ((actual_quarter_measurable c).comp
      (measurable_const.mul measurable_id))).sub (measurable_const.mul (actual_quarter_measurable c))
  exact Measurable.ite (measurableSet_singleton 0) measurable_const source

theorem actual_direct_raw (c:BurnolCompletedMellinCoordinate) (h:ℝ) :
    (waveDifference c h:ℝ→ℂ)=ᵐ[volume]directRaw c h := by
  apply (actual_difference_raw c h).trans
  have avoid : ∀ᵐx:ℝ∂volume,x≠0 := by simp [ae_iff,measure_singleton]
  filter_upwards [avoid] with x nonzero
  exact (actual_direct_nonzero c h x nonzero).symm

theorem actual_direct_outer_zero (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nonnegative:0≤h) (x:ℝ) (outside:q≤|x|) : directRaw c h x=0 := by
  have nonzero : x≠0 := abs_pos.mp (lt_of_lt_of_le (by norm_num : (0:ℝ)<q) outside)
  rw [actual_direct_nonzero c h x nonzero]
  exact actual_difference_outer_zero c zero h nonnegative x outside

/-- This global linear bound is generated from the same original zero and wave source. -/
theorem actual_direct_bound (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nonnegative:0≤h) :
    ∃ B:ℝ, 0≤B ∧ ∀ x:ℝ, ‖directRaw c h x‖≤B*|x| := by
  obtain ⟨B,lip⟩ := actual_positive_lipschitz c zero h nonnegative
  refine ⟨B,B.coe_nonneg,?_⟩
  intro x
  by_cases atZero:x=0
  · subst x
    rw [actual_direct_origin,norm_zero,abs_zero,mul_zero]
  · by_cases inside:|x|≤q
    · have positive : 0 < |x| := abs_pos.mpr atZero
      have bound := (lipschitzOnWith_iff_norm_sub_le.mp lip)
        (show |x|∈Icc 0 q from ⟨positive.le,inside⟩) (by norm_num : (0:ℝ)∈Icc 0 q)
      rw [actual_positive_origin c zero h nonnegative,sub_zero,sub_zero,Real.norm_eq_abs,abs_abs] at bound
      rw [actual_positive_raw c h nonnegative |x| positive inside] at bound
      rw [actual_direct_nonzero c h x atZero]
      rcases le_total 0 x with positiveX|negativeX
      · simpa only [abs_of_nonneg positiveX] using bound
      · simpa only [abs_of_nonpos negativeX,difference_even] using bound
    · rw [actual_direct_outer_zero c zero h nonnegative x (lt_of_not_ge inside).le,norm_zero]
      exact mul_nonneg B.coe_nonneg (abs_nonneg x)

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.DirectBound
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
