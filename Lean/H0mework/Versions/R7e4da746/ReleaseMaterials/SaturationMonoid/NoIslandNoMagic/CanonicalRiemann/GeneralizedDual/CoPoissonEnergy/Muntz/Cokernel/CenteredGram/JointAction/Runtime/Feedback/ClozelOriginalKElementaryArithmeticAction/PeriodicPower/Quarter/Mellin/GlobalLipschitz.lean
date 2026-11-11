import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.DirectBound

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.GlobalLipschitz
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.DirectBound
open scoped Topology ENNReal
local notation "q" => (1/4:ℝ)

private theorem difference_even (c:BurnolCompletedMellinCoordinate) (h x:ℝ) :
    differenceRaw c h (-x)=differenceRaw c h x := by
  unfold differenceRaw
  rw [mul_neg,actual_quarter_even,actual_quarter_even]

theorem actual_clipped_raw (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nonnegative:0≤h) (x:ℝ) :
    directRaw c h x=positiveRaw c h (min |x| q) := by
  by_cases origin:x=0
  · subst x
    rw [actual_direct_origin,abs_zero,min_eq_left (by norm_num : (0:ℝ)≤q),
      actual_positive_origin c zero h nonnegative]
  by_cases inside:|x|≤q
  · rw [min_eq_left inside,actual_direct_nonzero c h x origin,
      actual_positive_raw c h nonnegative |x| (abs_pos.mpr origin) inside]
    rcases le_total 0 x with positive|negative
    · rw [abs_of_nonneg positive]
    · rw [abs_of_nonpos negative,difference_even]
  · rw [min_eq_right (le_of_not_ge inside),actual_direct_outer_zero c zero h nonnegative x
      (le_of_not_ge inside),actual_positive_endpoint c zero h nonnegative]

/-- The original two endpoint zeros extend the actual quarter modulus to the whole source. -/
theorem actual_direct_global_lipschitz (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (h:ℝ) (nonnegative:0≤h) :
    ∃ L:NNReal,LipschitzWith L (directRaw c h) := by
  obtain ⟨L,source⟩:=actual_positive_lipschitz c zero h nonnegative
  have clip:LipschitzWith 1 (fun x:ℝ=>min |x| q) := by
    simpa only [Real.dist_eq,sub_zero] using (LipschitzWith.dist_left (0:ℝ)).min_const q
  have clipped (x:ℝ) : min |x| q∈Icc 0 q :=
    ⟨le_min (abs_nonneg x) (by norm_num),min_le_right _ _⟩
  refine ⟨L,lipschitzWith_iff_dist_le_mul.mpr ?_⟩
  intro x y
  rw [actual_clipped_raw c zero h nonnegative x,actual_clipped_raw c zero h nonnegative y]
  calc
    _≤(L:ℝ)*dist (min |x| q) (min |y| q) := source.dist_le_mul (min |x| q) (clipped x) (min |y| q) (clipped y)
    _≤(L:ℝ)*(1*dist x y) := mul_le_mul_of_nonneg_left (clip.dist_le_mul x y) L.coe_nonneg
    _=_ := by rw [one_mul]

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.GlobalLipschitz
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
