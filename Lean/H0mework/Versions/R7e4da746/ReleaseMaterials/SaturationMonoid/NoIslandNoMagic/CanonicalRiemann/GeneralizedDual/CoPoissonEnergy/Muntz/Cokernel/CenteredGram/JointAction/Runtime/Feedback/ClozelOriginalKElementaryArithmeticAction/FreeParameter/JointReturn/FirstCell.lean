import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.SourceWindow.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.JointReturn.CrossJet

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.FirstCell
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.FreeParameter.CountGeometry OriginalKElementaryArithmeticAction.FreeParameter.CountReturn
open OriginalKElementaryArithmeticAction.FreeParameter.UnitConsumer OriginalKElementaryArithmeticAction.FreeParameter.SourceWindow
open OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.Consumer
open OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.CrossContact OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.CrossJet
open scoped Topology InnerProductSpace
local notation "q" => (1/4 : ℝ)
local notation "Hq" => BurnolQuarterIntervalL2

theorem actual_count_first_cell (b : Hq) (x : ℝ) (after : q/2< |x|) (inside : |x|≤q) :
    countRaw b x=centeredRaw b x := by
  have positive : 0< |x| := by linarith
  have ordinal : ⌊q/|x|⌋₊=1 := by
    apply (Nat.floor_eq_iff (show 0≤q/|x| from div_nonneg (by norm_num) positive.le)).mpr
    constructor
    · rw [Nat.cast_one,le_div_iff₀ positive]
      simpa only [one_mul] using inside
    · norm_num
      rw [div_lt_iff₀ positive]
      linarith
  rw [countRaw,DualSourceRaw.channels,ordinal,Finset.Icc_self,Finset.sum_singleton,Nat.cast_one,one_mul]
  rcases le_total 0 x with nonnegative|nonpositive
  · rw [abs_of_nonneg nonnegative]
  · rw [abs_of_nonpos nonpositive,centeredRaw_even]

def bandReturnRaw (c : BurnolCompletedMellinCoordinate) (h : ℝ) (b : Hq) (x : ℝ) : ℂ :=
  if q*Real.exp (-h)< |x| ∧ |x|≤q then star (movedTest c h x)*centeredRaw b x else 0

private theorem return_integrand (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0≤h) (bounded : h≤Real.log 2) (b : Hq) :
    (fun x : ℝ=>inner ℂ (movedTest c h x) (countReader b x))=ᵐ[volume]bandReturnRaw c h b := by
  have half : q/2≤q*Real.exp (-h) := by
    have exponential : (1/2:ℝ)≤Real.exp (-h) := by
      calc
        (1/2:ℝ)=Real.exp (-Real.log 2) := by rw [Real.exp_neg,Real.exp_log (by norm_num)];norm_num
        _≤Real.exp (-h) := Real.exp_le_exp.mpr (neg_le_neg bounded)
    nlinarith
  filter_upwards [countReader_read b,actual_moved_gap c h nonnegative] with x read gap
  rw [RCLike.inner_apply,starRingEnd_apply,read]
  unfold bandReturnRaw
  by_cases outside : q< |x|
  · rw [countRaw_outside b x outside,zero_mul,if_neg (fun both=>not_lt_of_ge both.2 outside)]
  · have inside : |x|≤q := le_of_not_gt outside
    by_cases after : q*Real.exp (-h)< |x|
    · rw [if_pos ⟨after,inside⟩,actual_count_first_cell b x (half.trans_lt after) inside,mul_comm]
    · rw [if_neg (fun both=>after both.1),gap (le_of_not_gt after),star_zero,mul_zero]

theorem actual_band_return_integrable (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0≤h) (bounded : h≤Real.log 2) (b : Hq) : Integrable (bandReturnRaw c h b) :=
  (L2.integrable_inner (𝕜:=ℂ) (movedTest c h) (countReader b)).congr
    (return_integrand c h nonnegative bounded b)

theorem actual_count_return_price (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0≤h) (bounded : h≤Real.log 2) (b : Hq) :
    inner ℂ (movedTest c h) (countReader b)=∫ x : ℝ,bandReturnRaw c h b x := by
  rw [L2.inner_def]
  exact integral_congr_ae (return_integrand c h nonnegative bounded b)

/-- Both original contacts still consume the same B; its arithmetic return is now the actual n=1 band. -/
theorem actual_joint_B_first_cell (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0≤h) (bounded : h≤Real.log 2) (b : Hq) :
    jointBRead c h b=inner ℂ (burnolQuarterRestriction (fourierTest c h)) b-
      ∫ x : ℝ,bandReturnRaw c h b x := by
  change inner ℂ (burnolQuarterRestriction (fourierTest c h)) b-inner ℂ (movedTest c h) (countReader b)=_
  rw [actual_count_return_price c h nonnegative bounded b]

end OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.FirstCell
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
