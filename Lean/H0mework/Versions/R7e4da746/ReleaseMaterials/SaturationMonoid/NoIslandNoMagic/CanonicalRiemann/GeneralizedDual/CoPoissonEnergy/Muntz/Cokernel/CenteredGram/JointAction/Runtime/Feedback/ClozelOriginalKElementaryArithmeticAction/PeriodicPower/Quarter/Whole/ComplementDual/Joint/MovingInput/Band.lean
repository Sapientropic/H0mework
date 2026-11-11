import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.MovingInput.Arithmetic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3400000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.MovingInput.Band
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszSource OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.MovingInput.Arithmetic OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Prime.KSourceEnergy
open scoped Topology InnerProductSpace
local notation "q" => (1/4 : ℝ)
local notation "order" => generatedRiemannXiZeroOrder ActualAnalyticOwner

def portWeight (c : BurnolCompletedMellinCoordinate) (j : ℕ) (x : ℝ) : ℂ :=
  (x : ℂ)^(-c.value) * (Real.log (x/q) : ℂ)^j

def lowerBand (c : BurnolCompletedMellinCoordinate) (h : ℝ) (j : ℕ) : ℂ :=
  ∫ t : ℝ in Icc q (q*Real.exp h),
    portWeight c j t * burnolRieszSingleFourierSourceRaw c (Real.exp (-h)*t)

def upperBand (c : BurnolCompletedMellinCoordinate) (h : ℝ) (j : ℕ) : ℂ :=
  ∫ t : ℝ in Icc (4*Real.exp (-h)) 4,
    portWeight c j t * (t : ℂ)⁻¹ * positionSource c ((Real.exp h*t)⁻¹)

def jointMoment (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) (h : ℝ) (j : ℕ) : ℂ :=
  ∫ t : ℝ in Icc q 4, portWeight c j t * jointInput c zero h t

private theorem weight_continuous (c : BurnolCompletedMellinCoordinate) (j : ℕ) :
    ContinuousOn (portWeight c j) (Icc q 4) := by
  have power : ContinuousOn (fun t : ℝ => (t : ℂ)^(-c.value)) (Icc q 4) := by
    intro t inside
    exact (continuousAt_ofReal_cpow_const t _ (Or.inr (by linarith [inside.1] : t ≠ 0))).continuousWithinAt
  have logarithm : ContinuousOn (fun t : ℝ => (Real.log (t/q) : ℂ)) (Icc q 4) :=
    Complex.continuous_ofReal.comp_continuousOn
      ((continuousOn_id.div_const q).log (fun t inside => div_ne_zero (by change t ≠ 0; linarith [inside.1]) (by norm_num)))
  exact power.mul (logarithm.pow j)

private theorem band_domains (c : BurnolCompletedMellinCoordinate) (h : ℝ) (j : ℕ) :
    IntegrableOn (fun t : ℝ => portWeight c j t * burnolRieszSingleFourierSourceRaw c (Real.exp (-h)*t)) (Icc q 4) ∧
    IntegrableOn (fun t : ℝ => portWeight c j t * (t : ℂ)⁻¹ * positionSource c ((Real.exp h*t)⁻¹)) (Icc q 4) := by
  have b : ContinuousOn (fun t : ℝ => burnolRieszSingleFourierSourceRaw c (Real.exp (-h)*t)) (Icc q 4) := by
    intro t inside
    have positive : 0 < t := by linarith [inside.1]
    exact ((burnolRieszSingleFourierSourceRaw_continuousAt c (mul_pos (Real.exp_pos _) positive).ne').comp
      (continuous_const.mul continuous_id).continuousAt).continuousWithinAt
  have inv : ContinuousOn (fun t : ℝ => (t : ℂ)⁻¹) (Icc q 4) :=
    Complex.continuous_ofReal.continuousOn.inv₀ (fun t inside => Complex.ofReal_ne_zero.mpr (by linarith [inside.1]))
  have p : ContinuousOn (fun t : ℝ => positionSource c ((Real.exp h*t)⁻¹)) (Icc q 4) := by
    intro t inside
    have positive : 0 < Real.exp h*t := mul_pos (Real.exp_pos _) (by linarith [inside.1])
    have inner : ContinuousAt (fun u : ℝ => (Real.exp h*u)⁻¹) t :=
      (continuousAt_const.mul continuousAt_id).inv₀ positive.ne'
    exact ((positionSource_continuousAt c (inv_pos.mpr positive)).comp
      (f := fun u : ℝ => (Real.exp h*u)⁻¹) inner).continuousWithinAt
  exact ⟨((weight_continuous c j).mul b).integrableOn_Icc,
    (((weight_continuous c j).mul inv).mul p).integrableOn_Icc⟩

/-- The full annulus moment is paid by its two actual finite counting bands, with both original feet. -/
theorem actual_joint_band_moment (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0)
    (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) (j : ℕ) :
    jointMoment c zero h j = -(Real.exp (-h/2) : ℂ)/2 * (lowerBand c h j + upperBand c h j) := by
  let l : ℝ → ℂ := fun t => portWeight c j t * burnolRieszSingleFourierSourceRaw c (Real.exp (-h)*t)
  let u : ℝ → ℂ := fun t => portWeight c j t * (t : ℂ)⁻¹ * positionSource c ((Real.exp h*t)⁻¹)
  have domains := band_domains c h j
  have lowDomain : IntegrableOn ((Iic (q*Real.exp h)).indicator l) (Icc q 4) :=
    domains.1.indicator measurableSet_Iic
  have highDomain : IntegrableOn ((Ici (4*Real.exp (-h))).indicator u) (Icc q 4) :=
    domains.2.indicator measurableSet_Ici
  have point : (fun t : ℝ => portWeight c j t * jointInput c zero h t) =ᵐ[volume.restrict (Icc q 4)]
      fun t => -(Real.exp (-h/2) : ℂ)/2 *
        (((Iic (q*Real.exp h)).indicator l) t + ((Ici (4*Real.exp (-h))).indicator u) t) := by
    filter_upwards [ae_restrict_of_ae (actual_joint_input_arithmetic_raw c zero h nonnegative bounded),
      ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae (volume.ae_ne q),
      ae_restrict_of_ae (volume.ae_ne (4 : ℝ))] with t raw inside notQuarter notFour
    rw [raw ⟨lt_of_le_of_ne inside.1 notQuarter.symm, lt_of_le_of_ne inside.2 notFour⟩]
    dsimp only [l,u]
    by_cases lower : t ≤ q*Real.exp h <;> by_cases upper : 4*Real.exp (-h) ≤ t <;>
      simp only [indicator_apply, mem_Iic, mem_Ici, lower, upper, ↓reduceIte] <;> ring
  rw [jointMoment, integral_congr_ae point, integral_const_mul,
    integral_add lowDomain highDomain, setIntegral_indicator measurableSet_Iic,
    setIntegral_indicator measurableSet_Ici]
  have leLow : q ≤ q*Real.exp h := le_mul_of_one_le_right (by norm_num) (Real.one_le_exp_iff.mpr nonnegative)
  have lowLe : q*Real.exp h ≤ 4 := by
    have boundExp := Real.exp_le_exp.mpr bounded
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at boundExp
    linarith
  have leHigh : q ≤ 4*Real.exp (-h) := by
    have boundExp := Real.exp_le_exp.mpr (neg_le_neg bounded)
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at boundExp
    norm_num at boundExp
    linarith
  have highLe : 4*Real.exp (-h) ≤ 4 := by
    have boundExp := Real.exp_le_one_iff.mpr (by linarith : -h ≤ 0)
    linarith
  have lowSet : Icc q 4 ∩ Iic (q*Real.exp h) = Icc q (q*Real.exp h) := by
    ext t
    simp only [mem_inter_iff, mem_Icc, mem_Iic]
    constructor
    · exact fun v => ⟨v.1.1,v.2⟩
    · exact fun v => ⟨⟨v.1,v.2.trans lowLe⟩,v.2⟩
  have highSet : Icc q 4 ∩ Ici (4*Real.exp (-h)) = Icc (4*Real.exp (-h)) 4 := by
    ext t
    simp only [mem_inter_iff, mem_Icc, mem_Ici]
    constructor
    · exact fun v => ⟨v.2,v.1.2⟩
    · exact fun v => ⟨⟨leHigh.trans v.1,v.2⟩,v.1⟩
  rw [lowSet, highSet]
  rfl

/-- This is the literal complete top port of the original Xi owner; no moment is assumed zero. -/
theorem actual_original_top_band_moment (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0)
    (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    (∫ t : ℝ in Icc q 4, (t : ℂ)^(-c.value) * (Real.log (t/q) : ℂ)^(order c.value-1) * jointInput c zero h t) =
      -(Real.exp (-h/2) : ℂ)/2 * (lowerBand c h (order c.value-1) + upperBand c h (order c.value-1)) :=
  actual_joint_band_moment c zero h nonnegative bounded (order c.value-1)

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.MovingInput.Band
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
