import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Mellin
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Muntz.Original

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.MellinValue
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Landing OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Whole
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.ReciprocalMean.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Clock
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Muntz.Original OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Counting OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Mellin
open scoped Topology InnerProductSpace
open private actual_dilation_mellin actual_smul_mellin source_ae from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitMellin.UnitSource

theorem actual_fourier_whole_clock (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (positive : 0<h) :
    burnolMultiplicativeDilation (-h) (fourierL2 (wholeValue c zero h positive))-
      Complex.exp ((star c.value-1/2)*(h:ℂ)) • fourierL2 (wholeValue c zero h positive)=
        countedValue c zero h positive.le := by
  have source:=congrArg fourierL2 (actual_whole_clock c zero h positive)
  simpa only [map_sub,map_smul,fourierL2_burnolMultiplicativeDilation,fourierL2_fourierL2,actual_counted_even] using source

theorem actual_whole_clock_mellin (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (positiveH : 0<h) (w : ℂ) (positive : 0<w.re) (below : w.re<1) :
    (Complex.exp ((w-1/2)*(h:ℂ))-Complex.exp ((star c.value-1/2)*(h:ℂ)))*
      mellin (wholeCountedRaw c) w=riemannZeta (1-w)*mellin (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.DirectBound.directRaw c h) (1-w) := by
  let value:=fourierL2 (wholeValue c zero h positiveH)
  let M:=mellin (wholeCountedRaw c) w
  have original:HasMellin (value:ℝ→ℂ) w M:=actual_fourier_whole_mellin c zero h positiveH w positive below
  have original':HasMellin (value:ℝ→ℂ) (1-(1-w)) M:=by simpa only [sub_sub_cancel] using original
  have shifted:=actual_dilation_mellin value (1-w) M (-h) original'
  have exponent:((1-w)-1/2)*((-h:ℝ):ℂ)=(w-1/2)*(h:ℂ) := by push_cast;ring
  simp only [sub_sub_cancel,exponent] at shifted
  have scaled:=actual_smul_mellin value w M (Complex.exp ((star c.value-1/2)*(h:ℂ))) original
  have difference:=hasMellin_sub shifted.1 scaled.1
  rw [shifted.2,scaled.2] at difference
  have raw:HasMellin (countedValue c zero h positiveH.le:ℝ→ℂ) w
      ((Complex.exp ((w-1/2)*(h:ℂ))-Complex.exp ((star c.value-1/2)*(h:ℂ)))*M) := by
    rw [←actual_fourier_whole_clock c zero h positiveH]
    have generated:=source_ae _ _ _ _ (ae_restrict_of_ae (Lp.coeFn_sub
      (burnolMultiplicativeDilation (-h) value) (Complex.exp ((star c.value-1/2)*(h:ℂ)) • value))) difference
    simpa only [sub_mul] using generated
  have actual:HasMellin (countedRaw c h) w
      ((Complex.exp ((w-1/2)*(h:ℂ))-Complex.exp ((star c.value-1/2)*(h:ℂ)))*M) :=
    source_ae _ _ _ _ (ae_restrict_of_ae (actual_counted_raw c zero h positiveH.le).symm) raw
  rw [←actual.2,actual_native_counted_mellin c zero h positiveH.le w positive below]

private theorem clock_separates (c : BurnolCompletedMellinCoordinate) (w : ℂ) (apart : w≠star c.value) :
    ∃h:ℝ,0<h ∧ Complex.exp ((w-1/2)*(h:ℂ))-Complex.exp ((star c.value-1/2)*(h:ℂ))≠0 := by
  let h:ℝ:=Real.pi/(1+|(w-star c.value).im|)
  have denominator:0<1+|(w-star c.value).im|:=by positivity
  have positive:0<h:=div_pos Real.pi_pos denominator
  refine ⟨h,positive,?_⟩
  intro equality
  have exponential:=Complex.exp_eq_exp_iff_exp_sub_eq_one.mp (sub_eq_zero.mp equality)
  have exponent:(w-1/2)*(h:ℂ)-(star c.value-1/2)*(h:ℂ)=(w-star c.value)*(h:ℂ):=by ring
  rw [exponent] at exponential
  have small:|((w-star c.value)*(h:ℂ)).im|<Real.pi := by
    simp only [mul_im,ofReal_im,mul_zero,ofReal_re,zero_add,abs_mul,abs_of_pos positive]
    change |(w-star c.value).im| * (Real.pi/(1+|(w-star c.value).im|))<Real.pi
    rw [←mul_div_assoc,div_lt_iff₀ denominator]
    nlinarith [Real.pi_pos]
  have equalZero:(w-star c.value)*(h:ℂ)=0 :=
    Complex.exp_inj_of_neg_pi_lt_of_le_pi (abs_lt.mp small).1
      (abs_lt.mp small).2.le (by simpa using neg_neg_of_pos Real.pi_pos)
      (by simpa using Real.pi_pos.le) (by simpa only [Complex.exp_zero] using exponential)
  exact (mul_ne_zero (sub_ne_zero.mpr apart) (Complex.ofReal_ne_zero.mpr positive.ne')) equalZero

/-- The whole field is read first; only then is a nonzero actual clock cancelled. -/
theorem actual_whole_mellin_value (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (w : ℂ) (positive : 0<w.re) (below : w.re<1) (apart : w≠star c.value) :
    mellin (wholeCountedRaw c) w=
      riemannZeta (1-w)*mellin (companionWholeRaw c) (1-w)/(w-star c.value) := by
  obtain ⟨h,positiveH,separates⟩:=clock_separates c w apart
  have source:=actual_whole_clock_mellin c zero h positiveH w positive below
  have nonresonant:1-w≠1-star c.value := by intro same;apply apart;linear_combination -same
  have clock:=actual_nonresonant_mellin c zero h positiveH.le (1-w)
    (by simp only [sub_re,one_re];linarith) nonresonant
  rw [clock.2,show 1/2-(1-w)=w-1/2 by ring,show 1-star c.value-(1-w)=w-star c.value by ring] at source
  apply (mul_left_cancel₀ separates)
  calc
    _=riemannZeta (1-w)*
      ((Complex.exp ((w-1/2)*(h:ℂ))-Complex.exp ((star c.value-1/2)*(h:ℂ))))/
        (w-star c.value)*mellin (companionWholeRaw c) (1-w) := by linear_combination source
    _=_ := by ring

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.MellinValue
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
