import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Gamma.Coefficient
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.FinitePart

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Gamma.Whole
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Gamma.Coefficient OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.FinitePart
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Counting
open scoped Topology InnerProductSpace
open private bare_nonzero from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitMellin.XiConjugateOrderSource
local notation "order"=>generatedRiemannXiZeroOrder ActualAnalyticOwner
local notation "bare"=>generatedRiemannBareZeroLocalizedSpectrum ActualAnalyticOwner

/-- The same original Xi complement and the actual forcing Gamma head cancel their completion factors. -/
theorem actual_whole_leading_coefficient (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    (-1:ℂ)^(order c.value+1)*bare (1-star c.value) (1-star c.value)*
      ForcingPrimitive.leadingCoefficient c= -bare (star c.value) (star c.value)/2:=by
  let observation:=burnolPaZeroObservation c zero
  have complement:=generatedRiemannBareZeroLocalizedSpectrum_one_sub_at
    (conjugateZeroObservation observation)
    (observation.conjugate_nontrivial (burnolPaZeroObservation_nontrivial c zero))
  change bare (1-star c.value) (1-star c.value)=(-1:ℂ)^(order (star c.value))*
    (Gammaℝ (star c.value)/Gammaℝ (1-star c.value))*bare (star c.value) (star c.value) at complement
  rw [OriginalUnitXiConjugateOrderSource.actual_original_Xi_order_conjugate c] at complement
  have gamma:Gammaℝ (star c.value)≠0:=Gammaℝ_ne_zero_of_re_pos
    (by simp only [star_def,conj_re];linarith [c.rightHalf])
  have otherGamma:Gammaℝ (1-star c.value)≠0:=Gammaℝ_ne_zero_of_re_pos
    (by simp only [sub_re,one_re,star_def,conj_re];linarith [c.belowOne])
  have signs:(-1:ℂ)^(order c.value+1)*(-1:ℂ)^(order c.value)= -1:=by
    rw [pow_succ]
    calc
      _=((-1:ℂ)^(order c.value)*(-1:ℂ)^(order c.value))*(-1):=by ring
      _= -1:=by rw [←mul_pow];norm_num
  rw [complement,actual_forcing_gamma_coefficient c]
  calc
    _=((-1:ℂ)^(order c.value+1)*(-1:ℂ)^(order c.value))*
        bare (star c.value) (star c.value)/2:=by field_simp [gamma,otherGamma]
    _=_:=by rw [signs];ring

/-- This nonzero value is the actual m−1 quotient of the original Whole Fourier field. -/
theorem actual_whole_Xi_leading_limit (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    Tendsto (fun w:ℂ=>mellin (wholeCountedRaw c) w/(w-star c.value)^(order c.value-1))
      (𝓝[≠](star c.value)) (𝓝 (-bare (star c.value) (star c.value)/2)):=by
  have source:=actual_original_order_limit c zero
  rw [actual_whole_leading_coefficient c zero] at source
  exact source

theorem actual_whole_Xi_leading_nonzero (c:BurnolCompletedMellinCoordinate):
    -bare (star c.value) (star c.value)/2≠0:=by
  let conjugate:BurnolCompletedMellinCoordinate:=
    ⟨star c.value,by simpa only [star_def,conj_re] using c.rightHalf,
      by simpa only [star_def,conj_re] using c.belowOne⟩
  exact div_ne_zero (neg_ne_zero.mpr (bare_nonzero conjugate)) (by norm_num)

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Gamma.Whole
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
