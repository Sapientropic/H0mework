import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.TwoWindow.CommonInverse.Pairing
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.TwoWindow.CommonInverse.Response
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalCommonInverseForcing
open Complex MeasureTheory Set Filter OriginalRieszSource
open scoped Topology InnerProductSpace ENNReal
open OriginalTwoWindowInverseForcing
local notation "q" => (1/4:ℝ)

def edgeForceB (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  Kernel.A coordinate*Edge.raw q x+(star coordinate.value-1)*
    (Translator.ForcingMeanZero.mean coordinate+OriginalInverseReturnActionSource.returnMean coordinate)
def edgeForceP (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  -Kernel.beta coordinate*Edge.raw q x+
    star coordinate.value*(sourceMean coordinate-GapEuler.gapMean q coordinate)
def forcingInventoryRaw (coordinate : BurnolCompletedMellinCoordinate) (h x : ℝ) : ℂ :=
  star (edgeForceB coordinate (lowerScale h*x))*bLeg coordinate (h/2) x+
    star (bLeg coordinate (-h/2) x)*edgeForceB coordinate (upperScale h*x)-
    star (edgeForceP coordinate (lowerScale h*x))*pLeg coordinate (h/2) x-
    star (pLeg coordinate (-h/2) x)*edgeForceP coordinate (upperScale h*x)
def forcingInventory (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
  ∫ x:ℝ in (lowerRadius h)..(upperRadius h),forcingInventoryRaw coordinate h x

def inverseForcingRead (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
  (Real.exp (h/4):ℂ)*(star (Kernel.A coordinate)*inner ℂ Response.eta (inversePartner coordinate h).1-
    star (Kernel.beta coordinate)*inner ℂ Response.eta (inverseCotest coordinate h).1)+
  (Real.exp (-h/4):ℂ)*(Kernel.A coordinate*star (inner ℂ Response.eta (inversePartner coordinate h).2)-
    Kernel.beta coordinate*star (inner ℂ Response.eta (inverseCotest coordinate h).2))

private theorem interval_star (f : ℝ→ℂ) (a b : ℝ) :
    (∫ x:ℝ in a..b,star (f x))=star (∫ x:ℝ in a..b,f x) := by
  exact intervalIntegral.intervalIntegral_conj

private theorem fourier_b_integrable (state : BurnolQuarterMeanZeroCarrier)
    (coordinate : BurnolCompletedMellinCoordinate) (h scale leg : ℝ) :
    IntervalIntegrable (fun x:ℝ=>star (rawFourier state (Real.exp scale*x))*bLeg coordinate leg x)
      volume (lowerRadius h) (upperRadius h) := by
  have fourier : Continuous (fun x:ℝ=>rawFourier state (Real.exp scale*x)) :=
    (burnolRadiusTruncatedFourierRaw_continuous (state:BurnolQuarterIntervalL2)).comp (by fun_prop)
  exact (fourier.continuousOn.star.mul (bLeg_continuousOn coordinate h leg)).intervalIntegrable
private theorem fourier_p_integrable (state : BurnolQuarterMeanZeroCarrier)
    (coordinate : BurnolCompletedMellinCoordinate) (h scale leg : ℝ) :
    IntervalIntegrable (fun x:ℝ=>star (rawFourier state (Real.exp scale*x))*pLeg coordinate leg x)
      volume (lowerRadius h) (upperRadius h) := by
  have fourier : Continuous (fun x:ℝ=>rawFourier state (Real.exp scale*x)) :=
    (burnolRadiusTruncatedFourierRaw_continuous (state:BurnolQuarterIntervalL2)).comp (by fun_prop)
  exact (fourier.continuousOn.star.mul (pLeg_continuousOn coordinate h leg)).intervalIntegrable

private theorem reverse_b_read (state : BurnolQuarterMeanZeroCarrier)
    (coordinate : BurnolCompletedMellinCoordinate) (h scale leg : ℝ) :
    (∫ x:ℝ in (lowerRadius h)..(upperRadius h),
      star (bLeg coordinate leg x)*rawFourier state (Real.exp scale*x))=
      star (∫ x:ℝ in (lowerRadius h)..(upperRadius h),
        star (rawFourier state (Real.exp scale*x))*bLeg coordinate leg x) := by
  rw [← interval_star]
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  rw [star_mul,star_star]
private theorem reverse_p_read (state : BurnolQuarterMeanZeroCarrier)
    (coordinate : BurnolCompletedMellinCoordinate) (h scale leg : ℝ) :
    (∫ x:ℝ in (lowerRadius h)..(upperRadius h),
      star (pLeg coordinate leg x)*rawFourier state (Real.exp scale*x))=
      star (∫ x:ℝ in (lowerRadius h)..(upperRadius h),
        star (rawFourier state (Real.exp scale*x))*pLeg coordinate leg x) := by
  rw [← interval_star]
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  rw [star_mul,star_star]

private theorem forcingInventory_integrable (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) :
    IntervalIntegrable (forcingInventoryRaw coordinate h) volume (lowerRadius h) (upperRadius h) := by
  apply ContinuousOn.intervalIntegrable
  intro x inside
  have positive:=two_window_positive h x inside
  have bLower:=(b_hasDerivAt coordinate _ (mul_pos (Real.exp_pos _) positive)).continuousAt.comp
    (by fun_prop : ContinuousAt (fun y:ℝ=>lowerScale h*y) x)
  have bUpper:=(b_hasDerivAt coordinate _ (mul_pos (Real.exp_pos _) positive)).continuousAt.comp
    (by fun_prop : ContinuousAt (fun y:ℝ=>upperScale h*y) x)
  have pLower:=(p_hasDerivAt coordinate _ (mul_pos (Real.exp_pos _) positive)).continuousAt.comp
    (by fun_prop : ContinuousAt (fun y:ℝ=>lowerScale h*y) x)
  have pUpper:=(p_hasDerivAt coordinate _ (mul_pos (Real.exp_pos _) positive)).continuousAt.comp
    (by fun_prop : ContinuousAt (fun y:ℝ=>upperScale h*y) x)
  have edgeB : Continuous (edgeForceB coordinate) := by
    have edge:=Edge.raw_continuous q
    unfold edgeForceB
    fun_prop
  have edgeP : Continuous (edgeForceP coordinate) := by
    have edge:=Edge.raw_continuous q
    unfold edgeForceP
    fun_prop
  have eBLower:=edgeB.continuousAt.comp (by fun_prop : ContinuousAt (fun y:ℝ=>lowerScale h*y) x)
  have eBUpper:=edgeB.continuousAt.comp (by fun_prop : ContinuousAt (fun y:ℝ=>upperScale h*y) x)
  have ePLower:=edgeP.continuousAt.comp (by fun_prop : ContinuousAt (fun y:ℝ=>lowerScale h*y) x)
  have ePUpper:=edgeP.continuousAt.comp (by fun_prop : ContinuousAt (fun y:ℝ=>upperScale h*y) x)
  exact ((((eBLower.star.mul bUpper).add (bLower.star.mul eBUpper)).sub
    (ePLower.star.mul pUpper)).sub (pLower.star.mul ePUpper)).continuousWithinAt

private theorem forcingCross_expanded (coordinate : BurnolCompletedMellinCoordinate) (h x : ℝ) :
    forcingCross coordinate h x=
    (star (Kernel.A coordinate)*
      (star (rawFourier Response.v (Real.exp (-h/2)*x))*bLeg coordinate (h/2) x-
       star (rawFourier Response.u (Real.exp (-h/2)*x))*pLeg coordinate (h/2) x)-
     star (Kernel.beta coordinate)*
      (star (rawFourier Response.u (Real.exp (-h/2)*x))*bLeg coordinate (h/2) x-
       star (rawFourier Response.v (Real.exp (-h/2)*x))*pLeg coordinate (h/2) x))+
    (Kernel.A coordinate*
      (star (bLeg coordinate (-h/2) x)*rawFourier Response.v (Real.exp (h/2)*x)-
       star (pLeg coordinate (-h/2) x)*rawFourier Response.u (Real.exp (h/2)*x))-
     Kernel.beta coordinate*
      (star (bLeg coordinate (-h/2) x)*rawFourier Response.u (Real.exp (h/2)*x)-
       star (pLeg coordinate (-h/2) x)*rawFourier Response.v (Real.exp (h/2)*x)))+
    forcingInventoryRaw coordinate h x := by
  unfold forcingCross forceB forceP responseU responseV forcingInventoryRaw edgeForceB edgeForceP
    bLeg pLeg lowerScale upperScale
  simp only [star_add,star_sub,star_mul,star_neg]
  ring

theorem forcingCross_common_inverse (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0≤h) :
    (∫ x:ℝ in (lowerRadius h)..(upperRadius h),forcingCross coordinate h x)=
      inverseForcingRead coordinate h+forcingInventory coordinate h := by
  let f1:=fun x:ℝ=>star (rawFourier Response.v (Real.exp (-h/2)*x))*bLeg coordinate (h/2) x-
    star (rawFourier Response.u (Real.exp (-h/2)*x))*pLeg coordinate (h/2) x
  let f2:=fun x:ℝ=>star (rawFourier Response.u (Real.exp (-h/2)*x))*bLeg coordinate (h/2) x-
    star (rawFourier Response.v (Real.exp (-h/2)*x))*pLeg coordinate (h/2) x
  let f3:=fun x:ℝ=>star (bLeg coordinate (-h/2) x)*rawFourier Response.v (Real.exp (h/2)*x)-
    star (pLeg coordinate (-h/2) x)*rawFourier Response.u (Real.exp (h/2)*x)
  let f4:=fun x:ℝ=>star (bLeg coordinate (-h/2) x)*rawFourier Response.u (Real.exp (h/2)*x)-
    star (pLeg coordinate (-h/2) x)*rawFourier Response.v (Real.exp (h/2)*x)
  have i1:= (fourier_b_integrable Response.v coordinate h (-h/2) (h/2)).sub
    (fourier_p_integrable Response.u coordinate h (-h/2) (h/2))
  have i2:= (fourier_b_integrable Response.u coordinate h (-h/2) (h/2)).sub
    (fourier_p_integrable Response.v coordinate h (-h/2) (h/2))
  have reverse_b_integrable (state : BurnolQuarterMeanZeroCarrier) :
      IntervalIntegrable (fun x:ℝ=>star (bLeg coordinate (-h/2) x)*rawFourier state (Real.exp (h/2)*x))
        volume (lowerRadius h) (upperRadius h) := by
    have fourier : Continuous (fun x:ℝ=>rawFourier state (Real.exp (h/2)*x)) :=
      (burnolRadiusTruncatedFourierRaw_continuous (state:BurnolQuarterIntervalL2)).comp (by fun_prop)
    exact ((bLeg_continuousOn coordinate h (-h/2)).star.mul fourier.continuousOn).intervalIntegrable
  have reverse_p_integrable (state : BurnolQuarterMeanZeroCarrier) :
      IntervalIntegrable (fun x:ℝ=>star (pLeg coordinate (-h/2) x)*rawFourier state (Real.exp (h/2)*x))
        volume (lowerRadius h) (upperRadius h) := by
    have fourier : Continuous (fun x:ℝ=>rawFourier state (Real.exp (h/2)*x)) :=
      (burnolRadiusTruncatedFourierRaw_continuous (state:BurnolQuarterIntervalL2)).comp (by fun_prop)
    exact ((pLeg_continuousOn coordinate h (-h/2)).star.mul fourier.continuousOn).intervalIntegrable
  have i3:=(reverse_b_integrable Response.v).sub (reverse_p_integrable Response.u)
  have i4:=(reverse_b_integrable Response.u).sub (reverse_p_integrable Response.v)
  have split : (∫ x:ℝ in (lowerRadius h)..(upperRadius h),forcingCross coordinate h x)=
      (star (Kernel.A coordinate)*(∫ x:ℝ in (lowerRadius h)..(upperRadius h),f1 x)-
        star (Kernel.beta coordinate)*(∫ x:ℝ in (lowerRadius h)..(upperRadius h),f2 x))+
      (Kernel.A coordinate*(∫ x:ℝ in (lowerRadius h)..(upperRadius h),f3 x)-
        Kernel.beta coordinate*(∫ x:ℝ in (lowerRadius h)..(upperRadius h),f4 x))+
      forcingInventory coordinate h := by
    rw [intervalIntegral.integral_congr (fun x _=>forcingCross_expanded coordinate h x)]
    rw [intervalIntegral.integral_add
      (((i1.const_mul _).sub (i2.const_mul _)).add ((i3.const_mul _).sub (i4.const_mul _)))
      (forcingInventory_integrable coordinate h),
      intervalIntegral.integral_add ((i1.const_mul _).sub (i2.const_mul _)) ((i3.const_mul _).sub (i4.const_mul _)),
      intervalIntegral.integral_sub (i1.const_mul _) (i2.const_mul _),
      intervalIntegral.integral_sub (i3.const_mul _) (i4.const_mul _)]
    simp only [intervalIntegral.integral_const_mul,forcingInventory,f1,f2,f3,f4]
  have vbl:=band_cotest_read Response.v Response.v_reflection coordinate h (-h/2) (h/2) nonnegative
  have upl:=return_band_cotest_read Response.u Response.u_reflection coordinate h (-h/2) (h/2) nonnegative
  have ubl:=band_cotest_read Response.u Response.u_reflection coordinate h (-h/2) (h/2) nonnegative
  have vpl:=return_band_cotest_read Response.v Response.v_reflection coordinate h (-h/2) (h/2) nonnegative
  have vbu:=band_cotest_read Response.v Response.v_reflection coordinate h (h/2) (-h/2) nonnegative
  have upu:=return_band_cotest_read Response.u Response.u_reflection coordinate h (h/2) (-h/2) nonnegative
  have ubu:=band_cotest_read Response.u Response.u_reflection coordinate h (h/2) (-h/2) nonnegative
  have vpu:=return_band_cotest_read Response.v Response.v_reflection coordinate h (h/2) (-h/2) nonnegative
  rw [show -(-h/2)/2=h/4 by ring] at vbl upl ubl vpl
  rw [show -(h/2)/2=-h/4 by ring] at vbu upu ubu vpu
  have r1 : (∫ x:ℝ in (lowerRadius h)..(upperRadius h),f1 x)=
      (Real.exp (h/4):ℂ)*(inner ℂ Response.v (sourceColumns coordinate h).1.1-
        inner ℂ Response.u (sourceColumns coordinate h).1.2) := by
    rw [intervalIntegral.integral_sub
      (fourier_b_integrable Response.v coordinate h (-h/2) (h/2))
      (fourier_p_integrable Response.u coordinate h (-h/2) (h/2)),vbl,upl]
    unfold sourceColumns
    ring
  have r2 : (∫ x:ℝ in (lowerRadius h)..(upperRadius h),f2 x)=
      (Real.exp (h/4):ℂ)*(inner ℂ Response.u (sourceColumns coordinate h).1.1-
        inner ℂ Response.v (sourceColumns coordinate h).1.2) := by
    rw [intervalIntegral.integral_sub
      (fourier_b_integrable Response.u coordinate h (-h/2) (h/2))
      (fourier_p_integrable Response.v coordinate h (-h/2) (h/2)),ubl,vpl]
    unfold sourceColumns
    ring
  have r3 : (∫ x:ℝ in (lowerRadius h)..(upperRadius h),f3 x)=
      (Real.exp (-h/4):ℂ)*star (inner ℂ Response.v (sourceColumns coordinate h).2.1-
        inner ℂ Response.u (sourceColumns coordinate h).2.2) := by
    rw [intervalIntegral.integral_sub (reverse_b_integrable Response.v) (reverse_p_integrable Response.u),
      reverse_b_read,reverse_p_read,vbu,upu,star_mul,star_mul,
      show star (Real.exp (-h/4):ℂ)=(Real.exp (-h/4):ℂ) from Complex.conj_ofReal _]
    unfold sourceColumns
    rw [star_sub]
    ring
  have r4 : (∫ x:ℝ in (lowerRadius h)..(upperRadius h),f4 x)=
      (Real.exp (-h/4):ℂ)*star (inner ℂ Response.u (sourceColumns coordinate h).2.1-
        inner ℂ Response.v (sourceColumns coordinate h).2.2) := by
    rw [intervalIntegral.integral_sub (reverse_b_integrable Response.u) (reverse_p_integrable Response.v),
      reverse_b_read,reverse_p_read,ubu,vpu,star_mul,star_mul,
      show star (Real.exp (-h/4):ℂ)=(Real.exp (-h/4):ℂ) from Complex.conj_ofReal _]
    unfold sourceColumns
    rw [star_sub]
    ring
  obtain ⟨lowerU,lowerV,upperU,upperV⟩:=actual_response_inverse_read coordinate h
  rw [split,r1,r2,r3,r4,lowerU,lowerV,upperU,upperV]
  unfold inverseForcingRead
  ring

end OriginalCommonInverseForcing
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
