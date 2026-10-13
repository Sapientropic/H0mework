import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.TwoWindow.CommonInverse.Annulus
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalCommonInverseForcing
open Complex MeasureTheory Set Filter OriginalRieszSource OriginalPaPhysicalGreen FixedWindowFourierReaction
open scoped Topology InnerProductSpace ENNReal
open OriginalTwoWindowInverseForcing
local notation "q" => (1/4:ℝ)
local notation "T" => burnolRechartedTruncatedFourierOperator
local notation "S" => burnolMeanZeroTruncatedFourier

def firstFoot (radius scale : ℝ) : ℝ := Real.sqrt (radius*q)*Real.exp (-scale/2)
def secondFoot (radius scale : ℝ) : ℝ := Real.sqrt (q*radius)*Real.exp (scale/2)

private theorem cut_sandwich_chart (state : BurnolQuarterMeanZeroCarrier)
    (radius firstScale secondScale : ℝ) (positive : 0<radius) :
    quarterChart (burnolQuarterRestriction (fourierL2 (burnolMultiplicativeDilation firstScale
      (originalPhysicalCutoff radius (burnolMultiplicativeDilation secondScale (fourierL2 (whole state)))))))=
      T (firstFoot radius firstScale)
        (T (secondFoot radius secondScale) (quarterChart (state:BurnolQuarterIntervalL2))) := by
  have factored : quarterChart (burnolQuarterRestriction (fourierL2 (burnolMultiplicativeDilation firstScale
      (originalPhysicalCutoff radius (burnolMultiplicativeDilation secondScale (fourierL2 (whole state)))))))=
      burnolFixedWindowFourierDilation positive (by norm_num : 0<q) firstScale
        (burnolFixedWindowDilationFourier (by norm_num : 0<q) positive secondScale
          (quarterChart (state:BurnolQuarterIntervalL2))) := by
    unfold originalPhysicalCutoff burnolFixedWindowFourierDilation burnolFixedWindowDilationFourier
      burnolUnitWindowEmbedding whole quarterChart
    simp only [ContinuousLinearMap.comp_apply,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousLinearEquiv.coe_coe,LinearIsometryEquiv.symm_apply_apply]
    rfl
  rw [factored,burnolFixedWindowFourierDilation_eq_radius,burnolFixedWindowDilationFourier_eq_radius]
  unfold firstFoot secondFoot
  rw [burnolRechartedTruncatedFourierOperator_of_pos
    (mul_pos (Real.sqrt_pos.mpr (mul_pos positive (by norm_num : 0<q))) (Real.exp_pos (-firstScale/2))),
    burnolRechartedTruncatedFourierOperator_of_pos
      (mul_pos (Real.sqrt_pos.mpr (mul_pos (by norm_num : 0<q) positive)) (Real.exp_pos (secondScale/2)))]

private theorem radius_root (h : ℝ) : Real.sqrt (FixedWindowFourierReaction.actualRadius h*q)=q*Real.exp (h/4) := by
  unfold FixedWindowFourierReaction.actualRadius
  rw [show q*Real.exp (h/2)*q=q^2*Real.exp (h/2) by ring,
    Real.sqrt_mul (by positivity : 0≤q^2),Real.sqrt_sq (by norm_num : 0≤q),← Real.exp_half]
  congr 1
  ring

theorem actual_window_feet (h : ℝ) :
    firstFoot (upperRadius h) (h/2)=q ∧ secondFoot (upperRadius h) (h/2)=upperRadius h ∧
    firstFoot (lowerRadius h) (h/2)=lowerRadius h ∧ secondFoot (lowerRadius h) (h/2)=q ∧
    firstFoot (upperRadius h) (-h/2)=upperRadius h ∧ secondFoot (upperRadius h) (-h/2)=q ∧
    firstFoot (lowerRadius h) (-h/2)=q ∧ secondFoot (lowerRadius h) (-h/2)=lowerRadius h := by
  have rootRight (t : ℝ) : Real.sqrt (q*FixedWindowFourierReaction.actualRadius t)=q*Real.exp (t/4) := by
    rw [mul_comm q,radius_root]
  unfold firstFoot secondFoot lowerRadius upperRadius
  simp only [radius_root,rootRight]
  unfold FixedWindowFourierReaction.actualRadius
  constructor
  · rw [mul_assoc,← Real.exp_add,show h/4+-(h/2)/2=0 by ring,Real.exp_zero,mul_one]
  constructor
  · rw [mul_assoc,← Real.exp_add,show h/4+(h/2)/2=h/2 by ring]
  constructor
  · rw [mul_assoc,← Real.exp_add,show -h/4+-(h/2)/2=-h/2 by ring]
  constructor
  · rw [mul_assoc,← Real.exp_add,show -h/4+(h/2)/2=0 by ring,Real.exp_zero,mul_one]
  constructor
  · rw [mul_assoc,← Real.exp_add,show h/4+-(-h/2)/2=h/2 by ring]
  constructor
  · rw [mul_assoc,← Real.exp_add,show h/4+(-h/2)/2=0 by ring,Real.exp_zero,mul_one]
  constructor
  · rw [mul_assoc,← Real.exp_add,show -h/4+-(-h/2)/2=0 by ring,Real.exp_zero,mul_one]
  · rw [mul_assoc,← Real.exp_add,show -h/4+(-h/2)/2=-h/2 by ring]


theorem source_window_kernel_lower (state : BurnolQuarterMeanZeroCarrier) (h : ℝ) :
    quarterChart (windowKernelColumn state h (-h/2) (h/2):BurnolQuarterIntervalL2)=
      Q (T q (T (upperRadius h) (quarterChart (state:BurnolQuarterIntervalL2)))-
        T (lowerRadius h) (T q (quarterChart (state:BurnolQuarterIntervalL2)))) := by
  unfold windowKernelColumn Constructor.zeroMean
  change quarterChart (burnolQuarterMeanZeroProjection _)=_
  rw [quarter_projection_chart]
  have lowerPositive : 0<lowerRadius h := by unfold lowerRadius FixedWindowFourierReaction.actualRadius; positivity
  have upperPositive : 0<upperRadius h := by unfold upperRadius FixedWindowFourierReaction.actualRadius; positivity
  obtain ⟨fUp,sUp,fLo,sLo,_,_,_,_⟩:=actual_window_feet h
  simp only [map_sub]
  rw [cut_sandwich_chart state (upperRadius h) (-(-h/2)) (h/2) upperPositive,
    cut_sandwich_chart state (lowerRadius h) (-(-h/2)) (h/2) lowerPositive]
  rw [show -(-h/2)=h/2 by ring,fUp,sUp,fLo,sLo]

theorem source_window_kernel_upper (state : BurnolQuarterMeanZeroCarrier) (h : ℝ) :
    quarterChart (windowKernelColumn state h (h/2) (-h/2):BurnolQuarterIntervalL2)=
      Q (T (upperRadius h) (T q (quarterChart (state:BurnolQuarterIntervalL2)))-
        T q (T (lowerRadius h) (quarterChart (state:BurnolQuarterIntervalL2)))) := by
  unfold windowKernelColumn Constructor.zeroMean
  change quarterChart (burnolQuarterMeanZeroProjection _)=_
  rw [quarter_projection_chart]
  have lowerPositive : 0<lowerRadius h := by unfold lowerRadius FixedWindowFourierReaction.actualRadius; positivity
  have upperPositive : 0<upperRadius h := by unfold upperRadius FixedWindowFourierReaction.actualRadius; positivity
  obtain ⟨_,_,_,_,fUp,sUp,fLo,sLo⟩:=actual_window_feet h
  simp only [map_sub]
  rw [cut_sandwich_chart state (upperRadius h) (-(h/2)) (-h/2) upperPositive,
    cut_sandwich_chart state (lowerRadius h) (-(h/2)) (-h/2) lowerPositive]
  rw [show -(h/2)=-h/2 by ring,fUp,sUp,fLo,sLo]

end OriginalCommonInverseForcing
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
