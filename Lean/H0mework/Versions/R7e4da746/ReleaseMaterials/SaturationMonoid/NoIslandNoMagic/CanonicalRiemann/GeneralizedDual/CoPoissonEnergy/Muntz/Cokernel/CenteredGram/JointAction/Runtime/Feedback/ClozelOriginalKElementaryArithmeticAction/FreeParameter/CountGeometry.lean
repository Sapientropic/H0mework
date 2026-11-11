import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.Inverse
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.FreeParameter.CountGeometry
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson.Ward
open scoped InnerProductSpace Topology FourierTransform
local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "μq" => (volume.restrict (symmetricInterval q))

def symFourier (b:Hq) (x:ℝ) : ℂ :=
 (burnolRadiusTruncatedFourierRaw q b x+burnolRadiusTruncatedFourierRaw q b (-x))/2

theorem symFourier_continuous (b:Hq) : Continuous (symFourier b) := by
 unfold symFourier
 exact ((burnolRadiusTruncatedFourierRaw_continuous b).add
  ((burnolRadiusTruncatedFourierRaw_continuous b).comp continuous_neg)).div_const 2

theorem symFourier_even (b:Hq) (x:ℝ) : symFourier b (-x)=symFourier b x := by
 simp only [symFourier,neg_neg];ring

theorem symFourier_add (a b:Hq) (x:ℝ) : symFourier (a+b) x=symFourier a x+symFourier b x := by
 simp only [symFourier,burnolRadiusTruncatedFourierRaw_add,Pi.add_apply];ring

theorem symFourier_smul (z:ℂ) (b:Hq) (x:ℝ) : symFourier (z•b) x=z*symFourier b x := by
 simp only [symFourier,burnolRadiusTruncatedFourierRaw_smul,Pi.smul_apply,smul_eq_mul];ring

theorem symFourier_bound (b:Hq) (x:ℝ) : ‖symFourier b x‖≤Real.sqrt (2*q)*‖b‖ := by
 rw [symFourier,norm_div,norm_ofNat]
 apply (div_le_iff₀ (by norm_num:(0:ℝ)<2)).mpr
 exact (norm_add_le _ _).trans ((add_le_add
  (burnolRadiusTruncatedFourierRaw_norm_le (by norm_num:(0:ℝ)<q) b x)
  (burnolRadiusTruncatedFourierRaw_norm_le (by norm_num:(0:ℝ)<q) b (-x))).trans_eq (by ring))

def halfMean (b:Hq) : ℂ := (q:ℂ)⁻¹*(∫x:ℝ in (0:ℝ)..q,symFourier b x)
def centeredRaw (b:Hq) (x:ℝ) : ℂ := symFourier b x-halfMean b

theorem centeredRaw_continuous (b:Hq) : Continuous (centeredRaw b) :=
 (symFourier_continuous b).sub continuous_const

theorem centeredRaw_even (b:Hq) (x:ℝ) : centeredRaw b (-x)=centeredRaw b x := by
 rw [centeredRaw,centeredRaw,symFourier_even]

theorem halfMean_add (a b:Hq) : halfMean (a+b)=halfMean a+halfMean b := by
 unfold halfMean
 simp_rw [symFourier_add]
 rw [intervalIntegral.integral_add ((symFourier_continuous a).intervalIntegrable _ _)
  ((symFourier_continuous b).intervalIntegrable _ _)]
 ring

theorem halfMean_smul (z:ℂ) (b:Hq) : halfMean (z•b)=z*halfMean b := by
 unfold halfMean
 simp_rw [symFourier_smul]
 rw [intervalIntegral.integral_const_mul]
 ring

theorem centeredRaw_add (a b:Hq) (x:ℝ) : centeredRaw (a+b) x=centeredRaw a x+centeredRaw b x := by
 rw [centeredRaw,centeredRaw,centeredRaw,symFourier_add,halfMean_add];ring

theorem centeredRaw_smul (z:ℂ) (b:Hq) (x:ℝ) : centeredRaw (z•b) x=z*centeredRaw b x := by
 rw [centeredRaw,centeredRaw,symFourier_smul,halfMean_smul];ring

theorem centeredRaw_half_zero (b:Hq) : (∫x:ℝ in (0:ℝ)..q,centeredRaw b x)=0 := by
 unfold centeredRaw
 rw [intervalIntegral.integral_sub ((symFourier_continuous b).intervalIntegrable _ _) intervalIntegrable_const,
  intervalIntegral.integral_const]
 simp only [sub_zero,Complex.real_smul,halfMean]
 norm_num
 ring

theorem halfMean_bound (b:Hq) : ‖halfMean b‖≤Real.sqrt (2*q)*‖b‖ := by
 have bounded:=intervalIntegral.norm_integral_le_of_norm_le_const (a:=0) (b:=q)
  (C:=Real.sqrt (2*q)*‖b‖) (f:=symFourier b) (fun x _=>symFourier_bound b x)
 rw [halfMean,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs]
 norm_num at bounded ⊢
 linarith

theorem centeredRaw_bound (b:Hq) (x:ℝ) : ‖centeredRaw b x‖≤2*Real.sqrt (2*q)*‖b‖ :=
 (norm_sub_le _ _).trans ((add_le_add (symFourier_bound b x) (halfMean_bound b)).trans_eq (by ring))

end OriginalKElementaryArithmeticAction.FreeParameter.CountGeometry
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
