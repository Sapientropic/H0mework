import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.CountGeometry
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.FourierBounds
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.FreeParameter.CountLipschitz
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalKElementaryArithmeticAction.FreeParameter.CountGeometry
open scoped InnerProductSpace Topology FourierTransform
local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "μq" => (volume.restrict (symmetricInterval q))
local instance : IsFiniteMeasure μq where
 measure_univ_lt_top:=lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top q)

theorem raw_lipschitz (b:Hq) (x y:ℝ) :
 ‖burnolRadiusTruncatedFourierRaw q b y-burnolRadiusTruncatedFourierRaw q b x‖≤
  (2*Real.pi*q*Real.sqrt (2*q)*‖b‖)*‖y-x‖ :=
 OriginalKElementaryArithmeticAction.FreeParameter.FourierBounds.actual_fourier_lipschitz b x y

theorem symFourier_lipschitz (b:Hq) (x y:ℝ) :
 ‖symFourier b y-symFourier b x‖≤(2*Real.pi*q*Real.sqrt (2*q)*‖b‖)*‖y-x‖ := by
 have regular:=raw_lipschitz b x y
 have reflected:=raw_lipschitz b (-x) (-y)
 have distance:‖-y- -x‖=‖y-x‖:=by rw [neg_sub_neg];exact norm_sub_rev _ _
 rw [distance] at reflected
 have decomposition:symFourier b y-symFourier b x=
  ((burnolRadiusTruncatedFourierRaw q b y-burnolRadiusTruncatedFourierRaw q b x)+
  (burnolRadiusTruncatedFourierRaw q b (-y)-burnolRadiusTruncatedFourierRaw q b (-x)))/2:=by
  unfold symFourier;ring
 rw [decomposition,norm_div,norm_ofNat]
 apply (div_le_iff₀ (by norm_num:(0:ℝ)<2)).mpr
 exact (norm_add_le _ _).trans ((add_le_add regular reflected).trans_eq (by ring))

theorem centeredRaw_lipschitz (b:Hq) (x y:ℝ) :
 ‖centeredRaw b y-centeredRaw b x‖≤(2*Real.pi*q*Real.sqrt (2*q)*‖b‖)*‖y-x‖:=by
 simpa only [centeredRaw,sub_sub_sub_cancel_right] using symFourier_lipschitz b x y

end OriginalKElementaryArithmeticAction.FreeParameter.CountLipschitz
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
