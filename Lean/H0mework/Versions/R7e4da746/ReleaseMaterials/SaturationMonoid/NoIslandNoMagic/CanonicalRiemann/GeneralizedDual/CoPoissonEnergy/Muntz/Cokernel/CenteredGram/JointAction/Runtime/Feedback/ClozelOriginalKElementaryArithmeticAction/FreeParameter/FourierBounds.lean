import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.Riesz
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedBEulerJunctionSource.TwoPieceFourierAction

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.FreeParameter.FourierBounds
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalRieszSource
open OriginalKPairedBEulerJunctionSource.TwoPieceFourierAction
open scoped Topology InnerProductSpace
open private state_fourierDerivative_integral from
 H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedBEulerJunctionSource.TwoPieceFourierAction
local notation "q" => (1/4 : ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "μq" => volume.restrict (symmetricInterval q)
local instance quarterFinite : IsFiniteMeasure μq where
 measure_univ_lt_top := lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top q)

theorem actual_fourier_value_bound (state : Hq) (x : ℝ) :
    ‖Constructor.fourierRaw state x‖ ≤ Real.sqrt (2*q)*‖state‖ :=
  burnolRadiusTruncatedFourierRaw_norm_le (by norm_num) state x

theorem actual_fourier_slope_bound (state : Hq) (x : ℝ) :
    ‖Constructor.fourierDerivative state x‖ ≤
      (2*Real.pi*q*Real.sqrt (2*q))*‖state‖ := by
  rw [state_fourierDerivative_integral,
    intervalIntegral.integral_of_le (by norm_num : -q≤q),←integral_Icc_eq_integral_Ioc]
  have base : Integrable state μq := (Lp.memLp state).integrable (by norm_num)
  calc
    _ ≤ ∫ y : ℝ, (2*Real.pi*q)*‖state y‖ ∂μq := by
      apply norm_integral_le_of_norm_le (base.norm.const_mul _)
      filter_upwards [ae_restrict_mem (measurableSet_symmetricInterval q)] with y inside
      simp only [norm_mul,Constructor.phase,Circle.norm_coe,one_mul,norm_neg,
        norm_ofNat,Complex.norm_real,Real.norm_eq_abs,norm_I,mul_one,
        abs_of_pos Real.pi_pos]
      gcongr
      exact abs_le.mpr inside
    _ = (2*Real.pi*q)*(∫ y : ℝ, ‖state y‖ ∂μq) := integral_const_mul _ _
    _ ≤ (2*Real.pi*q)*(Real.sqrt (2*q)*‖state‖) := by
      gcongr
      exact burnolRadiusInterval_integral_norm_le (by norm_num) state
    _ = _ := by ring

theorem actual_fourier_lipschitz (state : Hq) (x y : ℝ) :
    ‖Constructor.fourierRaw state y-Constructor.fourierRaw state x‖ ≤
      ((2*Real.pi*q*Real.sqrt (2*q))*‖state‖)*‖y-x‖ := by
  exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (state_fourier_hasDerivAt state t).hasDerivWithinAt)
    (fun t _ => actual_fourier_slope_bound state t) convex_univ (mem_univ x) (mem_univ y)

def fourierRead (x : ℝ) : Hq →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun state=>Constructor.fourierRaw state x
      map_add' := by
        intro a b
        exact congrFun (burnolRadiusTruncatedFourierRaw_add a b) x
      map_smul' := by
        intro a b
        exact congrFun (burnolRadiusTruncatedFourierRaw_smul a b) x }
    (Real.sqrt (2*q)) (fun state=>actual_fourier_value_bound state x)

end OriginalKElementaryArithmeticAction.FreeParameter.FourierBounds
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
